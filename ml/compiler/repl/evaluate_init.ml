(* ======================================================== *)
(*  evaluate_init: ported from HOL4's
    compiler/repl/evaluate_initScript.sml
    A definition theory, with 5 definitions and 34 theorems.  Needed
    by repl_types.ml.  *)
(* ======================================================== *)

(*
  Lemma used in repl_typesTheory: that evaluate_skip's invariant
  holds at initialisation.
*)

needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/repl/evaluate_skip.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "evaluate_init"
  ["evaluate"; "evaluateProps"; "evaluate_skip"; "ml_prog"; "namespaceProps";
   "semanticPrimitives"];;


(* TODO: move *)

let FUN_FMAP_SUBMAP_SUBSET = prove
 (`FINITE d1 /\ FINITE d2 ==>
   (FUN_FMAP f d1 SUBMAP FUN_FMAP f d2 <=> d1 SUBSET d2)`,
  CHEAT_TAC);;

(* NOT_NIL_CONS *)
let evaluate_init_NOT_NIL_CONS = prove
 (`~(xs = []) <=> (?y ys. xs = CONS y ys)`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 *
 * ------------------------------------------------------------------------- *)

let evaluate_init_state_ok_def = new_definition
  `evaluate_init_state_ok (s:'ffi semanticPrimitives_state) <=>
     evaluate_skip_state_rel (LENGTH (semanticPrimitives_state_refs s))
       (FUN_FMAP I (count (LENGTH (semanticPrimitives_state_refs s))))
                              (FUN_FMAP I (count
                                (semanticPrimitives_state_next_type_stamp s)))
                              (FUN_FMAP I (count
                                (semanticPrimitives_state_next_exn_stamp
                                s))) s s`;;

let env_ok_def = new_definition
  `evaluate_init_env_ok (s:'ffi semanticPrimitives_state) env <=>
     evaluate_skip_env_rel (FUN_FMAP I (count (LENGTH
       (semanticPrimitives_state_refs s))))
             (FUN_FMAP I (count (semanticPrimitives_state_next_type_stamp
               s)))
             (FUN_FMAP I (count (semanticPrimitives_state_next_exn_stamp
               s)))
             env env`;;

let v_ok_def = new_definition
  `evaluate_init_v_ok (s:'ffi semanticPrimitives_state) v <=>
     evaluate_skip_v_rel (FUN_FMAP I (count (LENGTH
       (semanticPrimitives_state_refs s))))
           (FUN_FMAP I (count (semanticPrimitives_state_next_type_stamp s)))
           (FUN_FMAP I (count (semanticPrimitives_state_next_exn_stamp s)))
           v v`;;

let evaluate_init_ref_ok_def = new_definition
  `evaluate_init_ref_ok (s:'ffi semanticPrimitives_state) v <=>
     evaluate_skip_ref_rel (evaluate_skip_v_rel (FUN_FMAP I (count (LENGTH
       (semanticPrimitives_state_refs s))))
                    (FUN_FMAP I (count
                      (semanticPrimitives_state_next_type_stamp s)))
                    (FUN_FMAP I (count
                      (semanticPrimitives_state_next_exn_stamp s))))
                    v v`;;

let ref_ok_thm = prove
 (`evaluate_init_ref_ok s (semanticPrimitives_Refv v) = evaluate_init_v_ok s v
  /\
   evaluate_init_ref_ok s (semanticPrimitives_Varray vs) = ALL
     (evaluate_init_v_ok s) vs /\
   evaluate_init_ref_ok s (semanticPrimitives_W8array a) = T /\
   evaluate_init_ref_ok s (semanticPrimitives_Thunk _ v) =
     evaluate_init_v_ok s v`,
  CHEAT_TAC);;

let stamp_ok_def = new_definition
  `stamp_ok (s:'ffi semanticPrimitives_state) st <=>
     stamp_rel (FUN_FMAP I (count (semanticPrimitives_state_next_type_stamp
       s)))
               (FUN_FMAP I (count
                 (semanticPrimitives_state_next_exn_stamp s))) st st`;;

let evaluate_v_ok_mono = prove
 (`evaluate s env xs = (t,res) /\
   evaluate_init_v_ok s v ==>
     evaluate_init_v_ok t v`,
  CHEAT_TAC);;

let evaluate_env_ok_mono = prove
 (`evaluate s env xs = (t,res) /\
   evaluate_init_env_ok s env ==>
     evaluate_init_env_ok t env`,
  CHEAT_TAC);;

let v_ok_thm = prove
 (`(!opt vs. evaluate_init_v_ok s (semanticPrimitives_Conv opt vs) <=>
      ALL (evaluate_init_v_ok s) vs /\
      (!st. opt = SOME st ==> stamp_ok s st)) /\
   (!env n x. evaluate_init_v_ok s (semanticPrimitives_Closure env n x) <=>
     evaluate_init_env_ok s env) /\
   (!env f n. evaluate_init_v_ok s (semanticPrimitives_Recclosure env f n)
     <=> evaluate_init_env_ok s env) /\
   (!vs. evaluate_init_v_ok s (semanticPrimitives_Vectorv vs) <=> ALL
     (evaluate_init_v_ok s) vs) /\
   (!lit. evaluate_init_v_ok s (semanticPrimitives_Litv lit)) /\
   (!loc b. evaluate_init_v_ok s (semanticPrimitives_Loc b loc) <=> loc <
     LENGTH (semanticPrimitives_state_refs s)) /\
   (!env ns. evaluate_init_v_ok s (semanticPrimitives_Env env ns) <=>
     evaluate_init_env_ok s env)`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:125-162: ML code, not ported *)

(* HOL4 evaluate_initScript.sml:164-198: a theorem whose statement the port
   cannot state yet: evaluate_ok *)

(* HOL4 evaluate_initScript.sml:200-202: a proof *)

(* HOL4 evaluate_initScript.sml:204-209: a proof *)

(* HOL4 evaluate_initScript.sml:211-214: a proof *)

(* HOL4 evaluate_initScript.sml:216-220: a proof *)

(* HOL4 evaluate_initScript.sml:222-225: a proof *)

(* HOL4 evaluate_initScript.sml:227-238: a proof *)

(* HOL4 evaluate_initScript.sml:240-245: a proof *)

(* HOL4 evaluate_initScript.sml:247-250: a proof *)

let state_ok_eval_state = prove
 (`evaluate_init_state_ok s ==> semanticPrimitives_state_eval_state s = NONE`,
  CHEAT_TAC);;

let do_eval_state_none = prove
 (`semanticPrimitives_state_eval_state
     s = NONE ==>
       do_eval_res vs s =
         (s,(Rerr (Rabort Rtype_error):(semanticPrimitives_v sem_env#dec
           list,semanticPrimitives_v)semanticPrimitives_result))`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:266-273: a proof *)

(* HOL4 evaluate_initScript.sml:275-289: a proof *)

(* v_ok_v_to_list *)
let evaluate_init_v_ok_v_to_list = prove
 (`!v vs.
     evaluate_init_v_ok s v /\
     evaluate_init_state_ok s /\
     semanticPrimitives_v_to_list v = SOME vs ==>
       ALL (evaluate_init_v_ok s) vs`,
  CHEAT_TAC);;

let v_ok_list_to_v = prove
 (`!v vs.
     ALL (evaluate_init_v_ok s) vs /\
     evaluate_init_state_ok s ==>
       evaluate_init_v_ok s (semanticPrimitives_list_to_v vs)`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:314: a theorem that HOL4 states as the value
   of an ML expression: do_app_cases *)

let state_ok_refs_ok = prove
 (`evaluate_init_state_ok s ==> ALL (evaluate_init_ref_ok s)
  (semanticPrimitives_state_refs s)`,
  CHEAT_TAC);;
add_simp state_ok_refs_ok;;

let with_same_refs_and_ffi = prove
 (`semanticPrimitives_state_ffi_fupd (K (semanticPrimitives_state_ffi s))
  (semanticPrimitives_state_refs_fupd (K (semanticPrimitives_state_refs s))
     s) = s`,
  CHEAT_TAC);;

let v_ok_sub_exn = prove
 (`evaluate_init_state_ok s ==> evaluate_init_v_ok s sub_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_sub_exn;;

let v_ok_chr_exn = prove
 (`evaluate_init_state_ok s ==> evaluate_init_v_ok s
  semanticPrimitives_chr_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_chr_exn;;

let v_ok_div_exn = prove
 (`evaluate_init_state_ok s ==> evaluate_init_v_ok s
  semanticPrimitives_div_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_div_exn;;

let v_ok_Boolv = prove
 (`evaluate_init_state_ok s ==> evaluate_init_v_ok s
  (semanticPrimitives_Boolv b)`,
  CHEAT_TAC);;
add_simp v_ok_Boolv;;

(* do_app_ok *)
let evaluate_init_do_app_ok = prove
 (`semanticPrimitives_do_app (semanticPrimitives_state_refs
  s,semanticPrimitives_state_ffi s) op vs = SOME ((refs,ffi),res) /\
   evaluate_init_state_ok s /\
   ALL (evaluate_init_v_ok s) vs /\ ~(op = ast_Opapp) /\ ~(op = ast_Eval)
     ==>
     (let t = (semanticPrimitives_state_ffi_fupd (K ffi)
       (semanticPrimitives_state_refs_fupd (K refs) s)) in
     evaluate_init_state_ok t /\
     ALL (evaluate_init_ref_ok t) refs /\
     (!v. res = Rval v ==> evaluate_init_v_ok t v) /\
     (!v. res = Rerr (Rraise v) ==> evaluate_init_v_ok t v))`,
  CHEAT_TAC);;

(* [allow_rebind] *)
let evaluate_init_do_app_ok = SIMP_RULE [LET_DEF] evaluate_init_do_app_ok;;

let dest_thunk_ok = prove
 (`evaluate_init_state_ok s /\
   semanticPrimitives_dest_thunk vs (semanticPrimitives_state_refs s) =
     semanticPrimitives_IsThunk m v /\
   semanticPrimitives_do_opapp [v; semanticPrimitives_Conv NONE []] = SOME
     (env,e) ==>
     evaluate_init_state_ok (evaluate_dec_clock s) /\ evaluate_init_env_ok
       (evaluate_dec_clock s) env`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:702-766: a proof *)

(* HOL4 evaluate_initScript.sml:768: a theorem that HOL4 states as the value
   of an ML expression: do_opapp_cases *)

(* do_opapp_update *)
let evaluate_init_do_opapp_update = prove
 (`semanticPrimitives_do_opapp vs = SOME (env,x) /\
   ALL (evaluate_init_v_ok s) vs /\
   evaluate_init_state_ok s ==>
     evaluate_init_env_ok s env`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:788-825: a proof *)

let v_ok_do_log = prove
 (`evaluate_init_state_ok s /\
   evaluate_init_v_ok s v /\
   do_log lop v x = SOME (semanticPrimitives_Val w) ==> evaluate_init_v_ok
     s w`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:836-841: a proof *)

(* HOL4 evaluate_initScript.sml:843-846: a proof *)

let v_ok_bind_exn = prove
 (`evaluate_init_state_ok s ==> evaluate_init_v_ok s
  semanticPrimitives_bind_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_bind_exn;;

(* HOL4 evaluate_initScript.sml:855-869: a proof *)

(* HOL4 evaluate_initScript.sml:871-889: a proof *)

(* HOL4 evaluate_initScript.sml:891-909: a proof *)

(* HOL4 evaluate_initScript.sml:911-913: a proof *)

(* HOL4 evaluate_initScript.sml:915-917: a proof *)

(* HOL4 evaluate_initScript.sml:919-921: a proof *)

let pmatch_ok = prove
 (`semanticPrimitives_pmatch (sem_env_c env) (semanticPrimitives_state_refs s)
  p v ws = Match env1 /\
   evaluate_init_state_ok s /\
   evaluate_init_env_ok s env /\
   evaluate_init_v_ok s v /\
   ALL (evaluate_init_v_ok s) (MAP SND ws) ==>
     ALL (evaluate_init_v_ok s) (MAP SND env1)`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:940-959: a proof *)

(* HOL4 evaluate_initScript.sml:961-964: a proof *)

(* env_ok_extend_dec_env *)
let evaluate_init_env_ok_extend_dec_env = prove
 (`evaluate_init_env_ok s env /\
   evaluate_init_state_ok s /\
   evaluate_init_env_ok s env1 ==>
     evaluate_init_env_ok s (extend_dec_env env1 env)`,
  CHEAT_TAC);;

let env_ok_nsAppend = prove
 (`evaluate_init_env_ok s env /\
   evaluate_init_state_ok s /\
   evaluate_init_env_ok s env1 ==>
     evaluate_init_env_ok s (mk_sem_env (nsAppend (sem_env_v env1)
       (sem_env_v env)) (nsAppend (sem_env_c env1) (sem_env_c env)))`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:986-1019: a proof *)

(* HOL4 evaluate_initScript.sml:1021-1029: a proof *)

(* HOL4 evaluate_initScript.sml:1031-1039: a proof *)

let state_ok_with_next_type_stamp = prove
 (`evaluate_init_state_ok s /\
   evaluate_init_env_ok s env ==>
     (let s' = semanticPrimitives_state_next_type_stamp_fupd (K (extra +
       semanticPrimitives_state_next_type_stamp s)) s in
     evaluate_init_state_ok s' /\
     evaluate_init_env_ok s' env)`,
  CHEAT_TAC);;

let state_ok_with_next_exn_stamp = prove
 (`evaluate_init_state_ok s /\
   evaluate_init_env_ok s env ==>
     (let s' = semanticPrimitives_state_next_exn_stamp_fupd (K (extra +
       semanticPrimitives_state_next_exn_stamp s)) s in
     evaluate_init_state_ok s' /\
     evaluate_init_env_ok s' env)`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:1097-1122: a proof *)

(* HOL4 evaluate_initScript.sml:1124-1127: a proof *)

(* [local] *)
let state_ok_declare_env = prove
 (`evaluate_init_state_ok s ==>
     (!env. declare_env (semanticPrimitives_state_eval_state s) env =
       NONE)`,
  CHEAT_TAC);;

(* HOL4 evaluate_initScript.sml:1136-1139: a proof *)

(* HOL4 evaluate_initScript.sml:1141-1148: a proof *)

(* HOL4 evaluate_initScript.sml:1150-1154: a proof *)

(* HOL4 evaluate_initScript.sml:1156-1178: a proof *)

(* HOL4 evaluate_initScript.sml:1180: a proof *)

(* -------------------------------------------------------------------------
 *  top-level results
 * ------------------------------------------------------------------------- *)

let state_ok_init = prove
 (`evaluate_init_state_ok (semanticPrimitives_state_clock_fupd (K ck)
  (ml_prog_init_state ffi))`,
  CHEAT_TAC);;

let env_ok_init = prove
 (`evaluate_init_env_ok (semanticPrimitives_state_clock_fupd (K ck)
  (ml_prog_init_state ffi)) init_env`,
  CHEAT_TAC);;

let evaluate_decs_init = prove
 (`evaluate_evaluate_decs (semanticPrimitives_state_clock_fupd (K ck)
  (ml_prog_init_state ffi)) init_env decs = (s,Rval env) ==>
   (?fr ft fe.
      fr = FUN_FMAP I (count (LENGTH (semanticPrimitives_state_refs s))) /\
      ft = FUN_FMAP I (count (semanticPrimitives_state_next_type_stamp s))
        /\
      fe = FUN_FMAP I (count (semanticPrimitives_state_next_exn_stamp s)) /\
      evaluate_skip_state_rel (LENGTH (semanticPrimitives_state_refs s)) fr
        ft fe s s /\
      evaluate_skip_env_rel fr ft fe (extend_dec_env env init_env)
                       (extend_dec_env env init_env))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
