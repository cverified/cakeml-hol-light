(* ======================================================== *)
(*  cfDiv: ported from HOL4's
    characteristic/cfDivScript.sml
    A definition theory, with 24 definitions and 91 theorems.
    Needed by RuntimeProg.ml.  *)
(* ======================================================== *)

(*
  Defines the repeat function and the corresponding lemma used to prove
  non-termination of programs in cf.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cf.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeaps.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfNormalise.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/balanced_map.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/set_sep.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;
needs "translator/std_prelude.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cfDiv"
  ["cf"; "cfApp"; "cfHeaps"; "cfHeapsBase"; "cfNormalise"; "cfStore";
   "cfTactics"; "evaluate"; "ml_translator"; "semanticPrimitives";
   "std_prelude"];;

let _ = do_list hide_constant ["arg1"; "arg2"; "exps"; "fv"];;

(* HOL4 cfDivScript.sml:17: ML code, not ported *)

(* Make sure we are using the option monad even in the presence of other
   monads *)

(* -- general set up -- *)

(* HOL4 cfDivScript.sml:26: the ML values that the definitions below
   antiquote *)

let POSTd_eq = prove
 (`POSTd Q r h <=> (?io1. r = cfHeapsBase_Div io1 /\ Q io1 /\ emp h)`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:35-37: ML code, not ported *)

make_size "ast_exp";;
let dest_opapp_exp_size = prove
 (`!tm f arg.
    dest_opapp tm = SOME (f,arg) ==> list_size ast_exp_size arg <
      ast_exp_size tm`,
  CHEAT_TAC);;

let dest_opapp_eq_nil_IMP = prove
 (`dest_opapp (exp) = SOME (f,[]) ==> F`,
  CHEAT_TAC);;

let dest_opapp_eq_single_IMP = prove
 (`dest_opapp (ast_App op exps) = SOME (f,[arg]) ==> op = ast_Opapp /\ exps =
  [f; arg]`,
  CHEAT_TAC);;

let nsLookup_build_rec_env_fresh = prove
 (`!funs env env' fname.
     ALL (\x. ~(fname = x)) (MAP FST funs) ==>
     nsLookup (semanticPrimitives_build_rec_env funs env' (sem_env_v env))
       (Short fname) =
     nsLookup (sem_env_v env) (Short fname)`,
  CHEAT_TAC);;

let nsLookup_alist_to_ns_fresh = prove
 (`!l fname.
     ALL (\x. ~(fname = x)) (MAP FST l) ==>
     nsLookup (alist_to_ns l) (Short fname) = NONE`,
  CHEAT_TAC);;


(* -- tailrec -- *)

(* HOL4 cfDivScript.sml:106-111: ML code, not ported *)

(* HOL4 cfDivScript.sml:113: ML code, not ported *)

let mk_inl_def = new_definition
  `mk_inl e =
   ast_Let (SOME (implode "x")) e (ast_Con (SOME (Short (implode "Inl")))
     [ast_Var (Short (implode "x"))])`;;

let mk_inr_def = new_definition
  `mk_inr e =
   ast_Let (SOME (implode "x")) e (ast_Con (SOME (Short (implode "Inr")))
     [ast_Var (Short (implode "x"))])`;;

(* the clauses in three quotations: es is (exp list) and (_)list; l is lit
   and locs; pes is ((pat # exp) list), (_)list and (_#_)list; recfuns is
   ((varN # varN # exp) list), (_#_)list, (_)list and (_#_#_)list; v is 'n
   and ((modN , varN) id), which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     inv_image (<) (\x. match x with INL (t,x,e) -> ast_exp_size e
           | INR (INL (t,x,es)) -> list_size ast_exp_size es
           | INR (INR (INL (t,x,pes))) ->
               list_size (pair_size ast_pat_size ast_exp_size) pes
           | INR (INR (INR (t,x,funs))) ->
               list_size (pair_size mlstring_size
                          (pair_size mlstring_size ast_exp_size)) funs)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 cfDivScript.sml:303-314: the tactic that proves the termination *)
let mk_single_app_def,mk_single_app_ind = define_guess_clauses
  [`(mk_single_app fname allow_fname (ast_Raise e) =
        OPTION_BIND (mk_single_app fname F e) (\e.
          SOME ((ast_Raise e:ast_exp)))) /\
    (mk_single_app fname allow_fname (ast_Handle e pes) =
        OPTION_BIND (mk_single_app fname F e) (\e. OPTION_BIND
            (mk_single_appps fname allow_fname pes) (\pes.
          if allow_fname then
            SOME (ast_Handle (mk_inr e) pes)
          else SOME ((ast_Handle e pes:ast_exp))))) /\
    (mk_single_app fname allow_fname (ast_Lit l) =
        if allow_fname then
          SOME (mk_inr (ast_Lit l))
        else SOME (ast_Lit l)) /\
    (mk_single_app fname allow_fname (ast_Var (Short v)) =
        if SOME v = fname then
          NONE
        else if allow_fname then
          SOME (mk_inr (ast_Var (Short v)))
        else SOME (ast_Var (Short v))) /\
    (mk_single_app fname allow_fname (ast_Fun x e) =
        let fname' = (if SOME x = fname then
                       NONE
                     else fname) in
        OPTION_BIND (mk_single_app fname' F e) (\e.
          if allow_fname then
            SOME (mk_inr (ast_Fun x e))
          else SOME (ast_Fun x e))) /\
    (mk_single_app fname allow_fname (ast_Log lop e1 e2) =
        OPTION_BIND (mk_single_app fname F e1) (\e1. OPTION_BIND
            (mk_single_app fname F e2) (\e2.
          if allow_fname then
            SOME (mk_inr (ast_Log lop e1 e2))
          else SOME (ast_Log lop e1 e2)))) /\
    (mk_single_app fname allow_fname (ast_If e1 e2 e3) =
        OPTION_BIND (mk_single_app fname F e1) (\e1. OPTION_BIND
            (mk_single_app fname allow_fname e2) (\e2. OPTION_BIND
            (mk_single_app fname allow_fname e3) (\e3.
          SOME ((ast_If e1 e2 e3:ast_exp)))))) /\
    (mk_single_app fname allow_fname (ast_Mat e pes) =
        OPTION_BIND (mk_single_app fname F e) (\e. OPTION_BIND
            (mk_single_appps fname allow_fname pes) (\pes.
          SOME ((ast_Mat e pes:ast_exp))))) /\
    (mk_single_app fname allow_fname (ast_Tannot e ty) =
        OPTION_BIND (mk_single_app fname allow_fname e) (\e.
          SOME (ast_Tannot e ty))) /\
    (mk_single_app fname allow_fname (ast_Let NONE e1 e2) =
        OPTION_BIND (mk_single_app fname F e1) (\e1. OPTION_BIND
            (mk_single_app fname allow_fname e2) (\e2.
          SOME ((ast_Let NONE e1 e2:ast_exp))))) /\
    (mk_single_app fname allow_fname (ast_Let (SOME x) e1 e2) =
        let fname' =
            (if SOME x = fname then
              NONE
            else fname) in
        OPTION_BIND (mk_single_app fname F e1) (\e1. OPTION_BIND
            (mk_single_app fname' allow_fname e2) (\e2.
          SOME ((ast_Let (SOME x) e1 e2:ast_exp))))) /\
    (mk_single_apps fname allow_fname [] =
        SOME []) /\
    (mk_single_appps fname allow_fname (CONS (p,e) pes) =
        let fname' = (if EX ((=) fname o SOME) (ast_pat_bindings p) then
            NONE
                     else fname) in
        OPTION_BIND (mk_single_app fname' allow_fname e) (\e. OPTION_BIND
            (mk_single_appps fname allow_fname pes) (\pes.
          SOME (CONS (p,e) pes)))) /\
    (mk_single_appps fname allow_fname [] =
        SOME []) /\
    (mk_single_appr fname allow_fname [] =
        SOME [])`;
   `(mk_single_app fname allow_fname (ast_Con c es) =
        OPTION_BIND (mk_single_apps fname F es) (\es.
          if allow_fname then
            SOME (mk_inr (ast_Con c es))
          else SOME (ast_Con c es))) /\
    (mk_single_app fname allow_fname (ast_Var v) =
        if allow_fname then
          SOME (mk_inr (ast_Var v))
        else SOME (ast_Var v)) /\
    (mk_single_app fname allow_fname (ast_Lannot e l) =
        OPTION_BIND (mk_single_app fname allow_fname e) (\e.
          SOME (ast_Lannot e l))) /\
    (mk_single_app fname allow_fname (ast_App op es) =
          (match dest_opapp (ast_App op es) with
             SOME (ast_Var (Short f),[arg]) ->
               (if SOME f = fname then
                 if allow_fname then
                   OPTION_BIND (mk_single_app fname F arg) (\arg.
                     SOME (mk_inl arg))
                 else NONE
               else OPTION_BIND (mk_single_app fname F arg) (\arg.
                   if allow_fname then
                     SOME (mk_inr (ast_App op [ast_Var (Short f); arg]))
                   else SOME (ast_App op [ast_Var (Short f); arg])))
           | _ ->
             OPTION_BIND (mk_single_apps fname F es) (\es.
               if allow_fname then
                 SOME (mk_inr (ast_App op es))
               else SOME (ast_App op es)))) /\
    (mk_single_apps fname allow_fname (CONS e es) =
        OPTION_BIND (mk_single_app fname allow_fname e) (\e. OPTION_BIND
            (mk_single_apps fname allow_fname es) (\es.
          SOME (CONS e es))))`;
   `(mk_single_app fname allow_fname (ast_Letrec recfuns e) =
        let fname' = (if EX ((=) fname o SOME) (MAP FST recfuns) then NONE
            else fname) in
        OPTION_BIND (mk_single_appr fname' F recfuns) (\recfuns.
            OPTION_BIND (mk_single_app fname' allow_fname e) (\e.
          SOME ((ast_Letrec recfuns e:ast_exp))))) /\
    (mk_single_appr fname allow_fname (CONS (f,x,e) recfuns) =
        let fname' = (if SOME x = fname then NONE else fname) in
        OPTION_BIND (mk_single_app fname allow_fname e) (\e. OPTION_BIND
            (mk_single_appr fname allow_fname recfuns) (\recfun.
          SOME (CONS (f,x,e) recfuns))))`];;

(* HOL4 cfDivScript.sml:316: ML code, not ported *)

let mk_stepfun_closure_def = new_definition
  `mk_stepfun_closure env fname farg fbody =
     match  with
        ->
       OPTION_BIND (mk_single_app (SOME fname) T fbody) (\gbody.
        SOME (let benv = semanticPrimitives_build_rec_env
          [(fname,farg,fbody)] env (sem_env_v env) in
          semanticPrimitives_Closure (sem_env_v_fupd (K benv) env) farg gbody))
     |  -> NONE`;;

let mk_tailrec_closure_def = new_definition
  `mk_tailrec_closure x1 =
     match x1 with
       semanticPrimitives_Recclosure env [(fname,farg,fbody)] name2 ->
       OPTION_BIND (mk_stepfun_closure env fname farg fbody) (\gclosure.
        SOME (semanticPrimitives_Closure (sem_env_v_fupd (K
               (nsBind fname gclosure (sem_env_v env))) env) farg
             (ast_App ast_Opapp
                  [ast_App ast_Opapp
                     [ast_Letrec tailrec_clos (ast_Var (Short (implode
                       "tailrec")));
                      ast_Var (Short fname)];
                   ast_Var (Short farg)])))
     | _ -> NONE`;;

(* [local] *)
let mk_single_app_F_unchanged_gen = prove
 (`(!fname allow_fname e e'.
                mk_single_app fname allow_fname e = SOME e' /\ allow_fname =
                  F ==> e = e') /\
    (!fname allow_fname es es'.
                mk_single_apps fname allow_fname es = SOME es'
                  /\ allow_fname = F ==> es = es') /\
    (!fname allow_fname pes pes'.
                 mk_single_appps fname allow_fname pes = SOME pes'
                   /\ allow_fname = F ==> pes = pes') /\
    (!fname allow_fname recfuns recfuns'.
                 mk_single_appr fname allow_fname recfuns = SOME recfuns'
                   /\ allow_fname = F ==> recfuns = recfuns')`,
  CHEAT_TAC);;

let mk_single_app_F_unchanged = SIMP_RULE [] mk_single_app_F_unchanged_gen;;

let mk_inr_res_def = new_definition
  `mk_inr_res res =
     match res with
       Rval vs ->
      Rval (MAP (\v. semanticPrimitives_Conv (SOME (TypeStamp (implode
        "Inr") 4)) [v]) vs)
     | res -> res`;;

let mk_inl_res_def = new_definition
  `mk_inl_res res =
     match res with
       Rval vs ->
      Rval (MAP (\v. semanticPrimitives_Conv (SOME (TypeStamp (implode
        "Inl") 4)) [v]) vs)
     | res -> res`;;

let dest_inr_v_def = new_definition
  `dest_inr_v x1' =
     match x1' with
       semanticPrimitives_Conv (SOME (TypeStamp txt n)) [v] ->
      if txt = (implode "Inr") /\ n = 4 then
        SOME v
      else NONE
     | _ -> NONE`;;

let dest_inl_v_def = new_definition
  `dest_inl_v x1'' =
     match x1'' with
       semanticPrimitives_Conv (SOME (TypeStamp txt n)) [v] ->
      if txt = (implode "Inl") /\ n = 4 then
        SOME v
      else NONE
     | _ -> NONE`;;

let dest_inr_v_IMP = prove
 (`!e1 v. dest_inr_v e1 = SOME v ==> e1 = semanticPrimitives_Conv (SOME
  (TypeStamp (implode "Inr") 4)) [v]`,
  CHEAT_TAC);;

let dest_inl_v_IMP = prove
 (`!e1 v. dest_inl_v e1 = SOME v ==> e1 = semanticPrimitives_Conv (SOME
  (TypeStamp (implode "Inl") 4)) [v]`,
  CHEAT_TAC);;

let evaluate_inl = prove
 (`do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 = T /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
          SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl") 4))
            [v])) ==> evaluate st env [mk_inl e] =
       (match evaluate st env [e] with
           (st,Rval v) -> (st,mk_inl_res (Rval v))
         | (st,rerr) -> (st,rerr))`,
  CHEAT_TAC);;

(* [local] *)
let build_conv_check_IMP_nsLookup = prove
 (`!env const v consname stamp n.
   (!v. build_conv env (SOME const) [v] =
    SOME (semanticPrimitives_Conv (SOME stamp) [v])) /\
   do_con_check env (SOME const) n ==> nsLookup env const = SOME (n,stamp)`,
  CHEAT_TAC);;

let evaluate_IMP_inl = prove
 (`do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 = T /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
          SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl") 4))
            [v])) /\
   evaluate st env [e] = (st',res) ==> evaluate st env [mk_inl e] =
     (st',mk_inl_res res)`,
  CHEAT_TAC);;

let evaluate_inr = prove
 (`do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 = T /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
          SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr") 4))
            [v])) ==> evaluate st env [mk_inr e] =
       (match evaluate st env [e] with
           (st,Rval v) -> (st,mk_inr_res (Rval v))
         | (st,rerr) -> (st,rerr))`,
  CHEAT_TAC);;

let evaluate_IMP_inr = prove
 (`do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 = T /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
          SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr") 4))
            [v])) /\
   evaluate (st:'ffi semanticPrimitives_state) env [e] = (st',res) ==>
     evaluate st env [mk_inr e] = (st',mk_inr_res res)`,
  CHEAT_TAC);;

let mk_single_appps_MAP_FST = prove
 (`!pes x b pes'.
     mk_single_appps x b pes = SOME pes' ==>
     MAP FST pes = MAP FST pes'`,
  CHEAT_TAC);;

(* [local] *)
let mk_single_app_NONE_evaluate = prove
 (`(!(st:'ffi semanticPrimitives_state) env es es'.
     mk_single_apps NONE T es = SOME es' /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 = T
       /\ (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
              4)) [v])) ==>
         evaluate st env es' = (match evaluate st env es with
            (st',res) -> (st',mk_inr_res res))) /\
    (!(st:'ffi semanticPrimitives_state) env v pes err_v pes'.
     mk_single_appps NONE T pes = SOME pes' /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 = T
       /\ (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
              4)) [v])) ==>
         evaluate_evaluate_match st env v pes' err_v = (match
           evaluate_evaluate_match st env v pes err_v with
            (st',res) -> (st',mk_inr_res res)))`,
  CHEAT_TAC);;

(* [local] *)
let mk_single_app_NONE_evaluate_single = prove
 (`(!(st:'ffi semanticPrimitives_state) env e e'.
     mk_single_app NONE T e = SOME e' /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 /\ (!v.
       build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
              4)) [v])) ==>
         evaluate st env [e'] = (match evaluate st env [e] with
            (st',res) -> (st',mk_inr_res res)))`,
  CHEAT_TAC);;

let partially_evaluates_to_def,partially_evaluates_to_ind = define_guess
  `(partially_evaluates_to fv' env st [] = T) /\
   (partially_evaluates_to fv' env st (CONS (e1,e2) r) =
      match evaluate st env [e1] with
        (st',Rval v1) ->
          (?v. dest_inr_v (HD v1) = SOME v /\ evaluate st env [e2] =
              (st',Rval [v]) /\
               partially_evaluates_to fv' env st' r) \/
          (?v st'' res. dest_inl_v (HD v1) = SOME v /\ evaluate st env [e2]
              = (st'',res) /\
              (match semanticPrimitives_do_opapp [fv'; v] with
                SOME (env',e3) ->
                   if semanticPrimitives_state_clock st' = 0 then st'' =
                       st' /\ res = Rerr (Rabort (Rtimeout_error))
                   else evaluate (evaluate_dec_clock st') env' [e3] =
                       (st'',res) /\
                     (match res with Rval _ ->
                        partially_evaluates_to fv' env st'' r
                      | _ -> T)
              | NONE -> res = Rerr (Rabort Rtype_error)))
       | (st',rerr) -> evaluate st env [e2] = (st',rerr))`;;

let partially_evaluates_to_match_def = new_definition
  `partially_evaluates_to_match fv' mv err_v env st (pr1,pr2) =
     match evaluate_evaluate_match st env mv pr1 err_v with
       (st',Rval v1) ->
         (?v. dest_inr_v (HD v1) = SOME v /\ evaluate_evaluate_match st env
           mv pr2 err_v = (st',Rval [v])) \/
         (?v st'' res. dest_inl_v (HD v1) = SOME v
           /\ evaluate_evaluate_match st env mv pr2 err_v = (st'',res) /\
             (match semanticPrimitives_do_opapp [fv'; v] with
                 SOME (env',e3) ->
                   if semanticPrimitives_state_clock st' = 0 then (st'' =
                     st' /\ res = Rerr (Rabort (Rtimeout_error)))
                   else evaluate (evaluate_dec_clock st') env' [e3] =
                     (st'',res)
               | NONE -> res = Rerr (Rabort Rtype_error)))
      | (st',rerr) -> evaluate_evaluate_match st env mv pr2 err_v =
        (st',rerr)`;;

(* [local] *)
let mk_single_app_evaluate = prove
 (`(!(st:'ffi semanticPrimitives_state) env es es' fname fv'.
     mk_single_apps (SOME fname) T es = SOME es' /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 = T /\
     (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
              4)) [v])) /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 = T /\
     (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl")
              4)) [v])) /\ nsLookup (sem_env_v env) (Short fname) = SOME fv'
              ==> partially_evaluates_to fv' env st (ZIP es' es)) /\
    (!(st:'ffi semanticPrimitives_state) env v pes err_v pes' fname fv'.
     mk_single_appps (SOME fname) T pes = SOME pes' /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 = T /\
     (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
              4)) [v])) /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 = T /\
     (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl")
              4)) [v])) /\ nsLookup (sem_env_v env) (Short fname) = SOME fv'
              ==> partially_evaluates_to_match fv' v err_v env st (pes',pes))`,
  CHEAT_TAC);;

let mk_single_app_evaluate_single = prove
 (`!(st:'ffi semanticPrimitives_state) env e e' fname fv'.
     mk_single_app (SOME fname) T e = SOME e' /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 = T /\
     (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
              4)) [v])) /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 = T /\
     (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
            SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl")
              4)) [v])) /\ nsLookup (sem_env_v env) (Short fname) = SOME fv'
              ==> partially_evaluates_to fv' env st [(e',e)]`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:969-1123: a theorem whose statement the port cannot
   state yet: evaluate_tailrec_ind_lemma *)

(* HOL4 cfDivScript.sml:1125-1176: a theorem whose statement the port cannot
   state yet: evaluate_tailrec_lemma *)

(* [local] *)
let mk_single_app_unroll_lemma = prove
 (`!fname fbody gbody (st:'ffi semanticPrimitives_state) st' ck1 env farg ck2 x
  v.
     mk_single_app (SOME fname) T fbody = SOME gbody /\
     evaluate (semanticPrimitives_state_clock_fupd (K ck1) (st:'ffi
       semanticPrimitives_state))
                (sem_env_v_fupd (K
                   (nsBind farg x
                     (nsBind fname (semanticPrimitives_Recclosure env
                       [(fname,farg,fbody)] fname) (sem_env_v
                        env)))) env) [gbody] =
              (semanticPrimitives_state_clock_fupd (K 0) st',mk_inl_res
                (Rval [v])) /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 /\
     (!v.
       build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
      SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr") 4))
        [v])) /\
     do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 /\
     (!v.
       build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
      SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl") 4))
        [v])) /\ ~(fname = farg) ==>
     evaluate (semanticPrimitives_state_clock_fupd (K (ck1 + ck2 + 1))
       (st:'ffi semanticPrimitives_state))
              (sem_env_v_fupd (K
               (nsBind farg x
                      (nsBind fname (semanticPrimitives_Recclosure env
                        [(fname,farg,fbody)] fname) (sem_env_v env)))) env)
              [fbody] =
    evaluate (semanticPrimitives_state_clock_fupd (K ck2) st')
             (sem_env_v_fupd (K
              (nsBind farg v
                     (nsBind fname (semanticPrimitives_Recclosure env
                       [(fname,farg,fbody)] fname) (sem_env_v env)))) env)
             [fbody]`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:1226-1393: a theorem whose statement the port cannot
   state yet: evaluate_tailrec_diverge_lemma *)

(* HOL4 cfDivScript.sml:1395-1535: a theorem whose statement the port cannot
   state yet: evaluate_tailrec_div_ind_lemma *)

(* HOL4 cfDivScript.sml:1537-1644: a theorem whose statement the port cannot
   state yet: evaluate_tailrec_div_ind_lemma2 *)

(* [local] *)
let lprefix_mono_lprefix = prove
 (`!f i k.
   (!i. LPREFIX (f i) (f (i + 1))) ==> LPREFIX (f i) (f (i + (k:num)))`,
  CHEAT_TAC);;

(* [local] *)
let gify = prove
 (`!g n.
   (!i. g i < g (i + 1)) ==> (?k (i:num). g i = (n:num) + k)`,
  CHEAT_TAC);;

let lprefix_lub_unskip = prove
 (`(!i. LPREFIX (f i) (f (i + 1))) /\
   (!i. g i < g (i + 1)) /\
   lprefix_lub (IMAGE (\i. f i) (UNIV:num->bool)) l ==>
   lprefix_lub (IMAGE (\i. f (g i)) (UNIV:num->bool)) l`,
  CHEAT_TAC);;

let mk_tailrec_closure_sound_basic = prove
 (`!fv' env.
   mk_tailrec_closure (semanticPrimitives_Recclosure env
     [(fname,farg,fbody)] fname) = SOME fv' /\
   do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
           SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
             4)) [v])) /\
   do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
          SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl") 4))
            [v])) /\
   ~(fname = farg) /\ app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list) fv' x H Q ==> app_basic p
     (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname) x H Q`,
  CHEAT_TAC);;

let mk_tailrec_closure_sound = prove
 (`!fv' env.
   mk_tailrec_closure (semanticPrimitives_Recclosure env
     [(fname,farg,fbody)] fname) = SOME fv' /\
   do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
           SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr")
             4)) [v])) /\
   do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
          SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl") 4))
            [v])) /\
   ~(fname = farg) /\ app p fv' [x] H Q ==> app p
     (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname) [x] H Q`,
  CHEAT_TAC);;

let some_tailrec_clos_def = new_definition
  `some_tailrec_clos env = semanticPrimitives_Recclosure env tailrec_clos
  (implode "tailrec")`;;

let POSTv_eq = prove
 (`POSTv Q r h <=> (?v. r = cfHeapsBase_Val v /\ Q v h)`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:1834-1837: ML code, not ported *)

let get_index_def,get_index_ind = define_guess
  `get_index st states i = if i = (0:num) then (i,st) else (i,states
  (get_index st states (i - 1)))`;;

let FFI_full_IN_st2heap_IMP = prove
 (`cfHeapsBase_FFI_full io IN st2heap p s ==> ffi_state_io_events
  (semanticPrimitives_state_ffi s) = io`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:1853: ML code, not ported *)

let evaluate_ck_timeout_error_IMP = prove
 (`evaluate_ck ck st env exps = (st1,Rerr (Rabort Rtimeout_error)) /\
   ck0 <= ck ==>
   (?st2. evaluate_ck ck0 st env exps = (st2,Rerr (Rabort
     Rtimeout_error)))`,
  CHEAT_TAC);;

(* lprefix_mono_lprefix[local] *)
let cfDiv_lprefix_mono_lprefix = prove
 (`!f i k.
   (!i. LPREFIX (f i) (f (i + 1))) ==> LPREFIX (f i) (f (i + (k:num)))`,
  CHEAT_TAC);;

(* gify[local] *)
let cfDiv_gify = prove
 (`!g n.
   (!i. g i < g (i + 1)) ==> (?k (i:num). g i = (n:num) + k)`,
  CHEAT_TAC);;

let lprefix_lub_skip = prove
 (`(!i. LPREFIX (f i) (f (i + 1))) /\
   (!i. g i < g (i + 1)) /\
   lprefix_lub (IMAGE (\i. f (g i)) (UNIV:num->bool)) l ==>
   lprefix_lub (IMAGE (\i. f i) (UNIV:num->bool)) l`,
  CHEAT_TAC);;

let SUM_GENLIST_SUC = prove
 (`SUM (list_of_seq f (SUC n)) = f n + SUM (list_of_seq f n)`,
  CHEAT_TAC);;

let SUM_GENLIST_LESS_EQ = prove
 (`!n m f. n <= m ==> SUM (list_of_seq f n) <= SUM (list_of_seq f m)`,
  CHEAT_TAC);;

let tailrec_POSTd = prove
 (`!p env fv' xv H Q.
     nsLookup (sem_env_c env) (Short (implode "Inr")) = SOME (1,inr)
       /\ same_type inr inl /\
     nsLookup (sem_env_c env) (Short (implode "Inl")) = SOME (1,inl)
       /\ ~(inr = inl) /\
     (?Hs events vs io.
        vs 0 = xv /\ SEP_IMP H (Hs 0) /\
        (!i. ?P. Hs i = P * set_sep_one (cfHeapsBase_FFI_full (events i)))
          /\
        (!i.
           (app p fv' [vs i] (Hs i)
              (POSTv (\v'. &(v' = semanticPrimitives_Conv (SOME inl) [vs
                (SUC i)]) *
                         Hs (SUC i))))) /\
        lprefix_lub (IMAGE (sptree_fromList o events) UNIV) io /\
        Q io) ==>
     app p (some_tailrec_clos env) [fv'; xv] H (POSTd Q)`,
  CHEAT_TAC);;

let app_opapp_intro = prove
 (`!body f args env x arg1v fv' argsv arg1 arg2 arg1v' arg2v H P.
   (!(st:'ffi semanticPrimitives_state).
     evaluate st (sem_env_v_fupd (K (nsBind x arg1v (sem_env_v env))) env)
       [f] = (st,Rval [fv'])) /\
   (!(st:'ffi semanticPrimitives_state).
     evaluate st (sem_env_v_fupd (K (nsBind x arg1v (sem_env_v env))) env)
       [arg1] = (st,Rval [arg1v'])) /\
   (!(st:'ffi semanticPrimitives_state).
     evaluate st (sem_env_v_fupd (K (nsBind x arg1v (sem_env_v env))) env)
       [arg2] = (st,Rval [arg2v])) /\
   app p fv' [arg1v'; arg2v] H P ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (semanticPrimitives_Closure env x (ast_App ast_Opapp [ast_App
         ast_Opapp [f; arg1]; arg2])) [arg1v] H P`,
  CHEAT_TAC);;

let IMP_app_POSTd_old = prove
 (`mk_stepfun_closure env fname farg fbody = SOME stepv /\
   nsLookup (sem_env_c env) (Short (implode "Inr")) = SOME (1,TypeStamp
     (implode "Inr") 4) /\
   nsLookup (sem_env_c env) (Short (implode "Inl")) = SOME (1,TypeStamp
     (implode "Inl") 4) /\
   do_con_check (sem_env_c env) (SOME (Short (implode "Inr"))) 1 /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inr"))) [v] =
        SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inr") 4))
          [v])) /\
   do_con_check (sem_env_c env) (SOME (Short (implode "Inl"))) 1 /\
   (!v. build_conv (sem_env_c env) (SOME (Short (implode "Inl"))) [v] =
        SOME (semanticPrimitives_Conv (SOME (TypeStamp (implode "Inl") 4))
          [v])) /\ ~(fname = farg) /\
   (?Hs events vs io.
        vs 0 = xv /\ SEP_IMP H (Hs 0 * set_sep_one (cfHeapsBase_FFI_full
          (events 0))) /\
        (!i.
             app p stepv [vs i] (Hs i * set_sep_one (cfHeapsBase_FFI_full
               (events i)))
               (POSTv (\v'.
                    &(v' = semanticPrimitives_Conv (SOME (TypeStamp (implode
                      "Inl") 4))
                             [vs (SUC i)]) *
                  Hs (SUC i) * set_sep_one (cfHeapsBase_FFI_full (events
                    (SUC i)))))) /\
        lprefix_lub (IMAGE (sptree_fromList o events) univ (:num)) io /\ Q
          io) ==>
   app p (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname)
     [xv] H (POSTd Q)`,
  CHEAT_TAC);;


(* -- repeat -- *)

(* HOL4 cfDivScript.sml:2253-2255: ML code, not ported *)

(* HOL4 cfDivScript.sml:2257: ML code, not ported *)

let cause_type_error_def = new_definition
  `cause_type_error = ast_App (ast_FromTo ast_CharT ast_IntT) [ast_Lit
  (ast_IntLit (&0))]`;;

(* evaluate *)
let cfDiv_evaluate = prove
 (`evaluate s env [cause_type_error] = (s,Rerr (Rabort Rtype_error))`,
  CHEAT_TAC);;
add_simp cfDiv_evaluate;;

let then_tyerr_def = new_definition
  `then_tyerr e =
   ast_Let NONE e cause_type_error`;;

(* the clauses in three quotations: es is (exp list) and (_)list; l is lit
   and locs; pes is ((pat # exp) list), (_)list and (_#_)list; recfuns is
   ((varN # varN # exp) list), (_#_)list, (_)list and (_#_#_)list; v is 'n
   and ((modN , varN) id), which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     inv_image (<) (\x. match x with INL (t,x,e) -> ast_exp_size e
                                   | INR (INL (t,es)) -> list_size ast_exp_size
                                     es
                                   | INR (INR (INL (t,x,pes))) ->
                                   list_size (pair_size ast_pat_size
                                     ast_exp_size) pes
                                   | INR (INR (INR (t,funs))) ->
               list_size (pair_size mlstring_size
                          (pair_size mlstring_size ast_exp_size)) funs)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 cfDivScript.sml:2451-2463: the tactic that proves the termination *)
let make_single_app_def,make_single_app_ind = define_guess_clauses
  [`(make_single_app fname allow_fname (ast_Raise e) =
        OPTION_BIND (make_single_app fname F e) (\e.
          SOME ((ast_Raise e:ast_exp)))) /\
    (make_single_app fname allow_fname (ast_Handle e pes) =
        OPTION_BIND (make_single_app fname F e) (\e. OPTION_BIND
            (make_single_appps fname allow_fname pes) (\pes.
          if allow_fname then
            SOME (ast_Handle (then_tyerr e) pes)
          else SOME ((ast_Handle e pes:ast_exp))))) /\
    (make_single_app fname allow_fname (ast_Lit l) =
        if allow_fname then
          SOME (then_tyerr (ast_Lit l))
        else SOME (ast_Lit l)) /\
    (make_single_app fname allow_fname (ast_Var (Short v)) =
        if SOME v = fname then
          NONE
        else if allow_fname then
          SOME (then_tyerr (ast_Var (Short v)))
        else SOME (ast_Var (Short v))) /\
    (make_single_app fname allow_fname (ast_Fun x e) =
        let fname' = (if SOME x = fname then
                       NONE
                     else fname) in
        OPTION_BIND (make_single_app fname' F e) (\e.
          if allow_fname then
            SOME (then_tyerr (ast_Fun x e))
          else SOME (ast_Fun x e))) /\
    (make_single_app fname allow_fname (ast_Log lop e1 e2) =
        OPTION_BIND (make_single_app fname F e1) (\e1. OPTION_BIND
            (make_single_app fname F e2) (\e2.
          if allow_fname then
            SOME (then_tyerr (ast_Log lop e1 e2))
          else SOME (ast_Log lop e1 e2)))) /\
    (make_single_app fname allow_fname (ast_If e1 e2 e3) =
        OPTION_BIND (make_single_app fname F e1) (\e1. OPTION_BIND
            (make_single_app fname allow_fname e2) (\e2. OPTION_BIND
            (make_single_app fname allow_fname e3) (\e3.
          SOME ((ast_If e1 e2 e3:ast_exp)))))) /\
    (make_single_app fname allow_fname (ast_Mat e pes) =
        OPTION_BIND (make_single_app fname F e) (\e. OPTION_BIND
            (make_single_appps fname allow_fname pes) (\pes.
          SOME ((ast_Mat e pes:ast_exp))))) /\
    (make_single_app fname allow_fname (ast_Tannot e ty) =
        OPTION_BIND (make_single_app fname allow_fname e) (\e.
          SOME (ast_Tannot e ty))) /\
    (make_single_app fname allow_fname (ast_Let NONE e1 e2) =
        OPTION_BIND (make_single_app fname F e1) (\e1. OPTION_BIND
            (make_single_app fname allow_fname e2) (\e2.
          SOME ((ast_Let NONE e1 e2:ast_exp))))) /\
    (make_single_app fname allow_fname (ast_Let (SOME x) e1 e2) =
        let fname' =
            (if SOME x = fname then
              NONE
            else fname) in
        OPTION_BIND (make_single_app fname F e1) (\e1. OPTION_BIND
            (make_single_app fname' allow_fname e2) (\e2.
          SOME ((ast_Let (SOME x) e1 e2:ast_exp))))) /\
    (make_single_apps fname [] = SOME []) /\
    (make_single_appps fname allow_fname (CONS (p,e) pes) =
        let fname' = (if EX ((=) fname o SOME) (ast_pat_bindings p) then
            NONE
                     else fname) in
        OPTION_BIND (make_single_app fname' allow_fname e) (\e. OPTION_BIND
            (make_single_appps fname allow_fname pes) (\pes.
          SOME (CONS (p,e) pes)))) /\
    (make_single_appps fname allow_fname [] =
        SOME []) /\
    (make_single_appr fname [] = SOME [])`;
   `(make_single_app fname allow_fname (ast_Con c es) =
        OPTION_BIND (make_single_apps fname es) (\es.
          if allow_fname then
            SOME (then_tyerr (ast_Con c es))
          else SOME (ast_Con c es))) /\
    (make_single_app fname allow_fname (ast_Var v) =
        if allow_fname then
          SOME (then_tyerr (ast_Var v))
        else SOME (ast_Var v)) /\
    (make_single_app fname allow_fname (ast_Lannot e l) =
        OPTION_BIND (make_single_app fname allow_fname e) (\e.
          SOME (ast_Lannot e l))) /\
    (make_single_app fname allow_fname (ast_App op es) =
          (match dest_opapp (ast_App op es) with
             SOME (ast_Var (Short f),[arg]) ->
               (if SOME f = fname then
                 if allow_fname then
                   OPTION_BIND (make_single_app fname F arg) (\arg.
                     SOME arg)
                 else NONE
               else OPTION_BIND (make_single_app fname F arg) (\arg.
                   if allow_fname then
                     SOME (then_tyerr (ast_App op [ast_Var (Short f);
                         arg]))
                   else SOME (ast_App op [ast_Var (Short f); arg])))
           | _ ->
             OPTION_BIND (make_single_apps fname es) (\es.
               if allow_fname then
                 SOME (then_tyerr (ast_App op es))
               else SOME (ast_App op es)))) /\
    (make_single_apps fname (CONS e es) =
        OPTION_BIND (make_single_app fname F e) (\e. OPTION_BIND
            (make_single_apps fname es) (\es.
          SOME (CONS e es))))`;
   `(make_single_app fname allow_fname (ast_Letrec recfuns e) =
        let fname' = (if EX ((=) fname o SOME) (MAP FST recfuns) then NONE
            else fname) in
        OPTION_BIND (make_single_appr fname' recfuns) (\recfuns.
            OPTION_BIND (make_single_app fname' allow_fname e) (\e.
          SOME ((ast_Letrec recfuns e:ast_exp))))) /\
    (make_single_appr fname (CONS (f,x,e) recfuns) =
        let fname' = (if SOME x = fname then NONE else fname) in
        OPTION_BIND (make_single_app fname F e) (\e. OPTION_BIND
            (make_single_appr fname recfuns) (\recfun.
          SOME (CONS (f,x,e) recfuns))))`];;

(* HOL4 cfDivScript.sml:2465: ML code, not ported *)

let make_stepfun_closure_def = new_definition
  `make_stepfun_closure env fname farg fbody =
     OPTION_BIND (make_single_app (SOME fname) T fbody) (\gbody.
      SOME (let benv = semanticPrimitives_build_rec_env
        [(fname,farg,fbody)] env (sem_env_v env) in
        semanticPrimitives_Closure (sem_env_v_fupd (K benv) env) farg
        gbody))`;;

let make_repeat_closure_def = new_definition
  `make_repeat_closure x1 =
     match x1 with
       semanticPrimitives_Recclosure env [(fname,farg,fbody)] name2 ->
       OPTION_BIND (make_stepfun_closure env fname farg fbody) (\gclosure.
        SOME (semanticPrimitives_Closure (sem_env_v_fupd (K
               (nsBind fname gclosure (sem_env_v env))) env) farg
             (ast_App ast_Opapp
                  [ast_App ast_Opapp
                     [ast_Letrec repeat_clos (ast_Var (Short (implode
                       "repeat")));
                      ast_Var (Short fname)];
                   ast_Var (Short farg)])))
     | _ -> NONE`;;

(* [local] *)
let make_single_app_F_unchanged_gen = prove
 (`(!fname allow_fname e e'.
                make_single_app fname allow_fname e = SOME e' /\ allow_fname
                  = F ==> e = e') /\
    (!fname es es'.
                make_single_apps fname es = SOME es' ==> es = es') /\
    (!fname allow_fname pes pes'.
                make_single_appps fname allow_fname pes = SOME pes'
                  /\ allow_fname = F ==> pes = pes') /\
    (!fname recfuns recfuns'.
                make_single_appr fname recfuns = SOME recfuns' ==> recfuns
                  = recfuns')`,
  CHEAT_TAC);;

let make_single_app_F_unchanged =
  SIMP_RULE [] make_single_app_F_unchanged_gen;;

let mk_tyerr_res_def = new_definition
  `mk_tyerr_res r =
   match r with
     Rerr e -> Rerr e
   | r -> Rerr (Rabort Rtype_error)`;;

let evaluate_then_tyerr = prove
 (`evaluate st env [then_tyerr e] =
   match evaluate st env [e] with (st,res) -> (st,mk_tyerr_res res)`,
  CHEAT_TAC);;
add_simp evaluate_then_tyerr;;

let dest_opapp_not_NIL = prove
 (`~(dest_opapp f = SOME (x,[]))`,
  CHEAT_TAC);;
add_simp dest_opapp_not_NIL;;

let make_single_appps_MAP_FST = prove
 (`!pes x b pes'.
     make_single_appps x b pes = SOME pes' ==>
     MAP FST pes = MAP FST pes'`,
  CHEAT_TAC);;

let make_single_app_NONE_evaluate = prove
 (`(!fname allow_fname e e' (st:'ffi semanticPrimitives_state) env.
      make_single_app fname allow_fname e = SOME e' /\
      allow_fname /\ fname = NONE ==>
                evaluate st env [e'] = (match evaluate st env [e] with
                  (st',res) -> (st',mk_tyerr_res res))) /\
   (!fname es es'.
      make_single_apps fname es = SOME es' ==> T) /\
   (!fname allow_fname pes pes' (st:'ffi semanticPrimitives_state) env v
     err_v.
      make_single_appps fname allow_fname pes = SOME pes' /\
      allow_fname /\ fname = NONE ==>
                evaluate_evaluate_match st env v pes' err_v = (match
                  evaluate_evaluate_match st env v pes err_v with
                  (st',res) -> (st',mk_tyerr_res res))) /\
   (!fname recfuns recfuns'.
      make_single_appr fname recfuns = SOME recfuns' ==> T)`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:2665-2666: ML code, not ported *)

let part_evaluates_to_def = new_definition
  `part_evaluates_to fv' env st (e1,e2) =
     match evaluate st env [e1] with
       (st',Rval v1) ->
         (?st'' res. evaluate st env [e2] = (st'',res) /\
             (match semanticPrimitives_do_opapp [fv'; HD v1] with
               SOME (env',e3) ->
                  if semanticPrimitives_state_clock st' = 0 then st'' = st'
                    /\ res = Rerr (Rabort (Rtimeout_error))
                  else evaluate (evaluate_dec_clock st') env' [e3] =
                    (st'',res)
             | NONE -> res = Rerr (Rabort Rtype_error)))
      | (st',Rerr (Rabort Rtype_error)) ->
          (?res. evaluate st env [e2] = (st',res))
      | (st',Rerr err) -> evaluate st env [e2] = (st',Rerr err)`;;

let part_evaluates_to_match_def = new_definition
  `part_evaluates_to_match fv' mv err_v env st (pr1,pr2) =
     match evaluate_evaluate_match st env mv pr1 err_v with
       (st',Rval v1) ->
         (?st'' res. evaluate_evaluate_match st env mv pr2 err_v =
           (st'',res) /\
             (match semanticPrimitives_do_opapp [fv'; HD v1] with
                 SOME (env',e3) ->
                   if semanticPrimitives_state_clock st' = 0 then
                     (st'' = st' /\ res = Rerr (Rabort (Rtimeout_error)))
                   else evaluate (evaluate_dec_clock st') env' [e3] =
                     (st'',res)
               | NONE -> res = Rerr (Rabort Rtype_error)))
      | (st',Rerr (Rabort Rtype_error)) ->
          (?res. evaluate_evaluate_match st env mv pr2 err_v = (st',res))
      | (st',Rerr err) -> evaluate_evaluate_match st env mv pr2 err_v =
        (st',Rerr err)`;;

let make_single_app_SOME_evaluate = prove
 (`(!fname allow_fname e e' (st:'ffi semanticPrimitives_state) env f fv'.
      make_single_app fname allow_fname e = SOME e' /\
      allow_fname /\ fname = SOME f /\ nsLookup (sem_env_v env) (Short f) =
        SOME fv' ==> part_evaluates_to fv' env st (e',e)) /\
   (!fname es es'.
      make_single_apps fname es = SOME es' ==> T) /\
   (!fname allow_fname pes pes' (st:'ffi semanticPrimitives_state) env v
     err_v f fv'.
      make_single_appps fname allow_fname pes = SOME pes' /\
      allow_fname /\ fname = SOME f /\ nsLookup (sem_env_v env) (Short f) =
        SOME fv' ==> part_evaluates_to_match fv' v err_v env st (pes',pes)) /\
   (!fname recfuns recfuns'.
      make_single_appr fname recfuns = SOME recfuns' ==> T)`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:2963-2964: ML code, not ported *)

(* [local] *)
let make_single_app_unroll_lemma = prove
 (`!fname fbody gbody (st:'ffi semanticPrimitives_state) st' ck1 env farg ck2 x
  v.
     make_single_app (SOME fname) T fbody = SOME gbody /\
     evaluate (semanticPrimitives_state_clock_fupd (K ck1) (st:'ffi
       semanticPrimitives_state))
                (sem_env_v_fupd (K
                   (nsBind farg x
                     (nsBind fname (semanticPrimitives_Recclosure env
                       [(fname,farg,fbody)] fname) (sem_env_v
                        env)))) env) [gbody] =
              (semanticPrimitives_state_clock_fupd (K 0) st',Rval [v])
                /\ ~(fname = farg) ==>
     evaluate (semanticPrimitives_state_clock_fupd (K (ck1 + ck2 + 1))
       (st:'ffi semanticPrimitives_state))
              (sem_env_v_fupd (K
               (nsBind farg x
                      (nsBind fname (semanticPrimitives_Recclosure env
                        [(fname,farg,fbody)] fname) (sem_env_v env)))) env)
              [fbody] =
    evaluate (semanticPrimitives_state_clock_fupd (K ck2) st')
             (sem_env_v_fupd (K
              (nsBind farg v
                     (nsBind fname (semanticPrimitives_Recclosure env
                       [(fname,farg,fbody)] fname) (sem_env_v env)))) env)
             [fbody]`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:3005-3151: a theorem whose statement the port cannot
   state yet: evaluate_repeat_diverge_lemma *)

(* HOL4 cfDivScript.sml:3153-3264: a theorem whose statement the port cannot
   state yet: evaluate_repeat_div_ind_lemma *)

(* HOL4 cfDivScript.sml:3266-3354: a theorem whose statement the port cannot
   state yet: evaluate_repeat_div_ind_lemma2 *)

let make_repeat_closure_sound_basic = prove
 (`!fv' env.
     make_repeat_closure (semanticPrimitives_Recclosure env
       [(fname,farg,fbody)] fname) = SOME fv' /\
     ~(fname = farg) /\ app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) fv' x H (POSTd Q) ==> app_basic
       p (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname) x H
       (POSTd Q)`,
  CHEAT_TAC);;

let make_repeat_closure_sound = prove
 (`!fv' env.
     make_repeat_closure (semanticPrimitives_Recclosure env
       [(fname,farg,fbody)] fname) = SOME fv' /\
     ~(fname = farg) /\ app p fv' [x] H (POSTd Q) ==> app p
       (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname) [x] H
       (POSTd Q)`,
  CHEAT_TAC);;

let some_repeat_clos_def = new_definition
  `some_repeat_clos env = semanticPrimitives_Recclosure env repeat_clos
  (implode "repeat")`;;

(* HOL4 cfDivScript.sml:3478-3481: ML code, not ported *)

(* HOL4 cfDivScript.sml:3483: ML code, not ported *)

let repeat_POSTd0 = prove
 (`!p env fv' xv H Q.
     (?Hs events vs io.
        vs 0 = xv /\ SEP_IMP H (Hs 0) /\
        (!i. ?P. Hs i = P * set_sep_one (cfHeapsBase_FFI_full (events i)))
          /\
        (!i.
           (app p fv' [vs i] (Hs i)
                            (POSTv (\v'. &(v' = vs (SUC i)) * Hs (SUC i)))))
                              /\
        lprefix_lub (IMAGE (sptree_fromList o events) UNIV) io /\
        Q io) ==>
     app p (some_repeat_clos env) [fv'; xv] H (POSTd Q)`,
  CHEAT_TAC);;

let IMP_app_POSTd = prove
 (`make_stepfun_closure env fname farg fbody = SOME stepv /\ ~(fname = farg) /\
   (?Hs events vs io.
        vs 0 = xv /\ SEP_IMP H (Hs 0 * set_sep_one (cfHeapsBase_FFI_full
          (events 0))) /\
        (!i.
             app p stepv [vs i] (Hs i * set_sep_one (cfHeapsBase_FFI_full
               (events i)))
               (POSTv (\v'. &(v' = vs (SUC i)) *
                          Hs (SUC i) * set_sep_one (cfHeapsBase_FFI_full
                            (events (SUC i)))))) /\
        lprefix_lub (IMAGE (sptree_fromList o events) univ (:num)) io /\ Q
          io) ==>
   app p (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname)
     [xv] H (POSTd Q)`,
  CHEAT_TAC);;

(* -- FFI_part -- *)

let limited_parts_def = new_definition
  `limited_parts ns ((proj,parts'):('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) <=>
     ns = FLAT (MAP FST parts')`;;

let FFI_part_IN_st2heap_IMP = prove
 (`cfHeapsBase_FFI_part s u ns events IN st2heap p st ==>
   FILTER (ffi_has_index_in ns) (ffi_state_io_events
     (semanticPrimitives_state_ffi st)) = events`,
  CHEAT_TAC);;

let limited_FFI_part_IN_st2heap_IMP = prove
 (`limited_parts ns p ==>
   cfHeapsBase_FFI_part s u ns events IN st2heap p st ==>
     ffi_state_io_events (semanticPrimitives_state_ffi
   st) = events`,
  CHEAT_TAC);;

let repeat_POSTd_one_FFI_part = prove
 (`!p env fv' xv H Q ns.
     limited_parts ns p /\
     (?Hs events vs ss u io.
        vs 0 xv /\ SEP_IMP H (Hs 0) /\
        (!i. ?P. Hs i = P * set_sep_one (cfHeapsBase_FFI_part (ss i) u ns
          (events i))) /\
        (!i xv. vs i xv ==>
           (app p fv' [xv] (Hs i)
                            (POSTv (\v'. &(vs (SUC i) v') * Hs (SUC i)))))
                              /\
        lprefix_lub (IMAGE (sptree_fromList o events) UNIV) io /\
        Q io) ==>
     app p (some_repeat_clos env) [fv'; xv] H (POSTd Q)`,
  CHEAT_TAC);;

let IMP_app_POSTd_one_FFI_part = prove
 (`make_stepfun_closure env fname farg fbody = SOME stepv /\ ~(fname = farg) /\
   limited_parts ns p /\
   (?Hs events vs ss u io.
        vs 0 xv /\ SEP_IMP H (Hs 0 * set_sep_one (cfHeapsBase_FFI_part (ss
          0) u ns (events 0))) /\
        (!i xv'.
             vs i xv' ==>
             app p stepv [xv'] (Hs i * set_sep_one (cfHeapsBase_FFI_part (ss
               i) u ns (events i)))
               (POSTv (\v'. &(vs (SUC i) v') *
                          Hs (SUC i) * set_sep_one (cfHeapsBase_FFI_part (ss
                            (SUC i)) u ns (events (SUC i)))))) /\
        lprefix_lub (IMAGE (sptree_fromList o events) univ (:num)) io /\ Q
          io) ==>
   app p (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname)
     [xv] H (POSTd Q)`,
  CHEAT_TAC);;

(* -- old repeat approach -- *)

(* HOL4 cfDivScript.sml:3986-3987: ML code, not ported *)

(* HOL4 cfDivScript.sml:3989: ML code, not ported *)

(* HOL4 cfDivScript.sml:3991: ML code, not ported *)

(* [local] *)
let evaluate_IMP_io_events_mono = prove
 (`evaluate s e exp = (t,res) ==> io_events_mono
  (semanticPrimitives_state_ffi s) (semanticPrimitives_state_ffi t)`,
  CHEAT_TAC);;

let repeat_POSTd = prove
 (`!p fv' xv H Q.
     (?Hs events vs io.
        vs 0 = xv /\ SEP_IMP H (Hs 0) /\
        (!i. ?P. Hs i = P * set_sep_one (cfHeapsBase_FFI_full (events i)))
          /\
        (!i.
           (app p fv' [vs i] (Hs i)
                            (POSTv (\v'. &(v' = vs (SUC i)) * Hs (SUC i)))))
                              /\
        lprefix_lub (IMAGE (sptree_fromList o events) UNIV) io /\
        Q io) ==>
     app p repeat_v [fv'; xv] H (POSTd Q)`,
  CHEAT_TAC);;

let repeat_POSTe = prove
 (`!(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) fv' xv H Q.
     (?Hs vs j.
         vs 0 = xv /\ SEP_IMP H (Hs 0) /\
         (!i. i < j ==>
           app p fv' [vs i] (Hs i) (POSTv (\v. &(v = vs (SUC i)) * Hs (SUC
             i)))) /\
         app p fv' [vs j] (Hs j) (POSTe Q)) ==>
           app p repeat_v [fv'; xv] H (POSTe Q)`,
  CHEAT_TAC);;

(* TODO: up-to techniques duplicated from divTheory; should go elsewhere (llistTheory?)
         other stuff can probably be moved to llistTheory, various other cf theories,
         evaluateProps etc.
*)
let llist_upto = cake_inductive
  `(llist_upto R x x) /\
   (R x y ==> llist_upto R x y) /\
   (llist_upto R x y /\ llist_upto R y z ==> llist_upto R x z) /\
   (llist_upto R x y ==> llist_upto R (LAPPEND z x) (LAPPEND z y))`;;

(* HOL4 cfDivScript.sml:4234-4238: ML code, not ported *)

let LLIST_BISIM_UPTO = prove
 (`!ll1 ll2 R'.
     R' ll1 ll2 /\
     (!ll3 ll4.
       R' ll3 ll4 ==>
       ll3 = LNIL /\ ll4 = LNIL \/
       LHD ll3 = LHD ll4 /\
       llist_upto R' (THE (LTL ll3)) (THE (LTL ll4))) ==> ll1 = ll2`,
  CHEAT_TAC);;


let LFLATTEN_fromList = prove
 (`!l.
     LFLATTEN (sptree_fromList (MAP sptree_fromList l)) = sptree_fromList
       (FLAT l)`,
  CHEAT_TAC);;

let parts_ok_remove_events = prove
 (`parts_ok (semanticPrimitives_state_ffi st) (q,r) ==> parts_ok
  (ffi_state_io_events_fupd (K []) (semanticPrimitives_state_ffi st)) (q,r)`,
  CHEAT_TAC);;

let evaluate_ck_history_irrelevance = prove
 (`(!(st:'ffi semanticPrimitives_state) env ck exp st' res l.
   evaluate_ck ck (semanticPrimitives_state_ffi_fupd (K
     (ffi_state_io_events_fupd (K l) (semanticPrimitives_state_ffi st))) st)
     env exp = (st',res) ==> evaluate_ck ck st env exp =
     (semanticPrimitives_state_ffi_fupd (K (ffi_state_io_events_fupd (K
     (APPEND (ffi_state_io_events (semanticPrimitives_state_ffi st)) (DROP
     (LENGTH l) (ffi_state_io_events (semanticPrimitives_state_ffi st')))))
     (semanticPrimitives_state_ffi st'))) st',res))`,
  CHEAT_TAC);;

let remove_events_IMAGE = prove
 (`parts_ok (semanticPrimitives_state_ffi st) p ==>
   st2heap p (semanticPrimitives_state_ffi_fupd (K (ffi_state_io_events_fupd
     (K []) (semanticPrimitives_state_ffi st))) st) =
   IMAGE (\x. match x with cfHeapsBase_FFI_part s u ns l ->
     cfHeapsBase_FFI_part s u ns []
                      | _ -> x) (st2heap p st)`,
  CHEAT_TAC);;

let parts_ok_swap_events = prove
 (`parts_ok (semanticPrimitives_state_ffi st) p /\
   ALL (ffi_has_index_in (FLAT (MAP FST (SND p)))) es ==>
   parts_ok (ffi_state_io_events_fupd (K es) (semanticPrimitives_state_ffi
     st)) p`,
  CHEAT_TAC);;

let FFI_part_has_index_in = prove
 (`cfHeapsBase_FFI_part s u ns es IN st2heap p st' ==>
   ALL (ffi_has_index_in (FLAT (MAP FST (SND p)))) es`,
  CHEAT_TAC);;

let remove_events_IMAGE2 = prove
 (`parts_ok (semanticPrimitives_state_ffi st) p /\
   parts_ok (ffi_state_io_events_fupd (K es) (semanticPrimitives_state_ffi
     st)) p ==>
   st2heap p (semanticPrimitives_state_ffi_fupd (K (ffi_state_io_events_fupd
     (K es) (semanticPrimitives_state_ffi st))) st) =
   IMAGE (\x. match x with cfHeapsBase_FFI_part s u ns l ->
     cfHeapsBase_FFI_part s u ns (FILTER (ffi_has_index_in ns) es)
                      | _ -> x) (st2heap p st)`,
  CHEAT_TAC);;

(* TODO: move every_LNTH *)
let every_LNTH = prove
 (`!P ll. every P ll <=> (!n e. LNTH n ll = SOME e ==> P e)`,
  CHEAT_TAC);;

let LNTH_LUNFOLD_SOME = prove
 (`!n f g x.
    LNTH n (LUNFOLD (\x. SOME (f x,g x)) x) =
    SOME (g (ITER n f x))`,
  CHEAT_TAC);;

(* [local] *)
let every_LGENLIST = prove
 (`every P (LGENLIST f NONE) = (!x. P (f x))`,
  CHEAT_TAC);;

let LFLATTEN_LAPPEND_fromList = prove
 (`!l1 ll2.
   LFLATTEN (LAPPEND (sptree_fromList l1) ll2) = LAPPEND (LFLATTEN
     (sptree_fromList l1)) (LFLATTEN ll2)`,
  CHEAT_TAC);;

(* HOL4 cfDivScript.sml:4387-4393: a theorem whose statement the port cannot
   state yet: LGENLIST_NONE_UNFOLD *)

let LAPPEND_fromList_EQ = prove
 (`!l ll ll'.
     LAPPEND (sptree_fromList l) ll = LAPPEND (sptree_fromList l) ll' ==>
       ll = ll'`,
  CHEAT_TAC);;

let LFLATTEN_NOT_NIL_IMP = prove
 (`~(LFLATTEN ll = LNIL) ==>
   (?n ll2. LNTH n ll = SOME ll2 /\ ~(ll2 = LNIL))`,
  CHEAT_TAC);;

let LFINITE_LFLATTEN_LGENERATE = prove
 (`LFINITE (LFLATTEN (LGENLIST f NONE)) ==>
   (?n. LFLATTEN (LGENLIST (f o (+) n) NONE) = LNIL)`,
  CHEAT_TAC);;

(* [local] *)
let list_length_eq = prove
 (`l1 = l2 ==> LENGTH l1 = LENGTH l2`,
  CHEAT_TAC);;

(* [local] *)
let list_length_eq2 = prove
 (`l1 = l2 ==> LENGTH (FLAT (MAP FST l1)) = LENGTH (FLAT (MAP FST l2))`,
  CHEAT_TAC);;

let MEM_FLAT_MAP_FST_SING = prove
 (`MEM (FLAT (MAP FST r),u) r /\
   ALL_DISTINCT (FLAT (MAP FST r)) /\
   MEM (ns,u') r /\ ~(ns = []) ==>
   ns = FLAT (MAP FST r) /\ u' = u`,
  CHEAT_TAC);;

let limited_parts_unique_part = prove
 (`limited_parts ns p /\
   cfHeapsBase_FFI_part s u ns events IN st2heap p st /\
   cfHeapsBase_FFI_part s' u' ns' events' IN st2heap p st ==>
   s = s' /\ u = u' /\ ns = ns' /\ events = events'`,
  CHEAT_TAC);;

let IMAGE_purge_parts_no_parts = prove
 (`(!s u ns es. ~(cfHeapsBase_FFI_part s u ns es IN h)) ==>
   IMAGE
       (\x.
            match x with
              cfHeapsBase_Mem v7 v8 -> x
            | cfHeapsBase_FFI_split -> x
            | cfHeapsBase_FFI_part s u ns l -> cfHeapsBase_FFI_part s u ns
              []
            | cfHeapsBase_FFI_full v13 -> x) h = h`,
  CHEAT_TAC);;

let IMAGE_purge_parts_no_parts2 = prove
 (`(!s u ns es. ~(cfHeapsBase_FFI_part s u ns es IN h)) ==>
   IMAGE
       (\x.
            match x with
              cfHeapsBase_Mem v7 v8 -> x
            | cfHeapsBase_FFI_split -> x
            | cfHeapsBase_FFI_part s u ns l -> cfHeapsBase_FFI_part s u ns
              (f ns)
            | cfHeapsBase_FFI_full v13 -> x) h = h`,
  CHEAT_TAC);;

let LFLATTEN_fromList_REPLICATE_LNIL = prove
 (`LFLATTEN (sptree_fromList (REPLICATE a1 LNIL)) = LNIL`,
  CHEAT_TAC);;

let repeat_POSTd_one_FFI_part_FLATTEN = prove
 (`!p env fv' xv H Q ns.
     limited_parts ns p /\
     (?Hs events vs ss u io.
        vs 0 xv /\ SEP_IMP H (Hs 0 * set_sep_one (cfHeapsBase_FFI_part (ss
          0) u ns (events 0))) /\
        (!i xv. vs i xv ==>
           (app p fv' [xv] (Hs i * set_sep_one (cfHeapsBase_FFI_part (ss i)
             u ns []))
                            (POSTv (\v'.
                             &(vs (SUC i) v') * Hs (SUC i) * set_sep_one
                               (cfHeapsBase_FFI_part (ss (SUC i)) u ns (events
                               (SUC i))))))) /\
        Q (LFLATTEN (LGENLIST (sptree_fromList o events) NONE))) ==>
     app p (some_repeat_clos env) [fv'; xv] H (POSTd Q)`,
  CHEAT_TAC);;

let LFLATTEN_LGENLIST_REPEAT = prove
 (`LFLATTEN (LGENLIST (\x. sptree_fromList l) NONE) = LREPEAT l`,
  CHEAT_TAC);;

let IMP_app_POSTd_one_FFI_part_FLATTEN = prove
 (`make_stepfun_closure env fname farg fbody = SOME stepv /\ ~(fname = farg) /\
   limited_parts ns p /\
   (?Hs events vs ss u io.
      vs 0 xv /\ SEP_IMP H (Hs 0 * set_sep_one (cfHeapsBase_FFI_part (ss 0)
        u ns (events 0))) /\
      (!i xv. vs i xv ==>
         (app p stepv [xv] (Hs i * set_sep_one (cfHeapsBase_FFI_part (ss i)
           u ns []))
                          (POSTv (\v'.
                           &(vs (SUC i) v') * Hs (SUC i) * set_sep_one
                             (cfHeapsBase_FFI_part (ss (SUC i)) u ns (events
                             (SUC i))))))) /\
      Q (LFLATTEN (LGENLIST (sptree_fromList o events) NONE))) ==>
   app p (semanticPrimitives_Recclosure env [(fname,farg,fbody)] fname)
     [xv] H (POSTd Q)`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["arg1";
   "arg2";
   "exps";
   "fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
