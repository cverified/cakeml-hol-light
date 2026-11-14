(* ======================================================== *)
(*  clos_mti: ported from HOL4's
    compiler/backend/clos_mtiScript.sml
    A definition theory, with 6 definitions and 12 theorems.  Needed
    by backendProof.ml, clos_mtiProof.ml, clos_to_bvl.ml and
    clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  This compiler phase introduces multi-argument function applications
  and function closures. This phase enables subsequent compiler phases
  to make use of closLang's support for true multi-argument
  functions. This phase is vital for good performance.
*)

needs "compiler/backend/closLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_mti"
  ["closLang"];;

let _ = size_thms "closLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let collect_args_def,collect_args_ind = define_wf
  `MEASURE (\(x0,x1,x2). closLang_exp_size x2)`
  [`collect_args max_app num_args e =
        match e with
          closLang_Fn t NONE NONE num_args' e ->
       (if num_args + num_args' <= max_app then
         collect_args max_app (num_args + num_args') e else
         (num_args,closLang_Fn t NONE NONE num_args' e))
        | e -> (num_args,e)`];;

(* HOL4 clos_mtiScript.sml:22: ML code, not ported *)

let collect_args_size = prove
 (`!max_app num_args e num_args' e'.
     (num_args',e') = collect_args max_app num_args e ==>
     num_args' + closLang_exp_size e' <= num_args +
       closLang_exp_size e`,
  CHEAT_TAC);;

(* [local] *)
let collect_args_more = prove
 (`!max_app num_args e num_args' e'.
     (num_args',e') = collect_args max_app num_args e ==>
     num_args <= num_args'`,
  CHEAT_TAC);;

let collect_args_zero = prove
 (`!max_app num_args e e'.
    collect_args max_app num_args e = (0,e') ==>
    num_args = 0`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let collect_apps_def,collect_apps_ind = define_wf
  `MEASURE (\(x0,x1,x2). closLang_exp_size x2)`
  [`collect_apps max_app args e =
        match e with
          (closLang_App tra NONE e es:closLang_exp) ->
       (if LENGTH args + LENGTH es <= max_app then
         collect_apps max_app (APPEND args es) e else
         (args,closLang_App tra NONE e es))
        | e -> (args,e)`];;

(* HOL4 clos_mtiScript.sml:70: ML code, not ported *)

(* HOL4 clos_mtiScript.sml:72-77: a theorem whose statement the port
   cannot state yet: exp3_size_append *)

(* [local] *)
let collect_apps_more = prove
 (`!max_app args e args' e'.
     (args',e') = collect_apps max_app args e ==>
     LENGTH args <= LENGTH args'`,
  CHEAT_TAC);;

let collect_apps_size = prove
 (`!max_app args e args' e'.
    (args',e') = collect_apps max_app args e ==>
    list_size closLang_exp_size args' + closLang_exp_size e' <=
      list_size closLang_exp_size args + closLang_exp_size e`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (list_size closLang_exp_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 clos_mtiScript.sml:144-153: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let intro_multi_def,intro_multi_ind = define_guess_cheat
  [`intro_multi max_app x2 =
        match x2 with
          [] -> []
        | (CONS e1 (CONS e2 es)) -> CONS (HD (intro_multi max_app
          [e1])) (CONS (HD (intro_multi max_app [e2])) (intro_multi
          max_app es))
        | [(closLang_Var t n:closLang_exp)] -> [closLang_Var t n]
        | [closLang_If t e1 e2 e3] ->
      [closLang_If t (HD (intro_multi max_app [e1]))
            (HD (intro_multi max_app [e2]))
            (HD (intro_multi max_app [e3]))]
        | [closLang_Let t es e] ->
       [closLang_Let t (intro_multi max_app es) (HD (intro_multi
         max_app [e]))]
        | [closLang_Raise t e] ->
       [closLang_Raise t (HD (intro_multi max_app [e]))]
        | [closLang_Handle t e1 e2] ->
       [closLang_Handle t (HD (intro_multi max_app [e1])) (HD
         (intro_multi max_app [e2]))]
        | [closLang_Tick t e] ->
       [closLang_Tick t (HD (intro_multi max_app [e]))]
        | [closLang_Call t ticks n es] ->
       [closLang_Call t ticks n (intro_multi max_app es)]
        | [closLang_App t NONE e es] ->
       (let (es',e') = collect_apps max_app es e in
         [closLang_App t NONE (HD (intro_multi max_app [e']))
           (intro_multi max_app es')])
        | [closLang_App t (SOME l) e es] ->
       [closLang_App t (SOME l) (HD (intro_multi max_app [e]))
         (intro_multi max_app es)]
        | [closLang_Fn t NONE NONE num_args e] ->
       (let (num_args',e') = collect_args max_app num_args e in
         [closLang_Fn t NONE NONE num_args' (HD (intro_multi max_app
           [e']))])
        | [closLang_Fn t loc fvs num_args e] ->
         [closLang_Fn t loc fvs num_args (HD (intro_multi max_app
           [e]))]
        | [closLang_Letrec t NONE NONE funs e] ->
       [closLang_Letrec t NONE NONE (MAP (\(num_args,e).
                              let (num_args',e') = collect_args
                                max_app num_args e in
                              (num_args',HD (intro_multi max_app
                                [e'])))
                             funs)
               (HD (intro_multi max_app [e]))]
        | [closLang_Letrec t (SOME loc) fvs funs e] ->
        [closLang_Letrec t (SOME loc) fvs funs (HD (intro_multi
          max_app [e]))]
        | [closLang_Letrec t NONE (SOME fvs) funs e] ->
        [closLang_Letrec t NONE (SOME fvs) funs (HD (intro_multi
          max_app [e]))]
        | [closLang_Op t op es] ->
       [closLang_Op t op (intro_multi max_app es)]`];;

(* HOL4 clos_mtiScript.sml:155: ML code, not ported *)

let intro_multi_length = prove
 (`!max_app es. LENGTH (intro_multi max_app es) = LENGTH es`,
  CHEAT_TAC);;

let intro_multi_sing = prove
 (`!e max_app. ?e'. intro_multi max_app [e] = [e']`,
  (REPEAT GEN_TAC THEN
   MP_TAC (ISPECL [`max_app:num`; `[e:closLang_exp]`]
     intro_multi_length) THEN
   SPEC_TAC (`intro_multi max_app [e]`,`l:closLang_exp list`) THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ;
     LENGTH_EQ_NIL] THEN
   MESON_TAC[]));;

let collect_args_idem = prove
 (`!max_app num_args e num_args' e'.
    collect_args max_app num_args e = (num_args',e') ==>
    collect_args max_app num_args' (HD (intro_multi max_app [e']))
      = (num_args',(HD (intro_multi max_app [e'])))`,
  CHEAT_TAC);;

let collect_apps_idem = prove
 (`!max_app args e args' e'.
    collect_apps max_app args e = (args',e') ==>
    collect_apps max_app (intro_multi max_app args') (HD
      (intro_multi max_app [e'])) = (intro_multi max_app args',(HD
      (intro_multi max_app [e'])))`,
  CHEAT_TAC);;

let intro_multi_idem = prove
 (`!max_app e. intro_multi max_app (intro_multi max_app e) =
  intro_multi max_app e`,
  CHEAT_TAC);;

let clos_mti_compile_def = define_general
  [`clos_mti_compile F max_app exps = exps`;
   `clos_mti_compile T max_app exps = intro_multi max_app exps`];;

let clos_mti_compile_inc_def = new_definition
  `clos_mti_compile_inc max_app (e,es) =
     (intro_multi max_app e,[])`;;

let cond_mti_compile_inc_def = new_definition
  `cond_mti_compile_inc do_it max_app =
     (if do_it then (clos_mti_compile_inc max_app) else I)`;;

(* compile_nil *)
let clos_mti_compile_nil = prove
 (`clos_mti_compile do_mti max_app [] = []`,
  CHEAT_TAC);;
add_simp clos_mti_compile_nil;;

(* and the interface *)
let _ = unhide_overloads ();;
