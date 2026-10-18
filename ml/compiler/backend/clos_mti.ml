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
needs "semantics/ast.ml";;

let collect_args_def = cake_define
  `collect_args max_app num_args e =
        match e with
          closLang_Fn t NONE NONE num_args' e ->
       (if num_args + num_args' <= max_app then
         collect_args max_app (num_args + num_args') e else
         (num_args,closLang_Fn t NONE NONE num_args' e))
        | e -> (num_args,e)`;;

(* HOL4 clos_mtiScript.sml:22: ML code, not ported *)

let collect_args_size = cake_theorem "collect_args_size"
  (fun () ->
    `!max_app num_args e num_args' e'.
       (num_args',e') = collect_args max_app num_args e ==>
       num_args' + closLang_exp_size e' <= num_args +
         closLang_exp_size e`)
  CHEAT_TAC;;

let collect_args_more = cake_theorem "collect_args_more[local]"
  (fun () ->
    `!max_app num_args e num_args' e'.
       (num_args',e') = collect_args max_app num_args e ==>
       num_args <= num_args'`)
  CHEAT_TAC;;

let collect_args_zero = cake_theorem "collect_args_zero"
  (fun () ->
    `!max_app num_args e e'.
      collect_args max_app num_args e = (0,e') ==>
      num_args = 0`)
  CHEAT_TAC;;

let collect_apps_def = cake_define
  `collect_apps max_app args e =
        match e with
          (App tra NONE e es:closLang_exp) ->
       (if LENGTH args + LENGTH es <= max_app then
         collect_apps max_app (args ++ es) e else
         (args,App tra NONE e es))
        | e -> (args,e)`;;

(* HOL4 clos_mtiScript.sml:70: ML code, not ported *)

(* HOL4 clos_mtiScript.sml:72-77: a theorem whose statement the port
   cannot state yet: exp3_size_append *)

let collect_apps_more = cake_theorem "collect_apps_more[local]"
  (fun () ->
    `!max_app args e args' e'.
       (args',e') = collect_apps max_app args e ==>
       LENGTH args <= LENGTH args'`)
  CHEAT_TAC;;

let collect_apps_size = cake_theorem "collect_apps_size"
  (fun () ->
    `!max_app args e args' e'.
      (args',e') = collect_apps max_app args e ==>
      list_size closLang_exp_size args' + closLang_exp_size e' <=
        list_size closLang_exp_size args + closLang_exp_size e`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* HOL4 clos_mtiScript.sml:144-153: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let intro_multi_def = cake_define_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
  `intro_multi max_app x2 =
        match x2 with
          [] -> []
        | (e1 :: e2 :: es) ->
       HD (intro_multi max_app [e1]) :: HD (intro_multi max_app [e2])
         :: intro_multi max_app es
        | [(Var t n:closLang_exp)] -> [Var t n]
        | [If t e1 e2 e3] ->
      [If t (HD (intro_multi max_app [e1]))
            (HD (intro_multi max_app [e2]))
            (HD (intro_multi max_app [e3]))]
        | [Let t es e] ->
       [Let t (intro_multi max_app es) (HD (intro_multi max_app
         [e]))]
        | [Raise t e] ->
       [Raise t (HD (intro_multi max_app [e]))]
        | [Handle t e1 e2] ->
       [Handle t (HD (intro_multi max_app [e1])) (HD (intro_multi
         max_app [e2]))]
        | [closLang_Tick t e] ->
       [closLang_Tick t (HD (intro_multi max_app [e]))]
        | [closLang_Call t ticks n es] ->
       [closLang_Call t ticks n (intro_multi max_app es)]
        | [App t NONE e es] ->
       (let (es',e') = collect_apps max_app es e in
         [App t NONE (HD (intro_multi max_app [e'])) (intro_multi
           max_app es')])
        | [App t (SOME l) e es] ->
       [App t (SOME l) (HD (intro_multi max_app [e])) (intro_multi
         max_app es)]
        | [closLang_Fn t NONE NONE num_args e] ->
       (let (num_args',e') = collect_args max_app num_args e in
         [closLang_Fn t NONE NONE num_args' (HD (intro_multi max_app
           [e']))])
        | [closLang_Fn t loc fvs num_args e] ->
         [closLang_Fn t loc fvs num_args (HD (intro_multi max_app
           [e]))]
        | [Letrec t NONE NONE funs e] ->
       [Letrec t NONE NONE (MAP (\(num_args,e).
                              let (num_args',e') = collect_args
                                max_app num_args e in
                              (num_args',HD (intro_multi max_app
                                [e'])))
                             funs)
               (HD (intro_multi max_app [e]))]
        | [Letrec t (SOME loc) fvs funs e] ->
        [Letrec t (SOME loc) fvs funs (HD (intro_multi max_app [e]))]
        | [Letrec t NONE (SOME fvs) funs e] ->
        [Letrec t NONE (SOME fvs) funs (HD (intro_multi max_app
          [e]))]
        | [closLang_Op t op es] ->
       [closLang_Op t op (intro_multi max_app es)]`;;

(* HOL4 clos_mtiScript.sml:155: ML code, not ported *)

let intro_multi_length = cake_theorem "intro_multi_length"
  (fun () ->
    `!max_app es. LENGTH (intro_multi max_app es) = LENGTH es`)
  CHEAT_TAC;;

let intro_multi_sing = cake_theorem "intro_multi_sing"
  (fun () ->
    `!e max_app. ?e'. intro_multi max_app [e] = [e']`)
  CHEAT_TAC;;

let collect_args_idem = cake_theorem "collect_args_idem"
  (fun () ->
    `!max_app num_args e num_args' e'.
      collect_args max_app num_args e = (num_args',e') ==>
      collect_args max_app num_args' (HD (intro_multi max_app
        [e'])) = (num_args',(HD (intro_multi max_app [e'])))`)
  CHEAT_TAC;;

let collect_apps_idem = cake_theorem "collect_apps_idem"
  (fun () ->
    `!max_app args e args' e'.
      collect_apps max_app args e = (args',e') ==>
      collect_apps max_app (intro_multi max_app args') (HD
        (intro_multi max_app [e'])) = (intro_multi max_app args',(HD
        (intro_multi max_app [e'])))`)
  CHEAT_TAC;;

let intro_multi_idem = cake_theorem "intro_multi_idem"
  (fun () ->
    `!max_app e. intro_multi max_app (intro_multi max_app e) =
  intro_multi max_app e`)
  CHEAT_TAC;;

let compile_def = cake_define_list
  [`clos_mti_compile F max_app exps = exps`;
   `clos_mti_compile T max_app exps = intro_multi max_app exps`];;
hol4_overload "compile" "clos_mti_compile";;

let compile_inc_def = cake_define
  `clos_mti_compile_inc max_app (e,es) =
     (intro_multi max_app e,[])`;;
hol4_overload "compile_inc" "clos_mti_compile_inc";;

let cond_mti_compile_inc_def = cake_define
  `cond_mti_compile_inc do_it max_app =
     (if do_it then (clos_mti_compile_inc max_app) else I)`;;

let clos_mti_compile_nil = cake_theorem "compile_nil[simp]"
  (fun () ->
    `clos_mti_compile do_mti max_app [] = []`)
  CHEAT_TAC;;
