(* ======================================================== *)
(*  clos_mti: ported from HOL4's
    compiler/backend/clos_mtiScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase introduces multi-argument function applications
  and function closures. This phase enables subsequent compiler phases
  to make use of closLang's support for true multi-argument
  functions. This phase is vital for good performance.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;

let collect_args_def = cake_define
  `collect_args max_app num_args e =
        match e with
          (closLang_Fn t NONE NONE num_args' e) ->
       if num_args + num_args' <= max_app then
         collect_args max_app (num_args + num_args') e else
         (num_args,closLang_Fn t NONE NONE num_args' e)
        | e -> (num_args,e)`;;

(* HOL4 ML code, not ported:
val collect_args_ind = theorem "collect_args_ind";
*)

let collect_apps_def = cake_define
  `collect_apps max_app args e =
        match e with
          (closLang_App tra NONE e es) ->
       if LENGTH args + LENGTH es <= max_app then
         collect_apps max_app (args ++ es) e else
         (args,closLang_App tra NONE e es)
        | e -> (args,e)`;;

(* HOL4 ML code, not ported:
val collect_apps_ind = theorem "collect_apps_ind";
*)

(* HOL4 termination: >> rw[]>> imp_res_tac collect_args_size >>
   imp_res_tac collect_apps_size >> gvs[]>> drule MEM_list_size>>
   disch_then (qspec_then `pair_size (λx. x) exp_size` mp_tac)>>
   simp[list_size_pair_size_MAP_FST_SND] *)
let intro_multi_def = cake_define_wf
  `MEASURE (list_size exp_size o SND)`
  `intro_multi max_app x2 =
        match x2 with
          [] -> []
        | (e1 :: e2 :: es) ->
       HD (intro_multi max_app [e1]) :: HD (intro_multi max_app [e2])
         :: intro_multi max_app es
        | [closLang_Var t n] -> [closLang_Var t n]
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
       let (es',e') = collect_apps max_app es e in
         [closLang_App t NONE (HD (intro_multi max_app [e']))
           (intro_multi max_app es')]
        | [closLang_App t (SOME l) e es] ->
       [closLang_App t (SOME l) (HD (intro_multi max_app [e]))
         (intro_multi max_app es)]
        | [closLang_Fn t NONE NONE num_args e] ->
       let (num_args',e') = collect_args max_app num_args e in
         [closLang_Fn t NONE NONE num_args' (HD (intro_multi max_app
           [e']))]
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
        | [closLang_Op t closLang_op es] ->
       [closLang_Op t closLang_op (intro_multi max_app es)]`;;

(* HOL4 ML code, not ported:
val intro_multi_ind = theorem "intro_multi_ind";
*)

let compile_def = cake_define
  `clos_mti_compile F max_app exps = exps /\
   clos_mti_compile T max_app exps = intro_multi max_app exps`;;

let compile_inc_def = cake_define
  `clos_mti_compile_inc max_app (e,es) =
     (intro_multi max_app e,[])`;;

let cond_mti_compile_inc_def = cake_define
  `cond_mti_compile_inc do_it max_app =
     (if do_it then (clos_mti_compile_inc max_app) else I)`;;
