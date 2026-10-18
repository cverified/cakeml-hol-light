(* ======================================================== *)
(*  closProps: ported from HOL4's
    compiler/backend/semantics/closPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about closLang and its semantics
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

let ref_rel_def = cake_define
  `closProps_ref_rel R x2 x3 =
        match (x2,x3) with
          (closSem_ValueArray vs,closSem_ValueArray ws) -> LIST_REL R
            vs ws
        | ((closSem_ByteArray as),(closSem_ByteArray bs)) -> as = bs
        | ((Thunk ma a),(Thunk mb b)) -> ma = mb /\ R a b
        | (_1,_2) -> F`;;
hol4_overload "ref_rel" "closProps_ref_rel";;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:158-161: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let code_locs_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`code_locs [] = []`;
   `code_locs (x :: y :: xs) =
         (let c1 = code_locs [x] in
         let c2 = code_locs (y :: xs) in
           c1 ++ c2)`;
   `code_locs [(Var _4 v:closLang_exp)] = []`;
   `code_locs [(If _6 x1 x2 x3:closLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs [x2] in
         let c3 = code_locs [x3] in
           c1 ++ c2 ++ c3)`;
   `code_locs [(Let _8 xs x2:closLang_exp)] =
         (let c1 = code_locs xs in
         let c2 = code_locs [x2] in
           c1 ++ c2)`;
   `code_locs [(Raise _10 x1:closLang_exp)] =
         code_locs [x1]`;
   `code_locs [(closLang_Tick _12 x1:closLang_exp)] =
         code_locs [x1]`;
   `code_locs [(closLang_Op _14 op xs:closLang_exp)] =
         code_locs xs`;
   `code_locs [(App _16 loc_opt x1 xs:closLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs xs in
             c1 ++ c2)`;
   `code_locs [closLang_Fn _17 loc_opt vs num_args x1] =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let c1 = code_locs [x1] in
           c1 ++ [loc])`;
   `code_locs [(Letrec _19 loc_opt vs fns x1:closLang_exp)] =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let c1 = code_locs (MAP SND fns) in
         let c2 = code_locs [x1] in
         c1 ++ GENLIST (\n. loc + 2 * n) (LENGTH fns) ++ c2)`;
   `code_locs [(Handle _21 x1 x2:closLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs [x2] in
           c1 ++ c2)`;
   `code_locs [(closLang_Call _23 ticks dest xs:closLang_exp)] =
         code_locs xs`];;

let _ = size_thms "closLang_exp";;
(* HOL4 closPropsScript.sml:229-232: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let contains_App_SOME_def = cake_define_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
  `contains_App_SOME max_app x2 =
        match x2 with
          [] -> F
        | (x :: y :: xs) ->
        contains_App_SOME max_app [x] \/
        contains_App_SOME max_app (y :: xs)
        | [(Var _25 v:closLang_exp)] -> F
        | [If _26 x1 x2 x3] ->
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app [x2] \/
        contains_App_SOME max_app [x3]
        | [Let _27 xs x2] ->
        contains_App_SOME max_app [x2] \/
        contains_App_SOME max_app xs
        | [Raise _28 x1] ->
        contains_App_SOME max_app [x1]
        | [closLang_Tick _29 x1] ->
        contains_App_SOME max_app [x1]
        | [closLang_Op _30 (ThunkOp ForceThunk) xs] ->
        max_app < 1 \/
        contains_App_SOME max_app xs
        | [closLang_Op _31 op xs] ->
        contains_App_SOME max_app xs
        | [App _32 loc_opt x1 x2] ->
        IS_SOME loc_opt \/ max_app < LENGTH x2 \/
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app x2
        | [closLang_Fn _33 loc vs num_args x1] ->
        contains_App_SOME max_app [x1]
        | [Letrec _34 loc vs fns x1] ->
        contains_App_SOME max_app (MAP SND fns) \/
        contains_App_SOME max_app [x1]
        | [Handle _35 x1 x2] ->
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app [x2]
        | [closLang_Call _36 ticks dest xs] ->
        contains_App_SOME max_app xs`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:275-278: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let every_Fn_SOME_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`every_Fn_SOME [] <=> T`;
   `every_Fn_SOME (x :: y :: xs) <=>
         every_Fn_SOME [x] /\
         every_Fn_SOME (y :: xs)`;
   `every_Fn_SOME [(Var _38 v:closLang_exp)] <=> T`;
   `every_Fn_SOME [(If _40 x1 x2 x3:closLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME [x2] /\
         every_Fn_SOME [x3]`;
   `every_Fn_SOME [(Let _42 xs x2:closLang_exp)] <=>
         every_Fn_SOME [x2] /\
         every_Fn_SOME xs`;
   `every_Fn_SOME [(Raise _44 x1:closLang_exp)] <=>
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(closLang_Tick _46 x1:closLang_exp)] <=>
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(closLang_Op _48 op xs:closLang_exp)] <=>
         every_Fn_SOME xs`;
   `every_Fn_SOME [(App _50 loc_opt x1 x2:closLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME x2`;
   `every_Fn_SOME [closLang_Fn _51 loc_opt vs num_args x1] <=>
         IS_SOME loc_opt /\
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(Letrec _53 loc_opt vs fns x1:closLang_exp)] <=>
         IS_SOME loc_opt /\
         every_Fn_SOME (MAP SND fns) /\
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(Handle _55 x1 x2:closLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME [x2]`;
   `every_Fn_SOME [(closLang_Call _57 ticks dest xs:closLang_exp)] <=>
         every_Fn_SOME xs`];;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:327-330: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let every_Fn_vs_NONE_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`every_Fn_vs_NONE [] <=> T`;
   `every_Fn_vs_NONE (x :: y :: xs) <=>
         every_Fn_vs_NONE [x] /\
         every_Fn_vs_NONE (y :: xs)`;
   `every_Fn_vs_NONE [(Var _59 v:closLang_exp)] <=> T`;
   `every_Fn_vs_NONE [(If _61 x1 x2 x3:closLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE [x2] /\
         every_Fn_vs_NONE [x3]`;
   `every_Fn_vs_NONE [(Let _63 xs x2:closLang_exp)] <=>
         every_Fn_vs_NONE [x2] /\
         every_Fn_vs_NONE xs`;
   `every_Fn_vs_NONE [(Raise _65 x1:closLang_exp)] <=>
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(closLang_Tick _67 x1:closLang_exp)] <=>
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(closLang_Op _69 op xs:closLang_exp)] <=>
         every_Fn_vs_NONE xs`;
   `every_Fn_vs_NONE [(App _71 loc_opt x1 x2:closLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE x2`;
   `every_Fn_vs_NONE [closLang_Fn _72 loc vs_opt num_args x1] <=>
         IS_NONE vs_opt /\
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(Letrec _74 loc vs_opt fns x1:closLang_exp)] <=>
         IS_NONE vs_opt /\
         every_Fn_vs_NONE (MAP SND fns) /\
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(Handle _76 x1 x2:closLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE [x2]`;
   `every_Fn_vs_NONE [(closLang_Call _78 ticks dest xs:closLang_exp)]
  <=>
         every_Fn_vs_NONE xs`];;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:386-389: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let every_Fn_vs_SOME_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`every_Fn_vs_SOME [] <=> T`;
   `every_Fn_vs_SOME (x :: y :: xs) <=>
         every_Fn_vs_SOME [x] /\
         every_Fn_vs_SOME (y :: xs)`;
   `every_Fn_vs_SOME [(Var _80 v:closLang_exp)] <=> T`;
   `every_Fn_vs_SOME [(If _82 x1 x2 x3:closLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME [x2] /\
         every_Fn_vs_SOME [x3]`;
   `every_Fn_vs_SOME [(Let _84 xs x2:closLang_exp)] <=>
         every_Fn_vs_SOME [x2] /\
         every_Fn_vs_SOME xs`;
   `every_Fn_vs_SOME [(Raise _86 x1:closLang_exp)] <=>
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(closLang_Tick _88 x1:closLang_exp)] <=>
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(closLang_Op _90 op xs:closLang_exp)] <=>
         every_Fn_vs_SOME xs`;
   `every_Fn_vs_SOME [(App _92 loc_opt x1 x2:closLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME x2`;
   `every_Fn_vs_SOME [closLang_Fn _93 loc vs_opt num_args x1] <=>
         IS_SOME vs_opt /\
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(Letrec _95 loc vs_opt fns x1:closLang_exp)] <=>
         IS_SOME vs_opt /\
         every_Fn_vs_SOME (MAP SND fns) /\
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(Handle _97 x1 x2:closLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME [x2]`;
   `every_Fn_vs_SOME [(closLang_Call _99 ticks dest xs:closLang_exp)]
  <=>
         every_Fn_vs_SOME xs`];;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:446-450: the tactic that proves the
   termination *)
let no_mti_def = cake_define_list_try (fun () ->
  `MEASURE closLang_exp_size`)
  [`no_mti (Var t n:closLang_exp) = T`;
   `no_mti (If t e1 e2 e3:closLang_exp) <=>
        no_mti e1 /\
        no_mti e2 /\
        no_mti e3`;
   `no_mti (Let t es e:closLang_exp) <=>
        EVERY no_mti es /\
        no_mti e`;
   `no_mti (Raise t e:closLang_exp) <=>
        no_mti e`;
   `no_mti (Handle t e1 e2:closLang_exp) <=>
        no_mti e1 /\
        no_mti e2`;
   `no_mti (closLang_Tick t e:closLang_exp) <=>
        no_mti e`;
   `no_mti (closLang_Call t ticks n es:closLang_exp) = F`;
   `no_mti (App t opt e es:closLang_exp) <=>
        LENGTH es = 1 /\ opt = NONE /\
        EVERY no_mti es /\
        no_mti e`;
   `no_mti (closLang_Fn t opt1 opt2 num_args e) <=>
        num_args = 1 /\ opt1 = NONE /\ opt2 = NONE /\
        no_mti e`;
   `no_mti (Letrec t opt1 opt2 funs e:closLang_exp) <=>
        no_mti e /\ opt1 = NONE /\ opt2 = NONE /\
        EVERY (\x. FST x = 1 /\ no_mti (SND x)) funs`;
   `no_mti (closLang_Op t op es) <=>
        EVERY no_mti es`];;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:473-476: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let fv_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
  [`fv n [] <=> F`;
   `fv n ((x:closLang_exp) :: y :: xs) <=>
         fv n [x] \/ fv n (y :: xs)`;
   `fv n [(Var _101 v:closLang_exp)] <=> (n = v)`;
   `fv n [(If _103 x1 x2 x3:closLang_exp)] <=>
         fv n [x1] \/ fv n [x2] \/ fv n [x3]`;
   `fv n [(Let _105 xs x2:closLang_exp)] <=>
         fv n xs \/ fv (n + LENGTH xs) [x2]`;
   `fv n [(Raise _107 x1:closLang_exp)] <=> fv n [x1]`;
   `fv n [(closLang_Tick _109 x1:closLang_exp)] <=> fv n [x1]`;
   `fv n [(closLang_Op _111 op xs:closLang_exp)] <=> fv n xs`;
   `fv n [(App _113 loc_opt x1 x2:closLang_exp)] <=>
         fv n [x1] \/ fv n x2`;
   `fv n [closLang_Fn _114 loc vs num_args x1] <=>
         fv (n + num_args) [x1]`;
   `fv n [(Letrec _116 loc vs fns x1:closLang_exp)] <=>
         EXISTS (\(num_args,x). fv (n + num_args + LENGTH fns)
           [x]) fns \/ fv (n + LENGTH fns) [x1]`;
   `fv n [(Handle _118 x1 x2:closLang_exp)] <=>
         fv n [x1] \/ fv (n + 1) [x2]`;
   `fv n [(closLang_Call _120 ticks dest xs:closLang_exp)] <=> fv n
  xs`];;

let fv1_def = cake_define
  `fv1 v e = fv v [e]`;;

(* HOL4 closPropsScript.sml:590-597: ML code, not ported *)

(* HOL4 closPropsScript.sml:599-604: a proof *)

(* HOL4 closPropsScript.sml:679-686: ML code, not ported *)

(* HOL4 closPropsScript.sml:698-708: a proof *)

(* HOL4 closPropsScript.sml:728-745: ML code, not ported *)

(* HOL4 closPropsScript.sml:747-823: a proof *)

(* HOL4 closPropsScript.sml:931-934: a proof *)

let is_closure_def = cake_define
  `is_closure x1 =
        match x1 with
          (Closure _126 _127 _128 _129 _130:closSem_v) -> T
        | (Recclosure _131 _132 _133 _134 _135) -> T
        | _136 -> F`;;

let clo_to_loc_def = cake_define_list
  [`clo_to_loc (Closure l _141 _142 _143 _144:closSem_v) = l`;
   `clo_to_loc (Recclosure l _148 _149 _150 i:closSem_v) =
  OPTION_MAP ((+) (2 * i)) l`];;

let clo_to_env_def = cake_define_list
  [`clo_to_env (Closure _155 _156 env _157 _158:closSem_v) = env`;
   `clo_to_env (Recclosure loc _161 env fns _162:closSem_v) =
       GENLIST (Recclosure loc [] env fns) (LENGTH fns) ++ env`];;

let clo_to_partial_args_def = cake_define_list
  [`clo_to_partial_args (Closure _167 args _168 _169 _170:closSem_v)
  = args`;
   `clo_to_partial_args (Recclosure _175 args _176 _177
  _178:closSem_v) = args`];;

let clo_add_partial_args_def = cake_define_list
  [`clo_add_partial_args args (Closure x1 args' x2 x3 x4:closSem_v) =
       Closure x1 (args ++ args') x2 x3 x4`;
   `clo_add_partial_args args (Recclosure x1 args' x2 x3 x4:closSem_v) =
       Recclosure x1 (args ++ args') x2 x3 x4`];;

let clo_to_num_params_def = cake_define_list
  [`clo_to_num_params (Closure _183 _184 _185 n _186:closSem_v) = n`;
   `clo_to_num_params (Recclosure _190 _191 _192 fns i:closSem_v) =
  FST (EL i fns)`];;

let rec_clo_ok_def = cake_define_list
  [`rec_clo_ok (Recclosure _196 _197 _198 fns i:closSem_v) <=> i <
  LENGTH fns`;
   `rec_clo_ok (Closure _204 _205 _206 _207 _208:closSem_v) <=> T`];;

let clo_can_apply_def = cake_define
  `clo_can_apply loc cl num_args <=>
     LENGTH (clo_to_partial_args cl) < clo_to_num_params cl /\
     rec_clo_ok cl /\
     (~(loc = NONE) ==>
      loc = clo_to_loc cl /\
      num_args = clo_to_num_params cl /\
      clo_to_partial_args cl = [])`;;

let check_closures_def = cake_define
  `check_closures cl cl' <=>
     (!loc num_args.
       clo_can_apply loc cl num_args ==> clo_can_apply loc cl'
         num_args)`;;

(* HOL4 closPropsScript.sml:1512-1516: ML code, not ported *)

(* HOL4 closPropsScript.sml:1565: the ML values that the definitions
   below antiquote *)
(* HOL4 closPropsScript.sml:1669-1671: the ML values that the
   definitions below antiquote *)

(* HOL4 closPropsScript.sml:1673-1685: a proof *)

(* HOL4 closPropsScript.sml:1737: ML code, not ported *)

(* finding the SetGlobal operations *)
let op_gbag_def = cake_define
  `closProps_op_gbag x1 =
      match x1 with
        closLang_GlobOp (closLang_SetGlobal n) -> BAG_INSERT n
          EMPTY_BAG
      | _209 -> EMPTY_BAG`;;
hol4_overload "op_gbag" "closProps_op_gbag";;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:1783-1786: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let set_globals_def = cake_define_list_try_tac (fun () ->
  `MEASURE (sum_size closLang_exp_size (list_size closLang_exp_size))`)
  CHEAT_TAC
  [`closProps_set_globals (Var _212 _213:closLang_exp) = EMPTY_BAG`;
   `closProps_set_globals (If _215 e1 e2 e3:closLang_exp) = (BAG_UNION)
  ((BAG_UNION)
        (closProps_set_globals e1) (closProps_set_globals e2))
          (closProps_set_globals e3)`;
   `closProps_set_globals (Let _217 binds e:closLang_exp) =
  (BAG_UNION) (closProps_set_globals e) (closProps_elist_globals
  binds)`;
   `closProps_set_globals (Raise _219 e:closLang_exp) =
  closProps_set_globals e`;
   `closProps_set_globals (Handle _221 e1 e2:closLang_exp) =
  (BAG_UNION) (closProps_set_globals e1) (closProps_set_globals e2)`;
   `closProps_set_globals (closLang_Tick _223 e:closLang_exp) =
  closProps_set_globals e`;
   `closProps_set_globals (closLang_Call _227 _228 _229
  args:closLang_exp) = closProps_elist_globals args`;
   `closProps_set_globals (App _232 _233 f args:closLang_exp) =
  (BAG_UNION) (closProps_set_globals f) (closProps_elist_globals
  args)`;
   `closProps_set_globals (closLang_Fn _234 _235 _236 _237 bod) =
  closProps_set_globals bod`;
   `closProps_set_globals (Letrec _241 _242 _243 fbinds
  bod:closLang_exp) = (BAG_UNION)
        (closProps_set_globals bod) (closProps_elist_globals (MAP
          SND fbinds))`;
   `closProps_set_globals (closLang_Op _245 opn args:closLang_exp) =
  (BAG_UNION) (closProps_op_gbag opn) (closProps_elist_globals args)`;
   `closProps_elist_globals [] = EMPTY_BAG`;
   `closProps_elist_globals (e :: es) = (BAG_UNION)
  (closProps_set_globals e) (closProps_elist_globals es)`];;
hol4_overload "elist_globals" "closProps_elist_globals";;
hol4_overload "set_globals" "closProps_set_globals";;

(* {foo}sgc_free: foo is free of SetGlobal closures, meaning closures
   that
   include calls to SetGlobal, for
     foo = {(e)xpr, (v)alue, (r)esult, and (s)tate}
*)

(* value is setglobal-closure free *)
let _ = size_thms "closSem_v";;
(* HOL4 closPropsScript.sml:1809-1812: the tactic that proves the
   termination *)
let vsgc_free_def = cake_define_wf
  `MEASURE closSem_v_size`
  `vsgc_free x1 =
        match x1 with
          (Closure _248 VL1 VL2 _249 body:closSem_v) ->
        closProps_set_globals body = EMPTY_BAG /\
        EVERY vsgc_free VL1 /\ EVERY vsgc_free VL2
        | (Recclosure _250 VL1 VL2 bods _251) ->
        closProps_elist_globals (MAP SND bods) = EMPTY_BAG /\
        EVERY vsgc_free VL1 /\ EVERY vsgc_free VL2
        | (closSem_Block _252 VL) -> EVERY vsgc_free VL
        | _253 -> T`;;

(* result is setglobal-closure free *)
let rsgc_free_def = cake_define
  `rsgc_free x1 =
        match x1 with
          Rval vs -> EVERY vsgc_free vs
        | (Rerr (Rabort _254)) -> T
        | (Rerr (Rraise v)) -> vsgc_free v`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:1849-1852: the tactic that proves the
   termination *)
let esgc_free_def = cake_define_list_try (fun () ->
  `MEASURE closLang_exp_size`)
  [`closProps_esgc_free (Var _257 _258:closLang_exp) <=> T`;
   `closProps_esgc_free (If _260 e1 e2 e3:closLang_exp) <=>
  closProps_esgc_free e1 /\ closProps_esgc_free e2 /\
  closProps_esgc_free e3`;
   `closProps_esgc_free (Let _262 binds e:closLang_exp) <=> EVERY
  closProps_esgc_free binds /\ closProps_esgc_free e`;
   `closProps_esgc_free (Raise _264 e:closLang_exp) <=>
  closProps_esgc_free e`;
   `closProps_esgc_free (Handle _266 e1 e2:closLang_exp) <=>
  closProps_esgc_free e1 /\ closProps_esgc_free e2`;
   `closProps_esgc_free (closLang_Tick _268 e:closLang_exp) <=>
  closProps_esgc_free e`;
   `closProps_esgc_free (closLang_Call _272 _273 _274
  args:closLang_exp) <=> EVERY closProps_esgc_free args`;
   `closProps_esgc_free (App _277 _278 e args:closLang_exp) <=>
  closProps_esgc_free e /\ EVERY closProps_esgc_free args`;
   `closProps_esgc_free (closLang_Fn _279 _280 _281 _282 b) <=>
  closProps_set_globals b = EMPTY_BAG`;
   `closProps_esgc_free (Letrec _286 _287 _288 binds bod:closLang_exp)
  <=>
        closProps_elist_globals (MAP SND binds) = EMPTY_BAG /\
          closProps_esgc_free bod`;
   `closProps_esgc_free (closLang_Op _291 _292 args:closLang_exp)
  <=> EVERY closProps_esgc_free args`];;
hol4_overload "esgc_free" "closProps_esgc_free";;

(* state is setglobal-closure free *)
let ssgc_free_def = cake_define
  `ssgc_free (s:('c,'ffi)closSem_state) <=>
     (!n m e. FLOOKUP (closSem_state_code s) n = SOME (m,e) ==>
       closProps_set_globals e = EMPTY_BAG) /\
     (!n vl. FLOOKUP (state_refs s) n = SOME (closSem_ValueArray vl)
       ==> EVERY vsgc_free vl) /\
     (!n m v. FLOOKUP (state_refs s) n = SOME (Thunk m v) ==>
       vsgc_free v) /\
     (!v. MEM (SOME v) (closSem_state_globals s) ==> vsgc_free v) /\
     (!n exp aux. SND (closSem_state_compile_oracle s n) = (exp,aux)
       ==> EVERY closProps_esgc_free exp /\
          closProps_elist_globals (MAP (SND o SND) aux) =
            EMPTY_BAG)`;;

(* generic do_app compile proof *)

let isClos_def = cake_define
  `closProps_isClos x1 =
      match x1 with
        (Closure x1 x2 x3 x4 x5:closSem_v) -> T
      | (Recclosure y1 y2 y3 y4 y5) -> T
      | _293 -> F`;;
hol4_overload "isClos" "closProps_isClos";;

let simple_val_rel_def = cake_define
  `closProps_simple_val_rel vr <=>
    (!x n. vr x (closSem_Number n) <=> x = closSem_Number n) /\
    (!x p n.
       vr x (closSem_Block n p) <=>
       (?xs. x = closSem_Block n xs /\ LIST_REL vr xs p)) /\
    (!x p. vr x (Word64 p) <=> x = Word64 p) /\
    (!x p. vr x (closSem_ByteVector p) <=> x = closSem_ByteVector p)
      /\
    (!x p b. vr x (closSem_RefPtr b p) <=> x = closSem_RefPtr b p) /\
    (!x5 x4 x3 x2 x1 x.
       vr x (Closure x1 x2 x3 x4 x5) ==> closProps_isClos x) /\
    (!y5 y4 y3 y2 y1 x.
       vr x (Recclosure y1 y2 y3 y4 y5) ==> closProps_isClos x)`;;
hol4_overload "simple_val_rel" "closProps_simple_val_rel";;

let simple_state_rel_def = cake_define
  `closProps_simple_state_rel vr sr <=>
     (!s t ptr. FLOOKUP (state_refs t) ptr = NONE /\ sr s t ==>
                FLOOKUP (state_refs s) ptr = NONE) /\
     (!w t s ptr.
       FLOOKUP (state_refs t) ptr = SOME (closSem_ByteArray w) /\ sr
         s t ==>
       FLOOKUP (state_refs s) ptr = SOME (closSem_ByteArray w)) /\
     (!w (t:('c,'ffi)closSem_state) (s:('d,'ffi)closSem_state) ptr.
       FLOOKUP (state_refs t) ptr = SOME (closSem_ValueArray w) /\ sr
         s t ==>
       (?w1.
         FLOOKUP (state_refs s) ptr = SOME (closSem_ValueArray w1) /\
         LIST_REL vr w1 w)) /\
     (!m v t s ptr.
       FLOOKUP (state_refs t) ptr = SOME (Thunk m v) /\ sr s t ==>
       (?w.
         FLOOKUP (state_refs s) ptr = SOME (Thunk m w) /\
         vr w v)) /\
     (!s t. sr s t ==> state_ffi s = state_ffi t /\ FDOM (state_refs
       s) = FDOM (state_refs t) /\
                       LIST_REL (OPTREL vr) (closSem_state_globals s)
                         (closSem_state_globals t)) /\
     (!f s t.
       sr s t ==> sr (state_ffi_fupd (K f) s)
                     (state_ffi_fupd (K f) t)) /\
     (!bs s t p.
       sr s t ==> sr (state_refs_fupd (K (state_refs s |+
         (p,closSem_ByteArray bs))) s)
                     (state_refs_fupd (K (state_refs t |+
                       (p,closSem_ByteArray bs))) t)) /\
     (!s t p xs ys.
       sr s t /\ LIST_REL vr xs ys ==>
       sr (state_refs_fupd (K (state_refs s |+ (p,closSem_ValueArray
         xs))) s)
          (state_refs_fupd (K (state_refs t |+ (p,closSem_ValueArray
            ys))) t)) /\
     (!s t p m v w.
       sr s t /\ vr v w ==>
       sr (state_refs_fupd (K (state_refs s |+ (p,Thunk m v))) s)
          (state_refs_fupd (K (state_refs t |+ (p,Thunk m w))) t)) /\
     (!s t xs ys.
       sr s t /\ LIST_REL (OPTREL vr) xs ys ==>
       sr (closSem_state_globals_fupd (K xs) s)
         (closSem_state_globals_fupd (K ys) t))`;;
hol4_overload "simple_state_rel" "closProps_simple_state_rel";;

(*TODO move to semanticPrimitivesProps*)

(*TODO upstream to HOL*)

(*TODO remove once its in Typebase and automatically
 simp*)
(* HOL4 closPropsScript.sml:2294-2296: ML code, not ported *)

(* HOL4 closPropsScript.sml:2325: ML code, not ported *)

(* generic do_install compile proof *)
let simple_compile_state_rel_def = cake_define
  `simple_compile_state_rel vr sr comp' cr <=>
     closProps_simple_state_rel vr sr /\
     (!(s:('c,'ffi)closSem_state) (t:('c,'ffi)closSem_state).
         sr s t ==> state_clock
         t = state_clock s /\ closSem_state_compile s = pure_cc comp'
           (closSem_state_compile t) /\ closSem_state_compile_oracle
         t = pure_co comp' o closSem_state_compile_oracle s /\
         (!n exps res p aux. SND (closSem_state_compile_oracle s n) =
           (p,aux) ==>
             comp' (p,aux) = (exps,res) ==>
             res = [] /\ LENGTH exps = LENGTH p /\ cr p exps) /\
         (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
         (!n. sr (closSem_state_code_fupd (K (closSem_state_code s))
           (closSem_state_compile_oracle_fupd (K
                         (misc_shift_seq 1
                           (closSem_state_compile_oracle s)))
                           (state_clock_fupd (K n) s)))
              (closSem_state_code_fupd (K (closSem_state_code t))
                (closSem_state_compile_oracle_fupd (K
                         (misc_shift_seq 1
                           (closSem_state_compile_oracle t)))
                           (state_clock_fupd (K n) t)))))`;;

(* HOL4 closPropsScript.sml:2726: ML code, not ported *)

(* HOL4 closPropsScript.sml:2728: ML code, not ported *)
  (* CASE_TAC restricted to a particular type. Works in the proof below,
     but needs more code from BasicProvers to be robust. *)
(* HOL4 closPropsScript.sml:2731-2736: a proof *)

(* after do_install evaluate uses the LAST element, and this helps *)
(* FIXME move *)

(* a generic semantics preservation lemma *)

let eval_sim_def = cake_define
  `closProps_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2
  rel allow_fail =
     (!k res1 s2.
       closSem_evaluate (es1,[],closSem_initial_state ffi max_app
         code1 co1 cc1 k) = (res1,s2) /\
       (allow_fail \/ ~(res1 = Rerr (Rabort Rtype_error))) /\
       rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
       (?ck res2 t2.
         closSem_evaluate (es2,[],
           closSem_initial_state ffi max_app code2 co2 cc2 (k + ck))
             = (res2,t2) /\
         semanticPrimitivesProps_result_rel (\x y. T) (\x y. T)
           res1 res2 /\ state_ffi s2 = state_ffi t2))`;;
hol4_overload "eval_sim" "closProps_eval_sim";;

(* HOL4 closPropsScript.sml:2800-2804: ML code, not ported *)

let adj_orac_rel_def = cake_define
  `closProps_adj_orac_rel cc f s1 s2 <=>
      (!n x y. closSem_state_compile_oracle s1 n = (x,y) ==>
         OPTION_MAP (I ## (I ## f)) (closSem_state_compile s1 x y) =
           cc (f x) y) /\
      s2 = mk_closSem_state (closSem_state_globals s1) (state_refs
        s1) (state_ffi s1) (state_clock s1) cc ((f ## I) o
        closSem_state_compile_oracle s1) (closSem_state_code s1)
        (closSem_state_max_app s1)`;;
hol4_overload "adj_orac_rel" "closProps_adj_orac_rel";;

(* HOL4 closPropsScript.sml:3178-3184: ML code, not ported *)

let SUBMAP_rel_def = cake_define
  `SUBMAP_rel z1 z2 <=>
     z2 = closSem_state_code_fupd (K (closSem_state_code z2)) z1 /\
       closSem_state_code z1 SUBMAP closSem_state_code z2 /\
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<)
         (FDOM (closSem_state_code z2))
           (closSem_state_compile_oracle z1)`;;

(* HOL4 closPropsScript.sml:3396-3402: ML code, not ported *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3554-3560: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let obeys_max_app_def = cake_define_list_try_tac (fun () ->
  `MEASURE (closLang_exp_size o SND)`)
  CHEAT_TAC
  [`obeys_max_app m (Var _296 _297:closLang_exp) <=> T`;
   `obeys_max_app m (If _299 e1 e2 e3:closLang_exp) <=> obeys_max_app
  m e1 /\ obeys_max_app m e2 /\ obeys_max_app m e3`;
   `obeys_max_app m (Let _301 es e:closLang_exp) <=> EVERY
  (obeys_max_app m) es /\ obeys_max_app m e`;
   `obeys_max_app m (Raise _303 e:closLang_exp) <=> obeys_max_app m e`;
   `obeys_max_app m (Handle _305 e1 e2:closLang_exp) <=>
  obeys_max_app m e1 /\ obeys_max_app m e2`;
   `obeys_max_app m (closLang_Tick _307 e:closLang_exp) <=>
  obeys_max_app m e`;
   `obeys_max_app m (closLang_Call _311 _312 _313 es:closLang_exp)
  <=> EVERY (obeys_max_app m) es`;
   `obeys_max_app m (App _316 _317 e es:closLang_exp) <=> LENGTH es
  <= m /\ obeys_max_app m e /\ EVERY (obeys_max_app m) es`;
   `obeys_max_app m (closLang_Fn _318 _319 _320 _321 e) <=>
  obeys_max_app m e`;
   `obeys_max_app m (Letrec _325 _326 _327 es e:closLang_exp) <=>
  EVERY (obeys_max_app m) (MAP SND es) /\ obeys_max_app m e`;
   `obeys_max_app m (closLang_Op _330 _331 es:closLang_exp) <=>
  EVERY (obeys_max_app m) es`];;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3578-3584: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let no_Labels_def = cake_define_list_try_tac (fun () ->
  `MEASURE closLang_exp_size`)
  CHEAT_TAC
  [`no_Labels (Var _334 _335:closLang_exp) <=> T`;
   `no_Labels (If _337 e1 e2 e3:closLang_exp) <=> no_Labels e1 /\
  no_Labels e2 /\ no_Labels e3`;
   `no_Labels (Let _339 es e:closLang_exp) <=> EVERY no_Labels es /\
  no_Labels e`;
   `no_Labels (Raise _341 e:closLang_exp) <=> no_Labels e`;
   `no_Labels (Handle _343 e1 e2:closLang_exp) <=> no_Labels e1 /\
  no_Labels e2`;
   `no_Labels (closLang_Tick _345 e:closLang_exp) <=> no_Labels e`;
   `no_Labels (closLang_Call _349 _350 _351 es:closLang_exp) <=>
  EVERY no_Labels es`;
   `no_Labels (App _354 _355 e es:closLang_exp) <=> no_Labels e /\
  EVERY no_Labels es`;
   `no_Labels (closLang_Fn _356 _357 _358 _359 e) <=> no_Labels e`;
   `no_Labels (Letrec _363 _364 _365 es e:closLang_exp) <=> EVERY
  no_Labels (MAP SND es) /\ no_Labels e`;
   `no_Labels (closLang_Op _367 op es:closLang_exp) <=> (!n. ~(op =
  closLang_Label n)) /\ EVERY no_Labels es`];;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3631-3634: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let app_call_dests_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
  [`app_call_dests opt [] = {}`;
   `app_call_dests opt (x :: y :: xs) =
         (let c1 = app_call_dests opt [x] in
         let c2 = app_call_dests opt (y :: xs) in
           c1 UNION c2)`;
   `app_call_dests opt [(Var _369 v:closLang_exp)] = {}`;
   `app_call_dests opt [(If _371 x1 x2 x3:closLang_exp)] =
         (let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt [x2] in
         let c3 = app_call_dests opt [x3] in
           c1 UNION c2 UNION c3)`;
   `app_call_dests opt [(Let _373 xs x2:closLang_exp)] =
         (let c1 = app_call_dests opt xs in
         let c2 = app_call_dests opt [x2] in
           c1 UNION c2)`;
   `app_call_dests opt [(Raise _375 x1:closLang_exp)] =
         app_call_dests opt [x1]`;
   `app_call_dests opt [(closLang_Tick _377 x1:closLang_exp)] =
         app_call_dests opt [x1]`;
   `app_call_dests opt [(closLang_Op _379 op xs:closLang_exp)] =
         app_call_dests opt xs`;
   `app_call_dests opt [(App _383 loc_opt x1 xs:closLang_exp)] =
         (let ll = (if opt = SOME T then {} else
                    match loc_opt with SOME n -> {n} | _384 -> {})
                      in
         let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt xs in
             ll UNION c1 UNION c2)`;
   `app_call_dests opt [closLang_Fn _385 loc_opt vs num_args x1] =
         (let c1 = app_call_dests opt [x1] in c1)`;
   `app_call_dests opt [(Letrec _387 loc_opt vs fns x1:closLang_exp)] =
         (let c1 = app_call_dests opt (MAP SND fns) in
         let c2 = app_call_dests opt [x1] in
         c1 UNION c2)`;
   `app_call_dests opt [(Handle _389 x1 x2:closLang_exp)] =
         (let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt [x2] in
           c1 UNION c2)`;
   `app_call_dests opt [(closLang_Call _391 ticks dest xs:closLang_exp)]
  =
         (if opt = SOME F then app_call_dests opt xs else
           dest INSERT app_call_dests opt xs)`];;

(* HOL4 closPropsScript.sml:3639: the overload call_dests, which the
   port expands *)
(* HOL4 closPropsScript.sml:3640: the overload app_dests, which the
   port expands *)
(* HOL4 closPropsScript.sml:3641: the overload any_dests, which the
   port expands *)

(* HOL4 closPropsScript.sml:3643: ML code, not ported *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3725-3731: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let get_code_labels_def = cake_define_list_try_tac (fun () ->
  `MEASURE closLang_exp_size`)
  CHEAT_TAC
  [`closProps_get_code_labels (Var _394 _395:closLang_exp) = {}`;
   `closProps_get_code_labels (If _397 e1 e2 e3:closLang_exp) =
        closProps_get_code_labels e1 UNION
        closProps_get_code_labels e2 UNION
        closProps_get_code_labels e3`;
   `closProps_get_code_labels (Let _399 es e:closLang_exp) =
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))
          UNION
        closProps_get_code_labels e`;
   `closProps_get_code_labels (Raise _401 e:closLang_exp) =
  closProps_get_code_labels e`;
   `closProps_get_code_labels (Handle _403 e1 e2:closLang_exp) =
        closProps_get_code_labels e1 UNION
        closProps_get_code_labels e2`;
   `closProps_get_code_labels (closLang_Tick _405 e:closLang_exp) =
  closProps_get_code_labels e`;
   `closProps_get_code_labels (closLang_Call _408 _409 l
  es:closLang_exp) =
        {l} UNION BIGUNION (set_of_list (MAP
          closProps_get_code_labels es))`;
   `closProps_get_code_labels (App _411 l e es:closLang_exp) =
        (match l with NONE -> {} | SOME n -> {n}) UNION
        closProps_get_code_labels e UNION
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))`;
   `closProps_get_code_labels (closLang_Fn _412 l _413 _414 e) =
       (match l with NONE -> {} | SOME n -> {n}) UNION
       closProps_get_code_labels e`;
   `closProps_get_code_labels (Letrec _417 l _418 es e:closLang_exp) =
       (match l with NONE -> {} | SOME n ->
         IMAGE (\k. n + 2 * k) (count (LENGTH es))) UNION
        closProps_get_code_labels e UNION
        BIGUNION (set_of_list (MAP closProps_get_code_labels (MAP
          SND es)))`;
   `closProps_get_code_labels (closLang_Op _420 op es:closLang_exp) =
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))
          UNION
        assign_get_code_label op`];;
hol4_overload "get_code_labels" "closProps_get_code_labels";;

(* HOL4 closPropsScript.sml:3737: ML code, not ported *)
