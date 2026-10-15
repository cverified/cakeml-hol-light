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
needs "semantics/proofs/semanticPrimitivesProps.ml";;
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

let code_locs_def = cake_define_list
  [`code_locs [] = []`;
   `code_locs (x :: y :: xs) =
         (let c1 = code_locs [x] in
         let c2 = code_locs (y :: xs) in
           c1 ++ c2)`;
   `code_locs [(Var _4 v:flatLang_exp)] = []`;
   `code_locs [(If _6 x1 x2 x3:flatLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs [x2] in
         let c3 = code_locs [x3] in
           c1 ++ c2 ++ c3)`;
   `code_locs [(Let _8 xs x2:flatLang_exp)] =
         (let c1 = code_locs xs in
         let c2 = code_locs [x2] in
           c1 ++ c2)`;
   `code_locs [(Raise _10 x1:flatLang_exp)] =
         code_locs [x1]`;
   `code_locs [closLang_Tick _11 x1] =
         code_locs [x1]`;
   `code_locs [closLang_Op _12 op xs] =
         code_locs xs`;
   `code_locs [(App _14 loc_opt x1 xs:flatLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs xs in
             c1 ++ c2)`;
   `code_locs [closLang_Fn _15 loc_opt vs num_args x1] =
         (let loc = match loc_opt with NONE -> 0 | SOME n -> n in
         let c1 = code_locs [x1] in
           c1 ++ [loc])`;
   `code_locs [(Letrec _17 loc_opt vs fns x1:flatLang_exp)] =
         (let loc = match loc_opt with NONE -> 0 | SOME n -> n in
         let c1 = code_locs (MAP SND fns) in
         let c2 = code_locs [x1] in
         c1 ++ GENLIST (\n. loc + 2 * n) (LENGTH fns) ++ c2)`;
   `code_locs [(Handle _19 x1 x2:flatLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs [x2] in
           c1 ++ c2)`;
   `code_locs [closLang_Call _20 ticks dest xs] =
         code_locs xs`];;

let _ = size_thms "flatLang_exp";;
let _ = size_thms "list";;
(* HOL4 termination: \\ gvs [list_size_pair_size_MAP_FST_SND] *)
let contains_App_SOME_def = cake_define_wf
  `MEASURE (list_size flatLang_exp_size o SND)`
  `contains_App_SOME max_app x2 =
        match x2 with
          [] -> F
        | (x :: y :: xs) ->
        contains_App_SOME max_app [x] \/
        contains_App_SOME max_app (y :: xs)
        | [Var _21 v] -> F
        | [If _22 x1 x2 x3] ->
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app [x2] \/
        contains_App_SOME max_app [x3]
        | [Let _23 xs x2] ->
        contains_App_SOME max_app [x2] \/
        contains_App_SOME max_app xs
        | [Raise _24 x1] ->
        contains_App_SOME max_app [x1]
        | [closLang_Tick _25 x1] ->
        contains_App_SOME max_app [x1]
        | [closLang_Op _26 (ThunkOp ForceThunk) xs] ->
        max_app < 1 \/
        contains_App_SOME max_app xs
        | [closLang_Op _27 op xs] ->
        contains_App_SOME max_app xs
        | [App _28 loc_opt x1 x2] ->
        IS_SOME loc_opt \/ max_app < LENGTH x2 \/
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app x2
        | [closLang_Fn _29 loc vs num_args x1] ->
        contains_App_SOME max_app [x1]
        | [Letrec _30 loc vs fns x1] ->
        contains_App_SOME max_app (MAP SND fns) \/
        contains_App_SOME max_app [x1]
        | [Handle _31 x1 x2] ->
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app [x2]
        | [closLang_Call _32 ticks dest xs] ->
        contains_App_SOME max_app xs`;;

let every_Fn_SOME_def = cake_define_list
  [`every_Fn_SOME [] <=> T`;
   `every_Fn_SOME (x :: y :: xs) <=>
         every_Fn_SOME [x] /\
         every_Fn_SOME (y :: xs)`;
   `every_Fn_SOME [(Var _34 v:flatLang_exp)] <=> T`;
   `every_Fn_SOME [(If _36 x1 x2 x3:flatLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME [x2] /\
         every_Fn_SOME [x3]`;
   `every_Fn_SOME [(Let _38 xs x2:flatLang_exp)] <=>
         every_Fn_SOME [x2] /\
         every_Fn_SOME xs`;
   `every_Fn_SOME [(Raise _40 x1:flatLang_exp)] <=>
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [closLang_Tick _41 x1] <=>
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [closLang_Op _42 op xs] <=>
         every_Fn_SOME xs`;
   `every_Fn_SOME [(App _44 loc_opt x1 x2:flatLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME x2`;
   `every_Fn_SOME [closLang_Fn _45 loc_opt vs num_args x1] <=>
         IS_SOME loc_opt /\
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(Letrec _47 loc_opt vs fns x1:flatLang_exp)] <=>
         IS_SOME loc_opt /\
         every_Fn_SOME (MAP SND fns) /\
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(Handle _49 x1 x2:flatLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME [x2]`;
   `every_Fn_SOME [closLang_Call _50 ticks dest xs] <=>
         every_Fn_SOME xs`];;

let every_Fn_vs_NONE_def = cake_define_list
  [`every_Fn_vs_NONE [] <=> T`;
   `every_Fn_vs_NONE (x :: y :: xs) <=>
         every_Fn_vs_NONE [x] /\
         every_Fn_vs_NONE (y :: xs)`;
   `every_Fn_vs_NONE [(Var _52 v:flatLang_exp)] <=> T`;
   `every_Fn_vs_NONE [(If _54 x1 x2 x3:flatLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE [x2] /\
         every_Fn_vs_NONE [x3]`;
   `every_Fn_vs_NONE [(Let _56 xs x2:flatLang_exp)] <=>
         every_Fn_vs_NONE [x2] /\
         every_Fn_vs_NONE xs`;
   `every_Fn_vs_NONE [(Raise _58 x1:flatLang_exp)] <=>
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [closLang_Tick _59 x1] <=>
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [closLang_Op _60 op xs] <=>
         every_Fn_vs_NONE xs`;
   `every_Fn_vs_NONE [(App _62 loc_opt x1 x2:flatLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE x2`;
   `every_Fn_vs_NONE [closLang_Fn _63 loc vs_opt num_args x1] <=>
         IS_NONE vs_opt /\
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(Letrec _65 loc vs_opt fns x1:flatLang_exp)] <=>
         IS_NONE vs_opt /\
         every_Fn_vs_NONE (MAP SND fns) /\
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(Handle _67 x1 x2:flatLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE [x2]`;
   `every_Fn_vs_NONE [closLang_Call _68 ticks dest xs] <=>
         every_Fn_vs_NONE xs`];;

let every_Fn_vs_SOME_def = cake_define_list
  [`every_Fn_vs_SOME [] <=> T`;
   `every_Fn_vs_SOME (x :: y :: xs) <=>
         every_Fn_vs_SOME [x] /\
         every_Fn_vs_SOME (y :: xs)`;
   `every_Fn_vs_SOME [(Var _70 v:flatLang_exp)] <=> T`;
   `every_Fn_vs_SOME [(If _72 x1 x2 x3:flatLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME [x2] /\
         every_Fn_vs_SOME [x3]`;
   `every_Fn_vs_SOME [(Let _74 xs x2:flatLang_exp)] <=>
         every_Fn_vs_SOME [x2] /\
         every_Fn_vs_SOME xs`;
   `every_Fn_vs_SOME [(Raise _76 x1:flatLang_exp)] <=>
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [closLang_Tick _77 x1] <=>
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [closLang_Op _78 op xs] <=>
         every_Fn_vs_SOME xs`;
   `every_Fn_vs_SOME [(App _80 loc_opt x1 x2:flatLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME x2`;
   `every_Fn_vs_SOME [closLang_Fn _81 loc vs_opt num_args x1] <=>
         IS_SOME vs_opt /\
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(Letrec _83 loc vs_opt fns x1:flatLang_exp)] <=>
         IS_SOME vs_opt /\
         every_Fn_vs_SOME (MAP SND fns) /\
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(Handle _85 x1 x2:flatLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME [x2]`;
   `every_Fn_vs_SOME [closLang_Call _86 ticks dest xs] <=>
         every_Fn_vs_SOME xs`];;

let no_mti_def = cake_define_list
  [`no_mti (Var t n:flatLang_exp) = T`;
   `no_mti (If t e1 e2 e3:flatLang_exp) <=>
        no_mti e1 /\
        no_mti e2 /\
        no_mti e3`;
   `no_mti (Let t es e:flatLang_exp) <=>
        EVERY no_mti es /\
        no_mti e`;
   `no_mti (Raise t e:flatLang_exp) <=>
        no_mti e`;
   `no_mti (Handle t e1 e2:flatLang_exp) <=>
        no_mti e1 /\
        no_mti e2`;
   `no_mti (closLang_Tick t e) <=>
        no_mti e`;
   `no_mti (closLang_Call t ticks n es) = F`;
   `no_mti (App t opt e es:flatLang_exp) <=>
        LENGTH es = 1 /\ opt = NONE /\
        EVERY no_mti es /\
        no_mti e`;
   `no_mti (closLang_Fn t opt1 opt2 num_args e) <=>
        num_args = 1 /\ opt1 = NONE /\ opt2 = NONE /\
        no_mti e`;
   `no_mti (Letrec t opt1 opt2 funs e:flatLang_exp) <=>
        no_mti e /\ opt1 = NONE /\ opt2 = NONE /\
        EVERY (\x. FST x = 1 /\ no_mti (SND x)) funs`;
   `no_mti (closLang_Op t op es) <=>
        EVERY no_mti es`];;

let fv_def = cake_define_list
  [`fv n [] <=> F`;
   `fv n ((x:closLang_exp) :: y :: xs) <=>
         fv n [x] \/ fv n (y :: xs)`;
   `fv n [(Var _88 v:flatLang_exp)] <=> (n = v)`;
   `fv n [(If _90 x1 x2 x3:flatLang_exp)] <=>
         fv n [x1] \/ fv n [x2] \/ fv n [x3]`;
   `fv n [(Let _92 xs x2:flatLang_exp)] <=>
         fv n xs \/ fv (n + LENGTH xs) [x2]`;
   `fv n [(Raise _94 x1:flatLang_exp)] <=> fv n [x1]`;
   `fv n [closLang_Tick _95 x1] <=> fv n [x1]`;
   `fv n [closLang_Op _96 op xs] <=> fv n xs`;
   `fv n [(App _98 loc_opt x1 x2:flatLang_exp)] <=>
         fv n [x1] \/ fv n x2`;
   `fv n [closLang_Fn _99 loc vs num_args x1] <=>
         fv (n + num_args) [x1]`;
   `fv n [(Letrec _101 loc vs fns x1:flatLang_exp)] <=>
         EXISTS (\(num_args,x). fv (n + num_args + LENGTH fns)
           [x]) fns \/ fv (n + LENGTH fns) [x1]`;
   `fv n [(Handle _103 x1 x2:flatLang_exp)] <=>
         fv n [x1] \/ fv (n + 1) [x2]`;
   `fv n [closLang_Call _104 ticks dest xs] <=> fv n xs`];;

let fv1_def = cake_define
  `fv1 v e = fv v [e]`;;

(* HOL4 ML code, not ported:
val evaluate_LENGTH_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,s,env).
       (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH
         res)
            | _ => T)`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (Rval res,s1) => (LENGTH res =
         1)
            | _ => T)`;
*)

(* HOL4 ML code, not ported:
val evaluate_LENGTH = prove(evaluate_LENGTH_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_LENGTH_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\
    rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [FORALL_PROD];
*)

(* HOL4 ML code, not ported:
val evaluate_const_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,env,s).
       (case evaluate (xs,env,s) of (_,s1) =>
          (s1.max_app = s.max_app))`
  |> Q.SPEC `\x1 x2 x3 x4.
       (case evaluate_app x1 x2 x3 x4 of (_,s1) =>
          (s1.max_app = x4.max_app))`;
*)

(* HOL4 ML code, not ported:
val evaluate_const_lemma = prove(
  evaluate_const_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_const_ind
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ full_simp_tac(srw_ss())[LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\
    rev_full_simp_tac(srw_ss())[]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\
    rev_full_simp_tac(srw_ss())[]
  \\ IMP_RES_TAC do_app_const
  \\ IMP_RES_TAC do_install_const
  \\ full_simp_tac(srw_ss())[dec_clock_def])
  |> SIMP_RULE std_ss [FORALL_PROD]
*)

(* HOL4 ML code, not ported:
val evaluate_code_ind =
  evaluate_ind
  |> Q.SPEC `\(xs,env,s).
       (case evaluate (xs,env,s) of (_,s1) =>
          ∃n.
            s1.compile_oracle = shift_seq n s.compile_oracle ∧
            let ls = FLAT (MAP (SND o SND) (GENLIST s.compile_oracle n))
              in
            s1.code = s.code |++ ls ∧
            ALL_DISTINCT (MAP FST ls) ∧
            DISJOINT (FDOM s.code) (set(MAP FST ls)))`
  |> Q.SPEC `\x1 x2 x3 s.
       (case evaluate_app x1 x2 x3 s of (_,s1) =>
          ∃n.
            s1.compile_oracle = shift_seq n s.compile_oracle ∧
            let ls = FLAT (MAP (SND o SND) (GENLIST s.compile_oracle n))
              in
            s1.code = s.code |++ ls ∧
            ALL_DISTINCT (MAP FST ls) ∧
            DISJOINT (FDOM s.code) (set(MAP FST ls)))`;
*)

(* HOL4 ML code, not ported:
val evaluate_code_lemma = prove(
  evaluate_code_ind |> concl |> rand,
  MATCH_MP_TAC evaluate_code_ind \\ rw[]
  \\ ONCE_REWRITE_TAC [evaluate_def] \\ fs[] \\ rw []
  \\ every_case_tac \\ fs[] \\ rfs[shift_seq_def,FUN_EQ_THM]
  \\ fs[dec_clock_def]
  \\ TRY(qexists_tac`0` \\ simp[FUPDATE_LIST_THM] \\ NO_TAC)
  \\ TRY (
    qmatch_goalsub_rename_tac`(n1 + (n2 + (n3 + _)))` \\
    qexists_tac`n3+n2+n1` \\
    fs[GENLIST_APPEND,GSYM FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
    fsrw_tac[ETA_ss][GSYM FUN_EQ_THM] \\
    rfs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\
    metis_tac[])
  \\ TRY (
    qmatch_goalsub_rename_tac`(z1 + (z2 + _))` \\
    qexists_tac`z2+z1` \\
    fs[GENLIST_APPEND,GSYM FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
    fsrw_tac[ETA_ss][GSYM FUN_EQ_THM] \\
    rfs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\
    metis_tac[])
  \\ TRY (
    qmatch_goalsub_rename_tac`(z1 + (z2 + _))` \\
    qexists_tac`z1+z2` \\
    fs[GENLIST_APPEND,GSYM FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
    fsrw_tac[ETA_ss][GSYM FUN_EQ_THM] \\
    rfs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\
    metis_tac[])
  \\ TRY (
    qmatch_asmsub_rename_tac`_ = _ ((nn:num) + _)` \\
    qexists_tac`nn` \\
    imp_res_tac do_app_const \\
    fs[] \\ NO_TAC)
  \\ TRY
   (qmatch_asmsub_rename_tac`_ = _ ((z:num) + _)`
    \\ qmatch_asmsub_rename_tac`s.compile_oracle (y + _)`
    \\ gvs[do_install_def,case_eq_thms,pair_case_eq,UNCURRY,bool_case_eq
      ,shift_seq_def]
    \\ qexists_tac`1+y`
    \\ fs[GENLIST_APPEND,FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
      rfs[]
    \\ fs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\ rveq \\ fs[]
    \\ metis_tac[])
  \\ TRY
   (qmatch_asmsub_rename_tac`_ = _ ((z:num) + _)`
    \\ qmatch_asmsub_rename_tac`s.compile_oracle (y + _)`
    \\ gvs[do_install_def,case_eq_thms,pair_case_eq,UNCURRY,bool_case_eq
      ,shift_seq_def]
    \\ qexists_tac`z+1+y`
    \\ fs[GENLIST_APPEND,FUPDATE_LIST_APPEND,ALL_DISTINCT_APPEND] \\
      rfs[]
    \\ fs[IN_DISJOINT,FDOM_FUPDATE_LIST] \\ rveq \\ fs[]
    \\ metis_tac[])
  >-
   (fs [do_install_def]
    \\ fs [case_eq_thms, pair_case_eq, UNCURRY, bool_case_eq] \\ TRY
      (metis_tac [])
    \\ rw [] \\ fs [shift_seq_def]
    \\ qmatch_goalsub_rename_tac `nn + _`
    \\ qexists_tac `nn+1` \\ fs []
    \\ once_rewrite_tac [ADD_COMM]
    \\ fs [GENLIST_APPEND] \\ rfs []
    \\ last_x_assum (qspec_then `0` (assume_tac o GSYM)) \\ fs []
    \\ fs [FUPDATE_LIST_APPEND, ALL_DISTINCT_APPEND, IN_DISJOINT]
    \\ rfs []
    \\ fs [FDOM_FUPDATE_LIST]
    \\ metis_tac [])
  \\ qmatch_goalsub_rename_tac`(n1 + (n2 + (n3 + _)))`
  \\ qexists_tac `n1+n2+n3` \\ fs []
  \\ sg `GENLIST r.compile_oracle n1 = GENLIST (\x. s.compile_oracle (n2
    + x)) n1`
  >- fsrw_tac [ETA_ss] [GSYM FUN_EQ_THM]
  \\ fs []
  \\ rfs []
  \\ sg `GENLIST r'.compile_oracle n3 = GENLIST (\x. s.compile_oracle
    (n1 + (n2 + x))) n3`
  >- (fsrw_tac [ETA_ss] [GSYM FUN_EQ_THM] \\ fs [])
  \\ fs []
  \\ once_rewrite_tac [ADD_ASSOC]
  \\ once_rewrite_tac [ADD_COMM]
  \\ fs [GSYM FUPDATE_LIST_APPEND, GENLIST_APPEND, ALL_DISTINCT_APPEND,
         IN_DISJOINT, FDOM_FUPDATE_LIST]
  \\ metis_tac [])
  |> SIMP_RULE std_ss [FORALL_PROD];
*)

(* HOL4 ML code, not ported:
fun cases_on_op q = Cases_on q
  >>> SELECT_LT_THEN (Q.RENAME_TAC [‘BlockOp’]) (Cases_on `b`)
  >>> SELECT_LT_THEN (Q.RENAME_TAC [‘GlobOp’]) (Cases_on `g`)
  >>> SELECT_LT_THEN (Q.RENAME_TAC [‘MemOp’]) (Cases_on `m`);
*)

let is_closure_def = cake_define
  `is_closure x1 =
        match x1 with
          (Closure _110 _111 _112 _113 _114:closSem_v) -> T
        | (Recclosure _115 _116 _117 _118 _119) -> T
        | _120 -> F`;;

let clo_to_loc_def = cake_define_list
  [`clo_to_loc (Closure l _125 _126 _127 _128:closSem_v) = l`;
   `clo_to_loc (Recclosure l _132 _133 _134 i:closSem_v) =
  OPTION_MAP ((+) (2 * i)) l`];;

let clo_to_env_def = cake_define_list
  [`clo_to_env (Closure _139 _140 env _141 _142:closSem_v) = env`;
   `clo_to_env (Recclosure loc _145 env fns _146:closSem_v) =
       GENLIST (Recclosure loc [] env fns) (LENGTH fns) ++ env`];;

let clo_to_partial_args_def = cake_define_list
  [`clo_to_partial_args (Closure _151 args _152 _153 _154:closSem_v)
  = args`;
   `clo_to_partial_args (Recclosure _159 args _160 _161
  _162:closSem_v) = args`];;

let clo_add_partial_args_def = cake_define_list
  [`clo_add_partial_args args (Closure x1 args' x2 x3 x4:closSem_v) =
       Closure x1 (args ++ args') x2 x3 x4`;
   `clo_add_partial_args args (Recclosure x1 args' x2 x3 x4:closSem_v) =
       Recclosure x1 (args ++ args') x2 x3 x4`];;

let clo_to_num_params_def = cake_define_list
  [`clo_to_num_params (Closure _167 _168 _169 n _170:closSem_v) = n`;
   `clo_to_num_params (Recclosure _174 _175 _176 fns i:closSem_v) =
  FST (EL i fns)`];;

let rec_clo_ok_def = cake_define_list
  [`rec_clo_ok (Recclosure _180 _181 _182 fns i:closSem_v) <=> i <
  LENGTH fns`;
   `rec_clo_ok (Closure _188 _189 _190 _191 _192:closSem_v) <=> T`];;

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

(* HOL4 ML code, not ported:
val case_eq_thms =
  pair_case_eq::bool_case_eq::list_case_eq::option_case_eq::map
  TypeBase.case_eq_of
  [``:'a ffi_result``, ``:v``, ``:'a ref``, ``:closLang$op``,
    ``:closLang$mem_op``,
   ``:closLang$int_op``, ``:closLang$word_op``, ``:closLang$block_op``,
     ``:closLang$glob_op``,
   ``:word_size``, ``:eq_result``, ``:('a,'b) result``, ``:'a
     error_result``, ``:app_kind``]
  |> LIST_CONJ;
*)

(* HOL4 ML code, not ported:
val s = ``s:('c,'ffi) closSem$state``;
*)
(* HOL4 ML code, not ported:
val lemma = DECIDE``¬(x < y - z) ⇒ ((a:num) + x - (y - z) = x - (y - z)
  + a)``
val lemma2 = DECIDE``x ≠ 0n ⇒ a + (x - 1) = a + x - 1``
val lemma3 = DECIDE``¬(x:num < t+1) ⇒ a + (x - (t+1)) = a + x - (t+1)``
*)

(* HOL4 ML code, not ported:
val tac =
  imp_res_tac evaluate_add_to_clock >> rev_full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac evaluate_io_events_mono_imp >> full_simp_tac(srw_ss())[]
    >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[dec_clock_def] >>
    full_simp_tac(srw_ss())[do_app_add_to_clock] >>
  imp_res_tac do_install_add_to_clock >> fs[] >>
  TRY(first_assum(split_uncurry_arg_tac o rhs o concl) >>
    full_simp_tac(srw_ss())[]) >>
  imp_res_tac do_app_io_events_mono >>
  imp_res_tac do_install_const >>
  rveq >>
  fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_COMM] >>
  rveq >> fs[] >>
  gvs[AppUnit_def] >>
  metis_tac[evaluate_io_events_mono,with_clock_ffi,FST,SND
    ,IS_PREFIX_TRANS,lemma,Boolv_11,lemma2,lemma3]
*)

(* HOL4 ML code, not ported:
val _ = export_rewrites ["closLang.exp_size_def"]
*)

(* finding the SetGlobal operations *)
let op_gbag_def = cake_define
  `closProps_op_gbag x1 =
      match x1 with
        closLang_GlobOp (SetGlobal n) -> BAG_INSERT n EMPTY_BAG
      | _193 -> EMPTY_BAG`;;
hol4_overload "op_gbag" "closProps_op_gbag";;

let set_globals_def = cake_define_list
  [`closProps_set_globals (Var _196 _197:flatLang_exp) = EMPTY_BAG`;
   `closProps_set_globals (If _199 e1 e2 e3:flatLang_exp) = BAG_UNION
  (BAG_UNION
        (closProps_set_globals e1) (closProps_set_globals e2))
          (closProps_set_globals e3)`;
   `closProps_set_globals (Let _201 binds e:flatLang_exp) = BAG_UNION
  (closProps_set_globals e) (closProps_elist_globals binds)`;
   `closProps_set_globals (Raise _203 e:flatLang_exp) =
  closProps_set_globals e`;
   `closProps_set_globals (Handle _205 e1 e2:flatLang_exp) =
  BAG_UNION (closProps_set_globals e1) (closProps_set_globals e2)`;
   `closProps_set_globals (closLang_Tick _206 e) =
  closProps_set_globals e`;
   `closProps_set_globals (closLang_Call _207 _208 _209 args) =
  closProps_elist_globals args`;
   `closProps_set_globals (App _212 _213 f args:flatLang_exp) =
  BAG_UNION (closProps_set_globals f) (closProps_elist_globals args)`;
   `closProps_set_globals (closLang_Fn _214 _215 _216 _217 bod) =
  closProps_set_globals bod`;
   `closProps_set_globals (Letrec _221 _222 _223 fbinds
  bod:flatLang_exp) = BAG_UNION
        (closProps_set_globals bod) (closProps_elist_globals (MAP
          SND fbinds))`;
   `closProps_set_globals (closLang_Op _224 opn args) = BAG_UNION
  (closProps_op_gbag opn) (closProps_elist_globals args)`;
   `closProps_elist_globals [] = EMPTY_BAG`;
   `closProps_elist_globals (e :: es) = BAG_UNION
  (closProps_set_globals e) (closProps_elist_globals es)`];;
hol4_overload "elist_globals" "closProps_elist_globals";;
hol4_overload "set_globals" "closProps_set_globals";;

(* {foo}sgc_free: foo is free of SetGlobal closures, meaning closures
   that
   include calls to SetGlobal, for
     foo = {(e)xpr, (v)alue, (r)esult, and (s)tate}
*)

(* value is setglobal-closure free *)
(* HOL4 termination: >> simp[v_size_def] >> rpt strip_tac >>
   imp_res_tac v_size_lemma >> simp[] *)
let vsgc_free_def = cake_define_wf
  `MEASURE v_size`
  `vsgc_free x1 =
        match x1 with
          (Closure _227 VL1 VL2 _228 body:closSem_v) ->
        closProps_set_globals body = EMPTY_BAG /\
        EVERY vsgc_free VL1 /\ EVERY vsgc_free VL2
        | (Recclosure _229 VL1 VL2 bods _230) ->
        closProps_elist_globals (MAP SND bods) = EMPTY_BAG /\
        EVERY vsgc_free VL1 /\ EVERY vsgc_free VL2
        | (closSem_Block _231 VL) -> EVERY vsgc_free VL
        | _232 -> T`;;

(* result is setglobal-closure free *)
let rsgc_free_def = cake_define
  `rsgc_free x1 =
        match x1 with
          Rval vs -> EVERY vsgc_free vs
        | (Rerr (Rabort _233)) -> T
        | (Rerr (Rraise v)) -> vsgc_free v`;;

let esgc_free_def = cake_define_list
  [`closProps_esgc_free (Var _236 _237:flatLang_exp) <=> T`;
   `closProps_esgc_free (If _239 e1 e2 e3:flatLang_exp) <=>
  closProps_esgc_free e1 /\ closProps_esgc_free e2 /\
  closProps_esgc_free e3`;
   `closProps_esgc_free (Let _241 binds e:flatLang_exp) <=> EVERY
  closProps_esgc_free binds /\ closProps_esgc_free e`;
   `closProps_esgc_free (Raise _243 e:flatLang_exp) <=>
  closProps_esgc_free e`;
   `closProps_esgc_free (Handle _245 e1 e2:flatLang_exp) <=>
  closProps_esgc_free e1 /\ closProps_esgc_free e2`;
   `closProps_esgc_free (closLang_Tick _246 e) <=>
  closProps_esgc_free e`;
   `closProps_esgc_free (closLang_Call _247 _248 _249 args) <=> EVERY
  closProps_esgc_free args`;
   `closProps_esgc_free (App _252 _253 e args:flatLang_exp) <=>
  closProps_esgc_free e /\ EVERY closProps_esgc_free args`;
   `closProps_esgc_free (closLang_Fn _254 _255 _256 _257 b) <=>
  closProps_set_globals b = EMPTY_BAG`;
   `closProps_esgc_free (Letrec _261 _262 _263 binds bod:flatLang_exp)
  <=>
        closProps_elist_globals (MAP SND binds) = EMPTY_BAG /\
          closProps_esgc_free bod`;
   `closProps_esgc_free (closLang_Op _264 _265 args) <=> EVERY
  closProps_esgc_free args`];;
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
      | _266 -> F`;;
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
(* HOL4 ML code, not ported:
fun case_constant typ =
  prove_case_const_thm {case_def = TypeBase.case_def_of typ,
  nchotomy = TypeBase.nchotomy_of typ};
*)

(* HOL4 ML code, not ported:
val _ = print "The following proof is slow due to Rerr cases.\n";
*)

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

(* HOL4 ML code, not ported:
fun first_term f tm = f (find_term (can f) tm);
*)

(* HOL4 ML code, not ported:
fun TYPE_CASE_TAC nm (g as (_, tm)) =
*)
  (* CASE_TAC restricted to a particular type. Works in the proof below,
     but needs more code from BasicProvers to be robust. *)
(* HOL4 ML code, not ported:
  let
    val ERR = mk_HOL_ERR "TYPE_CASE_TAC"
    fun m (_, x, _) = if fst (dest_type (type_of x)) = nm
        then x else raise ERR "TYPE_CASE_TAC" "no match"
    val t = first_term (m o TypeBase.dest_case) tm
  in CHANGED_TAC (Cases_on `^t`) end g;
*)

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
         result_rel (\x y. T) (\x y. T) res1 res2 /\ state_ffi s2
           = state_ffi t2))`;;
hol4_overload "eval_sim" "closProps_eval_sim";;

(* HOL4 ML code, not ported:
val evaluate_add_to_clock_io_events_mono_alt =
  evaluate_add_to_clock_io_events_mono
  |> SIMP_RULE std_ss [] |> CONJUNCT1 |> SPEC_ALL
  |> DISCH ``evaluate (es,env,s) = (res,s1:('c,'ffi) closSem$state)``
  |> SIMP_RULE std_ss [] |> GEN_ALL;
*)

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

(* HOL4 ML code, not ported:
val do_app_lemma =
  simple_val_rel_do_app
  |> Q.GENL [`vr`,`sr`]
  |> ISPEC ``(=):closSem$v -> closSem$v -> bool``
  |> ISPEC ``adj_orac_rel cc f``
  |> Q.INST [`opp`|->`op`,`s`|->`s1`,`t`|->`s2`,`ys`|->`xs`]
  |> SIMP_RULE std_ss [do_app_lemma_simp]
*)

let SUBMAP_rel_def = cake_define
  `SUBMAP_rel z1 z2 <=>
     z2 = closSem_state_code_fupd (K (closSem_state_code z2 /\
       closSem_state_code z1 SUBMAP closSem_state_code z2 /\
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<)
         (FDOM (closSem_state_code z2))
           (closSem_state_compile_oracle z1))) z1`;;

(* HOL4 ML code, not ported:
val do_app_lemma =
  simple_val_rel_do_app
  |> Q.GENL [`vr`,`sr`]
  |> ISPEC ``(=):closSem$v -> closSem$v -> bool``
  |> ISPEC ``SUBMAP_rel``
  |> Q.INST [`opp`|->`op`,`s`|->`s1`,`t`|->`s2`,`ys`|->`xs`]
  |> SIMP_RULE std_ss [do_app_lemma_simp]
*)

let obeys_max_app_def = cake_define_list
  [`obeys_max_app m (Var _269 _270:flatLang_exp) <=> T`;
   `obeys_max_app m (If _272 e1 e2 e3:flatLang_exp) <=> obeys_max_app
  m e1 /\ obeys_max_app m e2 /\ obeys_max_app m e3`;
   `obeys_max_app m (Let _274 es e:flatLang_exp) <=> EVERY
  (obeys_max_app m) es /\ obeys_max_app m e`;
   `obeys_max_app m (Raise _276 e:flatLang_exp) <=> obeys_max_app m e`;
   `obeys_max_app m (Handle _278 e1 e2:flatLang_exp) <=>
  obeys_max_app m e1 /\ obeys_max_app m e2`;
   `obeys_max_app m (closLang_Tick _279 e) <=> obeys_max_app m e`;
   `obeys_max_app m (closLang_Call _280 _281 _282 es) <=> EVERY
  (obeys_max_app m) es`;
   `obeys_max_app m (App _285 _286 e es:flatLang_exp) <=> LENGTH es
  <= m /\ obeys_max_app m e /\ EVERY (obeys_max_app m) es`;
   `obeys_max_app m (closLang_Fn _287 _288 _289 _290 e) <=>
  obeys_max_app m e`;
   `obeys_max_app m (Letrec _294 _295 _296 es e:flatLang_exp) <=>
  EVERY (obeys_max_app m) (MAP SND es) /\ obeys_max_app m e`;
   `obeys_max_app m (closLang_Op _297 _298 es) <=> EVERY
  (obeys_max_app m) es`];;

let no_Labels_def = cake_define_list
  [`no_Labels (Var _301 _302:flatLang_exp) <=> T`;
   `no_Labels (If _304 e1 e2 e3:flatLang_exp) <=> no_Labels e1 /\
  no_Labels e2 /\ no_Labels e3`;
   `no_Labels (Let _306 es e:flatLang_exp) <=> EVERY no_Labels es /\
  no_Labels e`;
   `no_Labels (Raise _308 e:flatLang_exp) <=> no_Labels e`;
   `no_Labels (Handle _310 e1 e2:flatLang_exp) <=> no_Labels e1 /\
  no_Labels e2`;
   `no_Labels (closLang_Tick _311 e) <=> no_Labels e`;
   `no_Labels (closLang_Call _312 _313 _314 es) <=> EVERY no_Labels
  es`;
   `no_Labels (App _317 _318 e es:flatLang_exp) <=> no_Labels e /\
  EVERY no_Labels es`;
   `no_Labels (closLang_Fn _319 _320 _321 _322 e) <=> no_Labels e`;
   `no_Labels (Letrec _326 _327 _328 es e:flatLang_exp) <=> EVERY
  no_Labels (MAP SND es) /\ no_Labels e`;
   `no_Labels (closLang_Op _329 op es) <=> (!n. ~(op =
  closLang_Label n)) /\ EVERY no_Labels es`];;

let app_call_dests_def = cake_define_list
  [`app_call_dests opt [] = {}`;
   `app_call_dests opt (x :: y :: xs) =
         (let c1 = app_call_dests opt [x] in
         let c2 = app_call_dests opt (y :: xs) in
           c1 UNION c2)`;
   `app_call_dests opt [(Var _331 v:flatLang_exp)] = {}`;
   `app_call_dests opt [(If _333 x1 x2 x3:flatLang_exp)] =
         (let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt [x2] in
         let c3 = app_call_dests opt [x3] in
           c1 UNION c2 UNION c3)`;
   `app_call_dests opt [(Let _335 xs x2:flatLang_exp)] =
         (let c1 = app_call_dests opt xs in
         let c2 = app_call_dests opt [x2] in
           c1 UNION c2)`;
   `app_call_dests opt [(Raise _337 x1:flatLang_exp)] =
         app_call_dests opt [x1]`;
   `app_call_dests opt [closLang_Tick _338 x1] =
         app_call_dests opt [x1]`;
   `app_call_dests opt [closLang_Op _339 op xs] =
         app_call_dests opt xs`;
   `app_call_dests opt [(App _343 loc_opt x1 xs:flatLang_exp)] =
         (let ll = if opt = SOME T then {} else
                    match loc_opt with SOME n -> {n} | _344 -> {} in
         let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt xs in
             ll UNION c1 UNION c2)`;
   `app_call_dests opt [closLang_Fn _345 loc_opt vs num_args x1] =
         (let c1 = app_call_dests opt [x1] in c1)`;
   `app_call_dests opt [(Letrec _347 loc_opt vs fns x1:flatLang_exp)] =
         (let c1 = app_call_dests opt (MAP SND fns) in
         let c2 = app_call_dests opt [x1] in
         c1 UNION c2)`;
   `app_call_dests opt [(Handle _349 x1 x2:flatLang_exp)] =
         (let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt [x2] in
           c1 UNION c2)`;
   `app_call_dests opt [closLang_Call _350 ticks dest xs] =
         (if opt = SOME F then app_call_dests opt xs else
           dest INSERT app_call_dests opt xs)`];;

(* HOL4 overload (expanded in the port):
     call_dests = app_call_dests (SOME T) *)
(* HOL4 overload (expanded in the port):
     app_dests = app_call_dests (SOME F) *)
(* HOL4 overload (expanded in the port):
     any_dests = app_call_dests NONE *)

(* HOL4 ML code, not ported:
val app_call_dests_ind = theorem"app_call_dests_ind";
*)

let get_code_labels_def = cake_define_list
  [`closProps_get_code_labels (Var _353 _354:flatLang_exp) = {}`;
   `closProps_get_code_labels (If _356 e1 e2 e3:flatLang_exp) =
        closProps_get_code_labels e1 UNION
        closProps_get_code_labels e2 UNION
        closProps_get_code_labels e3`;
   `closProps_get_code_labels (Let _358 es e:flatLang_exp) =
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))
          UNION
        closProps_get_code_labels e`;
   `closProps_get_code_labels (Raise _360 e:flatLang_exp) =
  closProps_get_code_labels e`;
   `closProps_get_code_labels (Handle _362 e1 e2:flatLang_exp) =
        closProps_get_code_labels e1 UNION
        closProps_get_code_labels e2`;
   `closProps_get_code_labels (closLang_Tick _363 e) =
  closProps_get_code_labels e`;
   `closProps_get_code_labels (closLang_Call _364 _365 l es) =
        {l} UNION BIGUNION (set_of_list (MAP
          closProps_get_code_labels es))`;
   `closProps_get_code_labels (App _367 l e es:flatLang_exp) =
        (match l with NONE -> {} | SOME n -> {n}) UNION
        closProps_get_code_labels e UNION
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))`;
   `closProps_get_code_labels (closLang_Fn _368 l _369 _370 e) =
       (match l with NONE -> {} | SOME n -> {n}) UNION
       closProps_get_code_labels e`;
   `closProps_get_code_labels (Letrec _373 l _374 es e:flatLang_exp) =
       (match l with NONE -> {} | SOME n ->
         IMAGE (\k. n + 2 * k) (count (LENGTH es))) UNION
        closProps_get_code_labels e UNION
        BIGUNION (set_of_list (MAP closProps_get_code_labels (MAP
          SND es)))`;
   `closProps_get_code_labels (closLang_Op _375 op es) =
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))
          UNION
        assign_get_code_label op`];;
hol4_overload "get_code_labels" "closProps_get_code_labels";;

(* HOL4 ML code, not ported:
val code_locs_ind = theorem"code_locs_ind";
*)
