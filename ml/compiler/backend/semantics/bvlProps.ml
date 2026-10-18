(* ======================================================== *)
(*  bvlProps: ported from HOL4's
    compiler/backend/semantics/bvlPropsScript.sml
    A proof theory about bvl.ml, with 7 definitions and 65 theorems.
    Needed by 12 files of the port.  *)
(* ======================================================== *)

(*
  Properties about BVL and its semantics
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["parts"];;

(* HOL4 bvlPropsScript.sml:14: the ML values that the definitions
   below antiquote *)

let with_same_code = cake_theorem "with_same_code[simp]"
  (fun () ->
    `bvlSem_state_code_fupd (K (bvlSem_state_code s))
        ((s:('c,'ffi)bvlSem_state)) = s`)
  CHEAT_TAC;;

let with_same_clock = cake_theorem "with_same_clock[simp]"
  (fun () ->
    `bvlSem_state_clock_fupd (K (bvlSem_state_clock st))
        (st:('a,'b)bvlSem_state) = st`)
  CHEAT_TAC;;

let dec_clock_with_code = cake_theorem "dec_clock_with_code[simp]"
  (fun () ->
    `bvlSem_dec_clock n (bvlSem_state_code_fupd (K c) s) =
  state_code_fupd (K c) (dec_clock n s)`)
  CHEAT_TAC;;

(* HOL4 bvlPropsScript.sml:34-42: ML code, not ported *)

(* HOL4 bvlPropsScript.sml:44-45: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

let do_app_split_list = cake_theorem "do_app_split_list[local]"
  (fun () ->
    `do_app op vs s = res <=>
     vs = [] /\ do_app op [] s = res \/
     (?v vs1. vs = v :: vs1 /\ do_app op (v :: vs1) s = res)`)
  CHEAT_TAC;;

let pair_lam_lem = cake_theorem "pair_lam_lem[local]"
  (fun () ->
    `!f v z. (let (x,y) = z in f x y) = v <=> (?x1 x2. z = (x1,x2) /\
  (f x1 x2 = v))`)
  CHEAT_TAC;;

(* HOL4 bvlPropsScript.sml:62-67: a theorem that HOL4 states as the
   value of an ML expression: do_app_cases_val *)

(* HOL4 bvlPropsScript.sml:69-74: a theorem that HOL4 states as the
   value of an ML expression: do_app_cases_err *)

let do_app_Rval_swap = cake_theorem "do_app_Rval_swap"
  (fun () ->
    `do_app op a (s1:('a,'b)bvlSem_state) = Rval (x0,x1) /\ ~(op =
  closLang_Install) /\
      (domain (bvlSem_state_code s1)) SUBSET (domain
        (bvlSem_state_code t1)) ==>
      do_app op a
        (bvlSem_state_ffi_fupd (K (bvlSem_state_ffi s1))
          (bvlSem_state_clock_fupd (K (bvlSem_state_clock s1))
          (bvlSem_state_refs_fupd (K (bvlSem_state_refs s1))
          (bvlSem_state_globals_fupd (K (bvlSem_state_globals s1))
          (t1:('a,'b)bvlSem_state))))) =
      Rval
        (x0,bvlSem_state_ffi_fupd (K (state_ffi x1))
          (bvlSem_state_clock_fupd (K (state_clock x1))
          (bvlSem_state_refs_fupd (K (state_refs x1))
          (bvlSem_state_globals_fupd (K (state_globals x1)) t1))))`)
  CHEAT_TAC;;

let do_app_with_code = cake_theorem "do_app_with_code"
  (fun () ->
    `bvlSem_do_app op vs s = Rval (r,s') /\ ~(op = closLang_Install) ==>
     domain (bvlSem_state_code s) SUBSET domain c ==>
     do_app op vs (bvlSem_state_compile_oracle_fupd (K co)
       (bvlSem_state_compile_fupd (K cc) (bvlSem_state_code_fupd (K c)
       s))) =
          Rval (r,compile_oracle_fupd (K co) (compile_fupd (K cc)
            (state_code_fupd (K c) s')))`)
  CHEAT_TAC;;

let do_app_Rerr_swap = cake_theorem "do_app_Rerr_swap"
  (fun () ->
    `do_app op a (s1:('a,'b)bvlSem_state) = Rerr e /\ ~(op =
  closLang_Install) /\
     (domain (bvlSem_state_code t1)) SUBSET (domain
       (bvlSem_state_code s1)) ==>
     do_app op a
      (bvlSem_state_ffi_fupd (K (bvlSem_state_ffi s1))
        (bvlSem_state_clock_fupd (K (bvlSem_state_clock s1))
        (bvlSem_state_refs_fupd (K (bvlSem_state_refs s1))
        (bvlSem_state_globals_fupd (K (bvlSem_state_globals s1))
        (t1:('a,'b)bvlSem_state))))) = Rerr e`)
  CHEAT_TAC;;

let do_app_with_code_err_not_Install =
  cake_theorem "do_app_with_code_err_not_Install"
  (fun () ->
    `bvlSem_do_app op vs s = Rerr e /\ ~(op = closLang_Install) ==>
     (domain c SUBSET domain (bvlSem_state_code s) \/ ~(e = Rabort
       Rtype_error)) ==>
     do_app op vs (bvlSem_state_compile_oracle_fupd (K co)
       (bvlSem_state_compile_fupd (K cc) (bvlSem_state_code_fupd (K c)
       s))) = Rerr e`)
  CHEAT_TAC;;

let do_app_with_code_err = cake_theorem "do_app_with_code_err"
  (fun () ->
    `bvlSem_do_app op vs s = Rerr e ==>
     (domain c = domain (bvlSem_state_code s) \/ ~(e = Rabort
       Rtype_error)) ==>
     do_app op vs (bvlSem_state_code_fupd (K c) s) = Rerr e`)
  CHEAT_TAC;;

let initial_state_simp = cake_theorem "initial_state_simp[simp]"
  (fun () ->
    `state_code
        (initial_state f c co cc k) = c /\ state_ffi
        (initial_state f c co cc k) = f /\ state_clock
        (initial_state f c co cc k) = k /\ compile
        (initial_state f c co cc k) = cc /\ compile_oracle
        (initial_state f c co cc k) = co /\ state_refs
        (initial_state f c co cc k) = FEMPTY /\ state_globals
        (initial_state f c co cc k) = []`)
  CHEAT_TAC;;

let initial_state_with_simp =
  cake_theorem "initial_state_with_simp[simp]"
  (fun () ->
    `state_clock_fupd (K k1)
        (initial_state f c co cc k) = initial_state f c co cc k1 /\
          state_code_fupd (K c1)
        (initial_state f c co cc k) = initial_state f c1 co cc k`)
  CHEAT_TAC;;

let bool_to_tag_11 = cake_theorem "bool_to_tag_11[simp]"
  (fun () ->
    `bool_to_tag b1 = bool_to_tag b2 <=> (b1 = b2)`)
  CHEAT_TAC;;

let boolv_11 = cake_theorem "Boolv_11[simp]"
  (fun () ->
    `bvlSem_Boolv b1 = Boolv b2 <=> b1 = b2`)
  CHEAT_TAC;;

let find_code_EVERY_IMP = cake_theorem "find_code_EVERY_IMP"
  (fun () ->
    `(find_code dest a (bvlSem_state_code (r:('c,'ffi)bvlSem_state)) =
  SOME (q,t)) ==>
      EVERY P a ==> EVERY P q`)
  CHEAT_TAC;;

let do_app_err = cake_theorem "do_app_err"
  (fun () ->
    `do_app op vs s = Rerr e ==>
                              (e = Rabort Rtype_error) \/
                              (?i x. op = FFI i /\ e = Rabort
                                (Rffi_error x))`)
  CHEAT_TAC;;

(* HOL4 bvlPropsScript.sml:213-223: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

(* HOL4 bvlPropsScript.sml:225: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

let evaluate_IMP_LENGTH = cake_theorem "evaluate_IMP_LENGTH"
  (fun () ->
    `(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH
  res)`)
  CHEAT_TAC;;

let evaluate_CONS = cake_theorem "evaluate_CONS"
  (fun () ->
    `evaluate (x :: xs,env,s) =
        (match evaluate ([x],env,s) with (Rval v,s2) ->
           (match evaluate (xs,env,s2) with (Rval vs,s1) -> (Rval
             (HD v :: vs),s1) | t -> t) | t -> t)`)
  CHEAT_TAC;;

let evaluate_SNOC = cake_theorem "evaluate_SNOC"
  (fun () ->
    `!xs env s x.
        evaluate (SNOC x xs,env,s) =
        (match evaluate (xs,env,s) with (Rval vs,s2) ->
           (match evaluate ([x],env,s2) with (Rval v,s1) -> (Rval
             (vs ++ v),s1) | t -> t) | t -> t)`)
  CHEAT_TAC;;

let evaluate_APPEND = cake_theorem "evaluate_APPEND"
  (fun () ->
    `!xs env s ys.
        evaluate (xs ++ ys,env,s) =
        (match evaluate (xs,env,s) with
          (Rval vs,s2) ->
            (match evaluate (ys,env,s2) with
               (Rval ws,s1) -> (Rval (vs ++ ws),s1) | res -> res)
                 | res -> res)`)
  CHEAT_TAC;;

let evaluate_SING = cake_theorem "evaluate_SING"
  (fun () ->
    `(evaluate ([x],env,s) = (Rval a,p1)) ==> (?d1. a = [d1])`)
  CHEAT_TAC;;

let evaluate_code = cake_theorem "evaluate_code"
  (fun () ->
    `!xs env s1 vs s2.
       (evaluate (xs,env,s1) = (vs,s2)) ==>
       (?n. compile_oracle
         s2 = misc_shift_seq n (compile_oracle s1) /\ state_code
         s2 = FOLDL sptree_union (state_code s1) (MAP (fromAList o
           SND)
           (GENLIST (compile_oracle s1) n)))`)
  CHEAT_TAC;;

let evaluate_mono = cake_theorem "evaluate_mono"
  (fun () ->
    `!xs env s1 vs s2.
       (evaluate (xs,env,s1) = (vs,s2)) ==>
       subspt (state_code s1) (state_code s2)`)
  CHEAT_TAC;;

let evaluate_mk_tick = cake_theorem "evaluate_mk_tick"
  (fun () ->
    `!exp env s n.
       evaluate ([mk_tick n exp],env,s) =
       (if bvlSem_state_clock s < n then
         (Rerr (Rabort Rtimeout_error),bvlSem_state_clock_fupd (K
           0) s) else
         evaluate ([exp],env,dec_clock n s))`)
  CHEAT_TAC;;

let evaluate_MAP_Const = cake_theorem "evaluate_MAP_Const"
  (fun () ->
    `!exps.
       evaluate (MAP (K (Op (closLang_IntOp (closLang_Const i))
         [])) (exps:'a list),env,t1) =
       (Rval (MAP (K (Number i)) exps),t1)`)
  CHEAT_TAC;;

let evaluate_Bool = cake_theorem "evaluate_Bool[simp]"
  (fun () ->
    `evaluate ([Bool b],env,s) = (Rval [Boolv b],s)`)
  CHEAT_TAC;;

(* HOL4 bvlPropsScript.sml:417: a proof *)

let evaluate_expand_env = cake_theorem "evaluate_expand_env"
  (fun () ->
    `!xs a s env. ~(FST (evaluate (xs,a,s)) = Rerr (Rabort Rtype_error))
  ==>
       (evaluate (xs,a ++ env,s) = evaluate (xs,a,s))`)
  CHEAT_TAC;;

let inc_clock_def = cake_define
  `bvlProps_inc_clock ck s = bvlSem_state_clock_fupd (K
  (bvlSem_state_clock s + ck)) s`;;
hol4_overload "inc_clock" "bvlProps_inc_clock";;

let inc_clock_code = cake_theorem "inc_clock_code[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). state_code (bvlProps_inc_clock n
  s) = bvlSem_state_code s`)
  CHEAT_TAC;;

let inc_clock_refs = cake_theorem "inc_clock_refs[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). state_refs (bvlProps_inc_clock n
  s) = bvlSem_state_refs s`)
  CHEAT_TAC;;

let inc_clock_ffi = cake_theorem "inc_clock_ffi[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). state_ffi (bvlProps_inc_clock n
  s) = bvlSem_state_ffi s`)
  CHEAT_TAC;;

let inc_clock_clock = cake_theorem "inc_clock_clock[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). state_clock (bvlProps_inc_clock n
  s) = bvlSem_state_clock s + n`)
  CHEAT_TAC;;

let inc_clock0 = cake_theorem "inc_clock0[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). bvlProps_inc_clock 0 s = s`)
  CHEAT_TAC;;

let inc_clock_add = cake_theorem "inc_clock_add"
  (fun () ->
    `bvlProps_inc_clock k1 (bvlProps_inc_clock k2 s) =
  bvlProps_inc_clock (k1 + k2) s`)
  CHEAT_TAC;;

let dec_clock_code = cake_theorem "dec_clock_code[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). state_code (dec_clock n s) =
  bvlSem_state_code s`)
  CHEAT_TAC;;

let dec_clock_refs = cake_theorem "dec_clock_refs[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). state_refs (dec_clock n s) =
  bvlSem_state_refs s`)
  CHEAT_TAC;;

let dec_clock_ffi = cake_theorem "dec_clock_ffi[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). state_ffi (dec_clock n s) =
  bvlSem_state_ffi s`)
  CHEAT_TAC;;

let dec_clock0 = cake_theorem "dec_clock0[simp]"
  (fun () ->
    `!n ((s:('c,'ffi)bvlSem_state)). dec_clock 0 s = s`)
  CHEAT_TAC;;

let do_app_change_clock = cake_theorem "do_app_change_clock"
  (fun () ->
    `(do_app op args s1 = Rval (res,s2)) ==>
     (do_app op args (state_clock_fupd (K ck) s1) = Rval
       (res,state_clock_fupd (K ck) s2))`)
  CHEAT_TAC;;

let do_app_change_clock_err = cake_theorem "do_app_change_clock_err"
  (fun () ->
    `(do_app op args s1 = Rerr e) ==>
     (do_app op args (state_clock_fupd (K ck) s1) = Rerr e)`)
  CHEAT_TAC;;

let evaluate_add_clock = cake_theorem "evaluate_add_clock"
  (fun () ->
    `!exps env s1 res s2.
       evaluate (exps,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
         Rtimeout_error)) ==>
       (!ck. evaluate (exps,env,bvlProps_inc_clock ck s1) =
         (res,bvlProps_inc_clock ck s2))`)
  CHEAT_TAC;;

let evaluate_add_clock_initial_state =
  cake_theorem "evaluate_add_clock_initial_state"
  (fun () ->
    `evaluate (es,env,initial_state ffi code co cc k) = (r,s') /\ ~(r =
  Rerr (Rabort Rtimeout_error)) ==>
      (!extra.
        evaluate (es,env,initial_state ffi code co cc (k + extra))
          =
        (r,state_clock_fupd (K (state_clock s' + extra)) s'))`)
  CHEAT_TAC;;

let do_app_io_events_mono = cake_theorem "do_app_io_events_mono"
  (fun () ->
    `do_app op vs s1 = Rval (x,s2) ==> ffi_state_io_events (state_ffi
     s1) <<= ffi_state_io_events (state_ffi s2)`)
  CHEAT_TAC;;

let evaluate_io_events_mono = cake_theorem "evaluate_io_events_mono"
  (fun () ->
    `!exps env s1 res s2.
       evaluate (exps,env,s1) = (res,s2) ==> ffi_state_io_events
         (state_ffi
       s1) <<= ffi_state_io_events (state_ffi s2)`)
  CHEAT_TAC;;

let do_app_inc_clock = cake_theorem "do_app_inc_clock[local]"
  (fun () ->
    `do_app op vs (bvlProps_inc_clock x y) =
      map_result (\(v,s). (v,bvlSem_state_clock_fupd (K (x +
        state_clock y)) s)) I (do_app op vs y)`)
  CHEAT_TAC;;

let dec_clock_1_inc_clock = cake_theorem "dec_clock_1_inc_clock[local]"
  (fun () ->
    `~(x = 0) ==> dec_clock 1 (bvlProps_inc_clock x s) =
  bvlProps_inc_clock (x - 1) s`)
  CHEAT_TAC;;

let dec_clock_1_inc_clock2 =
  cake_theorem "dec_clock_1_inc_clock2[local]"
  (fun () ->
    `~(bvlSem_state_clock
       s = 0) ==> dec_clock 1 (bvlProps_inc_clock x s) =
         bvlProps_inc_clock x (dec_clock 1 s)`)
  CHEAT_TAC;;

let dec_clock_inc_clock = cake_theorem "dec_clock_inc_clock[local]"
  (fun () ->
    `~(bvlSem_state_clock s < n) ==> dec_clock n (bvlProps_inc_clock x
  s) = bvlProps_inc_clock x (dec_clock n s)`)
  CHEAT_TAC;;

let evaluate_add_to_clock_io_events_mono =
  cake_theorem "evaluate_add_to_clock_io_events_mono"
  (fun () ->
    `!exps env s extra. ffi_state_io_events (state_ffi
      (SND (evaluate (exps,env,s)))) <<= ffi_state_io_events
        (state_ffi
      (SND (evaluate (exps,env,bvlProps_inc_clock extra s))))`)
  CHEAT_TAC;;

let take_drop_lem = cake_theorem "take_drop_lem[local]"
  (fun () ->
    `!skip env.
       skip < LENGTH env /\
       skip + SUC n <= LENGTH env /\ ~(DROP skip env = []) ==>
       EL skip env :: TAKE n (DROP (1 + skip) env) = TAKE (n + 1)
         (DROP skip env)`)
  CHEAT_TAC;;

let evaluate_genlist_vars = cake_theorem "evaluate_genlist_vars"
  (fun () ->
    `!skip env n st.
      n + skip <= LENGTH env ==>
      evaluate (GENLIST (\arg. Var (arg + skip)) n,env,st) =
      (Rval (TAKE n (DROP skip env)),st)`)
  CHEAT_TAC;;

let evaluate_var_reverse = cake_theorem "evaluate_var_reverse"
  (fun () ->
    `!xs env ys (st:('c,'ffi)bvlSem_state).
     evaluate (MAP Var xs,env,st) = (Rval ys,st) ==>
     evaluate (REVERSE (MAP Var xs),env,st) = (Rval (REVERSE
       ys),st)`)
  CHEAT_TAC;;

let evaluate_genlist_vars_rev = cake_theorem "evaluate_genlist_vars_rev"
  (fun () ->
    `!skip env n st.
       n + skip <= LENGTH env ==>
       evaluate (REVERSE (GENLIST (\arg. Var (arg + skip))
         n),env,st) =
       (Rval (REVERSE (TAKE n (DROP skip env))),st)`)
  CHEAT_TAC;;

let do_build_SUBSET = cake_theorem "do_build_SUBSET[local]"
  (fun () ->
    `!m n parts' refs q rs.
       bvlSem_do_build m n parts' refs = (q,rs) ==> FDOM refs
         SUBSET FDOM rs`)
  CHEAT_TAC;;

let do_app_refs_SUBSET = cake_theorem "do_app_refs_SUBSET"
  (fun () ->
    `(do_app op a r = Rval (q,t)) ==> FDOM (state_refs r) SUBSET FDOM
  (state_refs t)`)
  CHEAT_TAC;;

let evaluate_refs_SUBSET_lemma =
  cake_theorem "evaluate_refs_SUBSET_lemma[local]"
  (fun () ->
    `!xs env s. FDOM (bvlSem_state_refs s) SUBSET FDOM (state_refs
  (SND (evaluate (xs,env,s))))`)
  CHEAT_TAC;;

let evaluate_refs_SUBSET = cake_theorem "evaluate_refs_SUBSET"
  (fun () ->
    `(evaluate (xs,env,s) = (res,t)) ==> FDOM (bvlSem_state_refs s)
  SUBSET FDOM (state_refs t)`)
  CHEAT_TAC;;

let get_vars_def = cake_define_list
  [`bvlProps_get_vars [] env = SOME []`;
   `bvlProps_get_vars (n :: ns) env =
         (if n < LENGTH env then
           (match bvlProps_get_vars ns env with NONE -> NONE |
             SOME vs -> SOME (EL n env :: vs)) else NONE)`];;
hol4_overload "get_vars" "bvlProps_get_vars";;

let isVar_def = cake_define
  `isVar x1 =
        match x1 with
          ((Var n):bvl_exp) -> T
        | _1 -> F`;;

let destVar_def = cake_define
  `(destVar ((Var n):bvl_exp) = n)`;;

let evaluate_Var_list = cake_theorem "evaluate_Var_list"
  (fun () ->
    `!l. EVERY isVar l ==>
         (evaluate (l,env,s) = (Rerr (Rabort Rtype_error),s)) \/
         (?vs. (evaluate (l,env,s) = (Rval vs,s)) /\
              (bvlProps_get_vars (MAP destVar l) env = SOME vs) /\
              (LENGTH vs = LENGTH l))`)
  CHEAT_TAC;;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let bVarBound_def = cake_define_list_wf
  `MEASURE (list_size bvl_exp_size o SND)`
  [`bVarBound n [] <=> T`;
   `bVarBound n ((x:bvl_exp) :: y :: xs) <=>
         bVarBound n [x] /\ bVarBound n (y :: xs)`;
   `bVarBound n [(Var v:bvl_exp)] <=> v < n`;
   `bVarBound n [(If x1 x2 x3:bvl_exp)] <=>
         bVarBound n [x1] /\ bVarBound n [x2] /\ bVarBound n [x3]`;
   `bVarBound n [(Let xs x2:bvl_exp)] <=>
         bVarBound n xs /\ bVarBound (n + LENGTH xs) [x2]`;
   `bVarBound n [(Raise x1:bvl_exp)] <=> bVarBound n [x1]`;
   `bVarBound n [(Tick x1:bvl_exp)] <=> bVarBound n [x1]`;
   `bVarBound n [(Op op xs:bvl_exp)] <=> bVarBound n xs`;
   `bVarBound n [(Force loc v:bvl_exp)] <=> v < n`;
   `bVarBound n [(Handle x1 x2:bvl_exp)] <=>
         bVarBound n [x1] /\ bVarBound (n + 1) [x2]`;
   `bVarBound n [(Call ticks dest xs:bvl_exp)] <=> bVarBound n xs`];;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let bEvery_def = cake_define_list_wf
  `MEASURE (list_size bvl_exp_size o SND)`
  [`bEvery P [] <=> T`;
   `bEvery P ((x:bvl_exp) :: y :: xs) <=>
         bEvery P [x] /\ bEvery P (y :: xs)`;
   `bEvery P [(Var v:bvl_exp)] <=> P ((Var v:bvl_exp))`;
   `bEvery P [(If x1 x2 x3:bvl_exp)] <=> P ((If x1 x2 x3:bvl_exp)) /\
         bEvery P [x1] /\ bEvery P [x2] /\ bEvery P [x3]`;
   `bEvery P [(Let xs x2:bvl_exp)] <=> P ((Let xs x2:bvl_exp)) /\
         bEvery P xs /\ bEvery P [x2]`;
   `bEvery P [(Raise x1:bvl_exp)] <=> P ((Raise x1:bvl_exp)) /\
  bEvery P [x1]`;
   `bEvery P [(Tick x1:bvl_exp)] <=> P ((Tick x1:bvl_exp)) /\ bEvery
  P [x1]`;
   `bEvery P [(Force m n:bvl_exp)] <=> P ((Force m n:bvl_exp))`;
   `bEvery P [(Op op xs:bvl_exp)] <=> P ((Op op xs:bvl_exp)) /\
  bEvery P xs`;
   `bEvery P [(Handle x1 x2:bvl_exp)] <=> P ((Handle x1 x2:bvl_exp)) /\
         bEvery P [x1] /\ bEvery P [x2]`;
   `bEvery P [(Call ticks dest xs:bvl_exp)] <=> P ((Call ticks dest
  xs:bvl_exp)) /\ bEvery P xs`];;

let bVarBound_EVERY = cake_theorem "bVarBound_EVERY"
  (fun () ->
    `!ls. bVarBound P ls <=> EVERY (\e. bVarBound P [e]) ls`)
  CHEAT_TAC;;

let bEvery_EVERY = cake_theorem "bEvery_EVERY"
  (fun () ->
    `!ls. bEvery P ls <=> EVERY (\e. bEvery P [e]) ls`)
  CHEAT_TAC;;

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvlPropsScript.sml:888-895: the tactic that proves the
   termination *)
let get_code_labels_def = cake_define_list_try (fun () ->
  `MEASURE flatLang_exp_size`)
  [`bvlProps_get_code_labels (bvl_Var _2) = {}`;
   `bvlProps_get_code_labels (If e1 e2 e3:bvl_exp) =
  bvlProps_get_code_labels e1 UNION bvlProps_get_code_labels e2 UNION
  bvlProps_get_code_labels e3`;
   `bvlProps_get_code_labels (Let es e:bvl_exp) = BIGUNION
  (set_of_list (MAP bvlProps_get_code_labels es)) UNION
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (Raise e:bvl_exp) =
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (Handle e1 e2:bvl_exp) =
  bvlProps_get_code_labels e1 UNION bvlProps_get_code_labels e2`;
   `bvlProps_get_code_labels (Tick e:bvl_exp) =
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (Force loc v:bvl_exp) = {loc}`;
   `bvlProps_get_code_labels (Call _4 d es:bvl_exp) = (match d with
  NONE -> {} | SOME n -> {n}) UNION BIGUNION (set_of_list (MAP
  bvlProps_get_code_labels es))`;
   `bvlProps_get_code_labels (Op op es:bvl_exp) =
  assign_get_code_label op UNION BIGUNION (set_of_list (MAP
  bvlProps_get_code_labels es))`];;
hol4_overload "get_code_labels" "bvlProps_get_code_labels";;

(* HOL4 bvlPropsScript.sml:897-898: a theorem that HOL4 states as the
   value of an ML expression: get_code_labels_def *)

let mk_tick_code_labels = cake_theorem "mk_tick_code_labels[simp]"
  (fun () ->
    `!n x. bvlProps_get_code_labels (mk_tick n x) =
  bvlProps_get_code_labels x`)
  CHEAT_TAC;;

cake_hide [];;
