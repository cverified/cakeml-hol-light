(* ======================================================== *)
(*  bvlProps: ported from HOL4's
    compiler/backend/semantics/bvlPropsScript.sml
    A proof theory about bvl.ml, with 7 definitions and 65 theorems.
    Needed by 8 files of the port.  *)
(* ======================================================== *)

(*
  Properties about BVL and its semantics
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvlProps"
  ["backend_common"; "bvl"; "bvlSem"; "bvl_const"];;

let _ = do_list hide_constant ["parts"];;

(* HOL4 bvlPropsScript.sml:14: the ML values that the definitions
   below antiquote *)

(* [simp] *)
let with_same_code = prove
 (`bvlSem_state_code_fupd (K (bvlSem_state_code s))
      ((s:('c,'ffi)bvlSem_state)) = s`,
  CHEAT_TAC);;

(* [simp] *)
let with_same_clock = prove
 (`bvlSem_state_clock_fupd (K (bvlSem_state_clock st))
      (st:('a,'b)bvlSem_state) = st`,
  CHEAT_TAC);;

(* [simp] *)
let dec_clock_with_code = prove
 (`bvlSem_dec_clock n (bvlSem_state_code_fupd (K c) s) =
  state_code_fupd (K c) (bvlSem_dec_clock n s)`,
  CHEAT_TAC);;

(* HOL4 bvlPropsScript.sml:34-42: ML code, not ported *)

(* HOL4 bvlPropsScript.sml:44-45: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

(* [local] *)
let do_app_split_list = prove
 (`bvlSem_do_app op vs s = res <=>
   vs = [] /\ bvlSem_do_app op [] s = res \/
   (?v vs1. vs = CONS v vs1 /\ bvlSem_do_app op (CONS v vs1) s =
     res)`,
  CHEAT_TAC);;

(* [local] *)
let pair_lam_lem = prove
 (`!f v z. (let (x,y) = z in f x y) = v <=> (?x1 x2. z = (x1,x2) /\ (f
  x1 x2 = v))`,
  CHEAT_TAC);;

(* HOL4 bvlPropsScript.sml:62-67: a theorem that HOL4 states as the
   value of an ML expression: do_app_cases_val *)

(* HOL4 bvlPropsScript.sml:69-74: a theorem that HOL4 states as the
   value of an ML expression: do_app_cases_err *)

let do_app_Rval_swap = prove
 (`bvlSem_do_app op a (s1:('a,'b)bvlSem_state) = Rval (x0,x1) /\ ~(op =
  closLang_Install) /\
    (domain (bvlSem_state_code s1)) SUBSET (domain (bvlSem_state_code
      t1)) ==>
    bvlSem_do_app op a
      (bvlSem_state_ffi_fupd (K (bvlSem_state_ffi s1))
        (bvlSem_state_clock_fupd (K (bvlSem_state_clock s1))
        (bvlSem_state_refs_fupd (K (bvlSem_state_refs s1))
        (bvlSem_state_globals_fupd (K (bvlSem_state_globals s1))
        (t1:('a,'b)bvlSem_state))))) =
    Rval
      (x0,bvlSem_state_ffi_fupd (K (state_ffi x1))
        (bvlSem_state_clock_fupd (K (state_clock x1))
        (bvlSem_state_refs_fupd (K (state_refs x1))
        (bvlSem_state_globals_fupd (K (state_globals x1)) t1))))`,
  CHEAT_TAC);;

let do_app_with_code = prove
 (`bvlSem_do_app op vs s = Rval (r,s') /\ ~(op = closLang_Install) ==>
   domain (bvlSem_state_code s) SUBSET domain c ==>
   bvlSem_do_app op vs (bvlSem_state_compile_oracle_fupd (K co)
     (bvlSem_state_compile_fupd (K cc) (bvlSem_state_code_fupd (K c)
     s))) =
        Rval (r,compile_oracle_fupd (K co) (compile_fupd (K cc)
          (state_code_fupd (K c) s')))`,
  CHEAT_TAC);;

let do_app_Rerr_swap = prove
 (`bvlSem_do_app op a (s1:('a,'b)bvlSem_state) = Rerr e /\ ~(op =
  closLang_Install) /\
   (domain (bvlSem_state_code t1)) SUBSET (domain (bvlSem_state_code
     s1)) ==>
   bvlSem_do_app op a
    (bvlSem_state_ffi_fupd (K (bvlSem_state_ffi s1))
      (bvlSem_state_clock_fupd (K (bvlSem_state_clock s1))
      (bvlSem_state_refs_fupd (K (bvlSem_state_refs s1))
      (bvlSem_state_globals_fupd (K (bvlSem_state_globals s1))
      (t1:('a,'b)bvlSem_state))))) = Rerr e`,
  CHEAT_TAC);;

let do_app_with_code_err_not_Install = prove
 (`bvlSem_do_app op vs s = Rerr e /\ ~(op = closLang_Install) ==>
   (domain c SUBSET domain (bvlSem_state_code s) \/ ~(e = Rabort
     Rtype_error)) ==>
   bvlSem_do_app op vs (bvlSem_state_compile_oracle_fupd (K co)
     (bvlSem_state_compile_fupd (K cc) (bvlSem_state_code_fupd (K c)
     s))) = Rerr e`,
  CHEAT_TAC);;

let do_app_with_code_err = prove
 (`bvlSem_do_app op vs s = Rerr e ==>
   (domain c = domain (bvlSem_state_code s) \/ ~(e = Rabort
     Rtype_error)) ==>
   bvlSem_do_app op vs (bvlSem_state_code_fupd (K c) s) = Rerr e`,
  CHEAT_TAC);;

(* [simp] *)
let initial_state_simp = prove
 (`state_code
      (bvlSem_initial_state f c co cc k) = c /\ state_ffi
      (bvlSem_initial_state f c co cc k) = f /\ state_clock
      (bvlSem_initial_state f c co cc k) = k /\ compile
      (bvlSem_initial_state f c co cc k) = cc /\ compile_oracle
      (bvlSem_initial_state f c co cc k) = co /\ state_refs
      (bvlSem_initial_state f c co cc k) = FEMPTY /\ state_globals
      (bvlSem_initial_state f c co cc k) = []`,
  CHEAT_TAC);;

(* [simp] *)
let initial_state_with_simp = prove
 (`state_clock_fupd (K k1)
      (bvlSem_initial_state f c co cc k) = bvlSem_initial_state f c
        co cc k1 /\ state_code_fupd (K c1)
      (bvlSem_initial_state f c co cc k) = bvlSem_initial_state f
        c1 co cc k`,
  CHEAT_TAC);;

(* [simp] *)
let bool_to_tag_11 = prove
 (`bool_to_tag b1 = bool_to_tag b2 <=> (b1 = b2)`,
  CHEAT_TAC);;

(* Boolv_11[simp] *)
let boolv_11 = prove
 (`bvlSem_Boolv b1 = bvlSem_Boolv b2 <=> b1 = b2`,
  CHEAT_TAC);;

let find_code_EVERY_IMP = prove
 (`(bvlSem_find_code dest a (bvlSem_state_code
  (r:('c,'ffi)bvlSem_state)) = SOME (q,t)) ==>
    ALL P a ==> ALL P q`,
  CHEAT_TAC);;

let do_app_err = prove
 (`bvlSem_do_app op vs s = Rerr e ==>
                             (e = Rabort Rtype_error) \/
                             (?i x. op = closLang_FFI i /\ e =
                               Rabort (Rffi_error x))`,
  CHEAT_TAC);;

(* HOL4 bvlPropsScript.sml:213-223: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

(* HOL4 bvlPropsScript.sml:225: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

let evaluate_IMP_LENGTH = prove
 (`(bvlSem_evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs =
  LENGTH res)`,
  CHEAT_TAC);;

let evaluate_CONS = prove
 (`bvlSem_evaluate (CONS x xs,env,s) =
      (match bvlSem_evaluate ([x],env,s) with (Rval v,s2) ->
         (match bvlSem_evaluate (xs,env,s2) with (Rval vs,s1) ->
           (Rval (CONS (HD v) vs),s1) | t -> t) | t -> t)`,
  CHEAT_TAC);;

let evaluate_SNOC = prove
 (`!xs env s x.
      bvlSem_evaluate (SNOC x xs,env,s) =
      (match bvlSem_evaluate (xs,env,s) with (Rval vs,s2) ->
         (match bvlSem_evaluate ([x],env,s2) with (Rval v,s1) ->
           (Rval (APPEND vs v),s1) | t -> t) | t -> t)`,
  CHEAT_TAC);;

let evaluate_APPEND = prove
 (`!xs env s ys.
      bvlSem_evaluate (APPEND xs ys,env,s) =
      (match bvlSem_evaluate (xs,env,s) with
        (Rval vs,s2) ->
          (match bvlSem_evaluate (ys,env,s2) with
             (Rval ws,s1) -> (Rval (APPEND vs ws),s1) | res -> res)
               | res -> res)`,
  CHEAT_TAC);;

let evaluate_SING = prove
 (`(bvlSem_evaluate ([x],env,s) = (Rval a,p1)) ==> (?d1. a = [d1])`,
  CHEAT_TAC);;

let evaluate_code = prove
 (`!xs env s1 vs s2.
     (bvlSem_evaluate (xs,env,s1) = (vs,s2)) ==>
     (?n. compile_oracle
       s2 = misc_shift_seq n (compile_oracle s1) /\ state_code
       s2 = FOLDL sptree_union (state_code s1) (MAP (fromAList o SND)
         (list_of_seq (compile_oracle s1) n)))`,
  CHEAT_TAC);;

let evaluate_mono = prove
 (`!xs env s1 vs s2.
     (bvlSem_evaluate (xs,env,s1) = (vs,s2)) ==>
     subspt (state_code s1) (state_code s2)`,
  CHEAT_TAC);;

let evaluate_mk_tick = prove
 (`!exp env s n.
     bvlSem_evaluate ([mk_tick n exp],env,s) =
     (if bvlSem_state_clock s < n then
       (Rerr (Rabort Rtimeout_error),bvlSem_state_clock_fupd (K 0) s)
         else
       bvlSem_evaluate ([exp],env,bvlSem_dec_clock n s))`,
  CHEAT_TAC);;

let evaluate_MAP_Const = prove
 (`!exps.
     bvlSem_evaluate (MAP (K (bvl_Op (closLang_IntOp (closLang_Const
       i)) [])) (exps:'a list),env,t1) =
     (Rval (MAP (K (bvlSem_Number i)) exps),t1)`,
  CHEAT_TAC);;

(* [simp] *)
let evaluate_Bool = prove
 (`bvlSem_evaluate ([bvl_Bool b],env,s) = (Rval [bvlSem_Boolv b],s)`,
  CHEAT_TAC);;

(* HOL4 bvlPropsScript.sml:417: a proof *)

let evaluate_expand_env = prove
 (`!xs a s env. ~(FST (bvlSem_evaluate (xs,a,s)) = Rerr (Rabort
  Rtype_error)) ==>
     (bvlSem_evaluate (xs,APPEND a env,s) = bvlSem_evaluate
       (xs,a,s))`,
  CHEAT_TAC);;

let inc_clock_def = new_definition
  `bvlProps_inc_clock ck s = bvlSem_state_clock_fupd (K
  (bvlSem_state_clock s + ck)) s`;;

(* [simp] *)
let inc_clock_code = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). state_code (bvlProps_inc_clock n s)
  = bvlSem_state_code s`,
  CHEAT_TAC);;

(* [simp] *)
let inc_clock_refs = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). state_refs (bvlProps_inc_clock n s)
  = bvlSem_state_refs s`,
  CHEAT_TAC);;

(* [simp] *)
let inc_clock_ffi = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). state_ffi (bvlProps_inc_clock n s)
  = bvlSem_state_ffi s`,
  CHEAT_TAC);;

(* [simp] *)
let inc_clock_clock = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). state_clock (bvlProps_inc_clock n
  s) = bvlSem_state_clock s + n`,
  CHEAT_TAC);;

(* [simp] *)
let inc_clock0 = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). bvlProps_inc_clock 0 s = s`,
  CHEAT_TAC);;

let inc_clock_add = prove
 (`bvlProps_inc_clock k1 (bvlProps_inc_clock k2 s) =
  bvlProps_inc_clock (k1 + k2) s`,
  CHEAT_TAC);;

(* [simp] *)
let dec_clock_code = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). state_code (bvlSem_dec_clock n s) =
  bvlSem_state_code s`,
  CHEAT_TAC);;

(* [simp] *)
let dec_clock_refs = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). state_refs (bvlSem_dec_clock n s) =
  bvlSem_state_refs s`,
  CHEAT_TAC);;

(* [simp] *)
let dec_clock_ffi = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). state_ffi (bvlSem_dec_clock n s) =
  bvlSem_state_ffi s`,
  CHEAT_TAC);;

(* [simp] *)
let dec_clock0 = prove
 (`!n ((s:('c,'ffi)bvlSem_state)). bvlSem_dec_clock 0 s = s`,
  CHEAT_TAC);;

let do_app_change_clock = prove
 (`(bvlSem_do_app op args s1 = Rval (res,s2)) ==>
   (bvlSem_do_app op args (state_clock_fupd (K ck) s1) = Rval
     (res,state_clock_fupd (K ck) s2))`,
  CHEAT_TAC);;

let do_app_change_clock_err = prove
 (`(bvlSem_do_app op args s1 = Rerr e) ==>
   (bvlSem_do_app op args (state_clock_fupd (K ck) s1) = Rerr e)`,
  CHEAT_TAC);;

let evaluate_add_clock = prove
 (`!exps env s1 res s2.
     bvlSem_evaluate (exps,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
       Rtimeout_error)) ==>
     (!ck. bvlSem_evaluate (exps,env,bvlProps_inc_clock ck s1) =
       (res,bvlProps_inc_clock ck s2))`,
  CHEAT_TAC);;

let evaluate_add_clock_initial_state = prove
 (`bvlSem_evaluate (es,env,bvlSem_initial_state ffi code co cc k) =
  (r,s') /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
    (!extra.
      bvlSem_evaluate (es,env,bvlSem_initial_state ffi code co cc (k
        + extra)) =
      (r,state_clock_fupd (K (state_clock s' + extra)) s'))`,
  CHEAT_TAC);;

let do_app_io_events_mono = prove
 (`bvlSem_do_app op vs s1 = Rval (x,s2) ==> ffi_state_io_events
  (state_ffi
   s1) <<= ffi_state_io_events (state_ffi s2)`,
  CHEAT_TAC);;

let evaluate_io_events_mono = prove
 (`!exps env s1 res s2.
     bvlSem_evaluate (exps,env,s1) = (res,s2) ==> ffi_state_io_events
       (state_ffi
     s1) <<= ffi_state_io_events (state_ffi s2)`,
  CHEAT_TAC);;

(* [local] *)
let do_app_inc_clock = prove
 (`bvlSem_do_app op vs (bvlProps_inc_clock x y) =
    map_result (\(v,s). (v,bvlSem_state_clock_fupd (K (x +
      state_clock y)) s)) I (bvlSem_do_app op vs y)`,
  CHEAT_TAC);;

(* [local] *)
let dec_clock_1_inc_clock = prove
 (`~(x = 0) ==> bvlSem_dec_clock 1 (bvlProps_inc_clock x s) =
  bvlProps_inc_clock (x - 1) s`,
  CHEAT_TAC);;

(* [local] *)
let dec_clock_1_inc_clock2 = prove
 (`~(bvlSem_state_clock
     s = 0) ==> bvlSem_dec_clock 1 (bvlProps_inc_clock x s) =
       bvlProps_inc_clock x (bvlSem_dec_clock 1 s)`,
  CHEAT_TAC);;

(* [local] *)
let dec_clock_inc_clock = prove
 (`~(bvlSem_state_clock s < n) ==> bvlSem_dec_clock n
  (bvlProps_inc_clock x s) = bvlProps_inc_clock x (bvlSem_dec_clock n
  s)`,
  CHEAT_TAC);;

let evaluate_add_to_clock_io_events_mono = prove
 (`!exps env s extra. ffi_state_io_events (state_ffi
    (SND (bvlSem_evaluate (exps,env,s)))) <<= ffi_state_io_events
      (state_ffi
    (SND (bvlSem_evaluate (exps,env,bvlProps_inc_clock extra s))))`,
  CHEAT_TAC);;

(* [local] *)
let take_drop_lem = prove
 (`!skip env.
     skip < LENGTH env /\
     skip + SUC n <= LENGTH env /\ ~(DROP skip env = []) ==> CONS
       (EL skip env) (TAKE n (DROP (1 + skip) env)) = TAKE (n + 1)
       (DROP skip env)`,
  CHEAT_TAC);;

let evaluate_genlist_vars = prove
 (`!skip env n st.
    n + skip <= LENGTH env ==>
    bvlSem_evaluate (list_of_seq (\arg. bvl_Var (arg + skip))
      n,env,st) =
    (Rval (TAKE n (DROP skip env)),st)`,
  CHEAT_TAC);;

let evaluate_var_reverse = prove
 (`!xs env ys (st:('c,'ffi)bvlSem_state).
   bvlSem_evaluate (MAP bvl_Var xs,env,st) = (Rval ys,st) ==>
   bvlSem_evaluate (REVERSE (MAP bvl_Var xs),env,st) = (Rval
     (REVERSE ys),st)`,
  CHEAT_TAC);;

let evaluate_genlist_vars_rev = prove
 (`!skip env n st.
     n + skip <= LENGTH env ==>
     bvlSem_evaluate (REVERSE (list_of_seq (\arg. bvl_Var (arg +
       skip)) n),env,st) =
     (Rval (REVERSE (TAKE n (DROP skip env))),st)`,
  CHEAT_TAC);;

(* [local] *)
let do_build_SUBSET = prove
 (`!m n parts' refs q rs.
     bvlSem_do_build m n parts' refs = (q,rs) ==> FDOM refs SUBSET
       FDOM rs`,
  CHEAT_TAC);;

let do_app_refs_SUBSET = prove
 (`(bvlSem_do_app op a r = Rval (q,t)) ==> FDOM (state_refs r) SUBSET
  FDOM (state_refs t)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_refs_SUBSET_lemma = prove
 (`!xs env s. FDOM (bvlSem_state_refs s) SUBSET FDOM (state_refs (SND
  (bvlSem_evaluate (xs,env,s))))`,
  CHEAT_TAC);;

let evaluate_refs_SUBSET = prove
 (`(bvlSem_evaluate (xs,env,s) = (res,t)) ==> FDOM (bvlSem_state_refs
  s) SUBSET FDOM (state_refs t)`,
  CHEAT_TAC);;

let bvlProps_get_vars_def,bvlProps_get_vars_ind = define_rec
  [`bvlProps_get_vars [] env = SOME []`;
   `bvlProps_get_vars (CONS n ns) env =
         (if n < LENGTH env then
           (match bvlProps_get_vars ns env with NONE -> NONE |
             SOME vs -> SOME (CONS (EL n env) vs)) else NONE)`];;

let isVar_def = new_definition
  `isVar x1 =
        match x1 with
          ((bvl_Var n):bvl_exp) -> T
        | _1 -> F`;;

let destVar_def = define_general
  [`(destVar ((bvl_Var n):bvl_exp) = n)`];;

let evaluate_Var_list = prove
 (`!l. ALL isVar l ==>
       (bvlSem_evaluate (l,env,s) = (Rerr (Rabort Rtype_error),s)) \/
       (?vs. (bvlSem_evaluate (l,env,s) = (Rval vs,s)) /\
            (bvlProps_get_vars (MAP destVar l) env = SOME vs) /\
            (LENGTH vs = LENGTH l))`,
  CHEAT_TAC);;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvlPropsScript.sml:836-840: the tactic that proves the
   termination *)
let bVarBound_def,bVarBound_ind = define_wf
  `MEASURE (list_size bvl_exp_size o SND)`
  [`bVarBound n [] <=> T`;
   `bVarBound n (CONS (x:bvl_exp) (CONS y xs)) <=>
         bVarBound n [x] /\ bVarBound n (CONS y xs)`;
   `bVarBound n [(bvl_Var v:bvl_exp)] <=> v < n`;
   `bVarBound n [(bvl_If x1 x2 x3:bvl_exp)] <=>
         bVarBound n [x1] /\ bVarBound n [x2] /\ bVarBound n [x3]`;
   `bVarBound n [(bvl_Let xs x2:bvl_exp)] <=>
         bVarBound n xs /\ bVarBound (n + LENGTH xs) [x2]`;
   `bVarBound n [(bvl_Raise x1:bvl_exp)] <=> bVarBound n [x1]`;
   `bVarBound n [(bvl_Tick x1:bvl_exp)] <=> bVarBound n [x1]`;
   `bVarBound n [(bvl_Op op xs:bvl_exp)] <=> bVarBound n xs`;
   `bVarBound n [(bvl_Force loc v:bvl_exp)] <=> v < n`;
   `bVarBound n [(bvl_Handle x1 x2:bvl_exp)] <=>
         bVarBound n [x1] /\ bVarBound (n + 1) [x2]`;
   `bVarBound n [(bvl_Call ticks dest xs:bvl_exp)] <=> bVarBound n
  xs`];;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvlPropsScript.sml:858-862: the tactic that proves the
   termination *)
let bEvery_def,bEvery_ind = define_wf
  `MEASURE (list_size bvl_exp_size o SND)`
  [`bEvery P [] <=> T`;
   `bEvery P (CONS (x:bvl_exp) (CONS y xs)) <=>
         bEvery P [x] /\ bEvery P (CONS y xs)`;
   `bEvery P [(bvl_Var v:bvl_exp)] <=> P ((bvl_Var v:bvl_exp))`;
   `bEvery P [(bvl_If x1 x2 x3:bvl_exp)] <=> P ((bvl_If x1 x2
  x3:bvl_exp)) /\
         bEvery P [x1] /\ bEvery P [x2] /\ bEvery P [x3]`;
   `bEvery P [(bvl_Let xs x2:bvl_exp)] <=> P ((bvl_Let xs x2:bvl_exp))
  /\
         bEvery P xs /\ bEvery P [x2]`;
   `bEvery P [(bvl_Raise x1:bvl_exp)] <=> P ((bvl_Raise x1:bvl_exp))
  /\ bEvery P [x1]`;
   `bEvery P [(bvl_Tick x1:bvl_exp)] <=> P ((bvl_Tick x1:bvl_exp)) /\
  bEvery P [x1]`;
   `bEvery P [(bvl_Force m n:bvl_exp)] <=> P ((bvl_Force m
  n:bvl_exp))`;
   `bEvery P [(bvl_Op op xs:bvl_exp)] <=> P ((bvl_Op op xs:bvl_exp))
  /\ bEvery P xs`;
   `bEvery P [(bvl_Handle x1 x2:bvl_exp)] <=> P ((bvl_Handle x1
  x2:bvl_exp)) /\
         bEvery P [x1] /\ bEvery P [x2]`;
   `bEvery P [(bvl_Call ticks dest xs:bvl_exp)] <=> P ((bvl_Call
  ticks dest xs:bvl_exp)) /\ bEvery P xs`];;

let bVarBound_EVERY = prove
 (`!ls. bVarBound P ls <=> ALL (\e. bVarBound P [e]) ls`,
  CHEAT_TAC);;

let bEvery_EVERY = prove
 (`!ls. bEvery P ls <=> ALL (\e. bEvery P [e]) ls`,
  CHEAT_TAC);;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives is
     MEASURE flatLang_exp_size
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 bvlPropsScript.sml:888-895: the tactic that proves the
   termination *)
let bvlProps_get_code_labels_def,bvlProps_get_code_labels_ind =
  define_wf
  `MEASURE (\x0. bvl_exp_size x0)`
  [`bvlProps_get_code_labels (bvl_Var _2) = {}`;
   `bvlProps_get_code_labels (bvl_If e1 e2 e3:bvl_exp) =
  bvlProps_get_code_labels e1 UNION bvlProps_get_code_labels e2 UNION
  bvlProps_get_code_labels e3`;
   `bvlProps_get_code_labels (bvl_Let es e:bvl_exp) = UNIONS
  (set_of_list (MAP bvlProps_get_code_labels es)) UNION
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (bvl_Raise e:bvl_exp) =
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (bvl_Handle e1 e2:bvl_exp) =
  bvlProps_get_code_labels e1 UNION bvlProps_get_code_labels e2`;
   `bvlProps_get_code_labels (bvl_Tick e:bvl_exp) =
  bvlProps_get_code_labels e`;
   `bvlProps_get_code_labels (bvl_Force loc v:bvl_exp) = {loc}`;
   `bvlProps_get_code_labels (bvl_Call _4 d es:bvl_exp) = (match d
  with NONE -> {} | SOME n -> {n}) UNION UNIONS (set_of_list (MAP
  bvlProps_get_code_labels es))`;
   `bvlProps_get_code_labels (bvl_Op op es:bvl_exp) =
  assign_get_code_label op UNION UNIONS (set_of_list (MAP
  bvlProps_get_code_labels es))`];;

(* HOL4 bvlPropsScript.sml:897-898: a theorem that HOL4 states as the
   value of an ML expression: get_code_labels_def *)

(* [simp] *)
let mk_tick_code_labels = prove
 (`!n x. bvlProps_get_code_labels (mk_tick n x) =
  bvlProps_get_code_labels x`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["parts"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
