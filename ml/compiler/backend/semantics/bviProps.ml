(* ======================================================== *)
(*  bviProps: ported from HOL4's
    compiler/backend/semantics/bviPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about BVI and its semantics
*)

needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["error"];;

let bviProps_initial_state_simp =
  cake_theorem "initial_state_simp[simp]"
  (fun () ->
    `state_code
        (initial_state f c co cc k) = c /\ state_ffi
        (initial_state f c co cc k) = f /\ state_clock
        (initial_state f c co cc k) = k /\ compile
        (initial_state f c co cc k) = cc /\ compile_oracle
        (initial_state f c co cc k) = co /\ state_refs
        (initial_state f c co cc k) = FEMPTY /\ bviSem_state_global
        (initial_state f c co cc k) = NONE`)
  CHEAT_TAC;;

let bviProps_initial_state_with_simp =
  cake_theorem "initial_state_with_simp[simp]"
  (fun () ->
    `state_clock_fupd (K k1)
        (initial_state f c co cc k) = initial_state f c co cc k1 /\
          state_code_fupd (K c1)
        (initial_state f c co cc k) = initial_state f c1 co cc k`)
  CHEAT_TAC;;

let bvl_to_bvi_id = cake_theorem "bvl_to_bvi_id"
  (fun () ->
    `bvl_to_bvi (bvi_to_bvl s) s = s`)
  CHEAT_TAC;;

let bvl_to_bvi_with_refs = cake_theorem "bvl_to_bvi_with_refs"
  (fun () ->
    `bvl_to_bvi (state_refs_fupd (K y) x) z = state_refs_fupd (K y)
  (bvl_to_bvi x z)`)
  CHEAT_TAC;;

let bvl_to_bvi_with_clock = cake_theorem "bvl_to_bvi_with_clock"
  (fun () ->
    `bvl_to_bvi (state_clock_fupd (K y) x) z = state_clock_fupd (K y)
  (bvl_to_bvi x z)`)
  CHEAT_TAC;;

let bvl_to_bvi_with_ffi = cake_theorem "bvl_to_bvi_with_ffi"
  (fun () ->
    `bvl_to_bvi (state_ffi_fupd (K y) x) z = state_ffi_fupd (K y)
  (bvl_to_bvi x z)`)
  CHEAT_TAC;;

let bvl_to_bvi_code = cake_theorem "bvl_to_bvi_code[simp]"
  (fun () ->
    `state_code
        (bvl_to_bvi x y) = state_code y`)
  CHEAT_TAC;;

let bvl_to_bvi_clock = cake_theorem "bvl_to_bvi_clock[simp]"
  (fun () ->
    `state_clock
        (bvl_to_bvi x y) = state_clock x`)
  CHEAT_TAC;;

let bvi_to_bvl_refs = cake_theorem "bvi_to_bvl_refs[simp]"
  (fun () ->
    `state_refs
        (bvi_to_bvl x) = state_refs x`)
  CHEAT_TAC;;

let bvi_to_bvl_code = cake_theorem "bvi_to_bvl_code[simp]"
  (fun () ->
    `state_code
        (bvi_to_bvl x) = sptree_map (K ARB) (state_code x)`)
  CHEAT_TAC;;

let bvi_to_bvl_clock = cake_theorem "bvi_to_bvl_clock[simp]"
  (fun () ->
    `state_clock
        (bvi_to_bvl x) = state_clock x`)
  CHEAT_TAC;;

let bvi_to_bvl_ffi = cake_theorem "bvi_to_bvl_ffi[simp]"
  (fun () ->
    `state_ffi
        (bvi_to_bvl x) = state_ffi x`)
  CHEAT_TAC;;

let bvi_to_bvl_to_bvi_with_ffi =
  cake_theorem "bvi_to_bvl_to_bvi_with_ffi"
  (fun () ->
    `bvl_to_bvi (state_ffi_fupd (K f) (bvi_to_bvl x)) x =
  state_ffi_fupd (K f) x`)
  CHEAT_TAC;;

let domain_bvi_to_bvl_code = cake_theorem "domain_bvi_to_bvl_code[simp]"
  (fun () ->
    `domain (state_code (bvi_to_bvl s)) = domain (state_code s)`)
  CHEAT_TAC;;

(* HOL4 bviPropsScript.sml:103-108: ML code, not ported *)

let pair_case_elim = cake_theorem "pair_case_elim[local]"
  (fun () ->
    `pair_CASE p f <=> (?x y. p = (x,y) /\ f x y)`)
  CHEAT_TAC;;

(* HOL4 bviPropsScript.sml:116-119: a theorem that HOL4 states as the
   value of an ML expression: case_elim_thms *)

(* HOL4 bviPropsScript.sml:121-125: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

(* HOL4 bviPropsScript.sml:127-137: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

(* HOL4 bviPropsScript.sml:139-140: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

let bviProps_evaluate_IMP_LENGTH = cake_theorem "evaluate_IMP_LENGTH"
  (fun () ->
    `(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH
  res)`)
  CHEAT_TAC;;

let evaluate_SING_IMP = cake_theorem "evaluate_SING_IMP"
  (fun () ->
    `(evaluate ([x],env,s1) = (Rval vs,s2)) ==> (?w. vs = [w])`)
  CHEAT_TAC;;

let bviProps_evaluate_CONS = cake_theorem "evaluate_CONS"
  (fun () ->
    `evaluate (x :: xs,env,s) =
        (match evaluate ([x],env,s) with (Rval v,s2) ->
           (match evaluate (xs,env,s2) with (Rval vs,s1) -> (Rval
             (HD v :: vs),s1) | t -> t) | t -> t)`)
  CHEAT_TAC;;

let bviProps_evaluate_SNOC = cake_theorem "evaluate_SNOC"
  (fun () ->
    `!xs env s x.
        evaluate (SNOC x xs,env,s) =
        (match evaluate (xs,env,s) with (Rval vs,s2) ->
           (match evaluate ([x],env,s2) with (Rval v,s1) -> (Rval
             (vs ++ v),s1) | t -> t) | t -> t)`)
  CHEAT_TAC;;

let bviProps_evaluate_APPEND = cake_theorem "evaluate_APPEND"
  (fun () ->
    `!xs env s ys.
        evaluate (xs ++ ys,env,s) =
        (match evaluate (xs,env,s) with
          (Rval vs,s2) ->
            (match evaluate (ys,env,s2) with
               (Rval ws,s1) -> (Rval (vs ++ ws),s1) | res -> res)
                 | res -> res)`)
  CHEAT_TAC;;

let inc_clock_def = cake_define
  `bviProps_inc_clock n (s:('c,'ffi)bviSem_state) =
  bviSem_state_clock_fupd (K (bviSem_state_clock s + n)) s`;;
hol4_overload "inc_clock" "bviProps_inc_clock";;

let inc_clock_ZERO = cake_theorem "inc_clock_ZERO"
  (fun () ->
    `!s. inc_clock 0 s = s`)
  CHEAT_TAC;;

let inc_clock_ADD = cake_theorem "inc_clock_ADD"
  (fun () ->
    `inc_clock n (inc_clock m s) = inc_clock (n + m) s`)
  CHEAT_TAC;;

let bviProps_inc_clock_refs = cake_theorem "inc_clock_refs[simp]"
  (fun () ->
    `state_refs
        (inc_clock n s) = state_refs s`)
  CHEAT_TAC;;

let bviProps_inc_clock_code = cake_theorem "inc_clock_code[simp]"
  (fun () ->
    `state_code
        (inc_clock n s) = state_code s`)
  CHEAT_TAC;;

let inc_clock_global = cake_theorem "inc_clock_global[simp]"
  (fun () ->
    `bviSem_state_global
        (inc_clock n s) = bviSem_state_global s`)
  CHEAT_TAC;;

let bviProps_inc_clock_ffi = cake_theorem "inc_clock_ffi[simp]"
  (fun () ->
    `state_ffi
        (inc_clock n s) = state_ffi s`)
  CHEAT_TAC;;

let bviProps_inc_clock_clock = cake_theorem "inc_clock_clock[simp]"
  (fun () ->
    `state_clock
        (inc_clock n s) = state_clock s + n`)
  CHEAT_TAC;;

let dec_clock_global = cake_theorem "dec_clock_global[simp]"
  (fun () ->
    `bviSem_state_global
        (dec_clock n s) = bviSem_state_global s`)
  CHEAT_TAC;;

let bviProps_dec_clock_ffi = cake_theorem "dec_clock_ffi[simp]"
  (fun () ->
    `state_ffi
        (dec_clock n s) = state_ffi s`)
  CHEAT_TAC;;

let bviProps_dec_clock_refs = cake_theorem "dec_clock_refs[simp]"
  (fun () ->
    `state_refs
        (dec_clock n s) = state_refs s`)
  CHEAT_TAC;;

let bviProps_dec_clock_with_code =
  cake_theorem "dec_clock_with_code[simp]"
  (fun () ->
    `bviSem_dec_clock n (state_code_fupd (K c) s) = state_code_fupd (K
  c) (dec_clock n s)`)
  CHEAT_TAC;;

let bviProps_dec_clock_code = cake_theorem "dec_clock_code[simp]"
  (fun () ->
    `state_code
        (dec_clock n s) = state_code s`)
  CHEAT_TAC;;

let dec_clock_inv_clock = cake_theorem "dec_clock_inv_clock"
  (fun () ->
    `~(state_clock t1 < ticks + 1) ==>
      (dec_clock (ticks + 1) (inc_clock c t1) = inc_clock c
        (dec_clock (ticks + 1) t1))`)
  CHEAT_TAC;;

let dec_clock_inv_clock1 = cake_theorem "dec_clock_inv_clock1"
  (fun () ->
    `~(state_clock
        t1 = 0) ==>
         (dec_clock 1 (inc_clock c t1) = inc_clock c (dec_clock 1
           t1))`)
  CHEAT_TAC;;

let bviProps_dec_clock0 = cake_theorem "dec_clock0[simp]"
  (fun () ->
    `!n (s:('c,'ffi)bviSem_state). dec_clock 0 s = s`)
  CHEAT_TAC;;

let do_app_inv_clock = cake_theorem "do_app_inv_clock[local]"
  (fun () ->
    `match do_app op (REVERSE a) s with Rerr e -> (do_app op (REVERSE
  a) (inc_clock n s) = Rerr e) | Rval (v,s1) -> (do_app op (REVERSE a)
  (inc_clock n s) = Rval (v,inc_clock n s1))`)
  CHEAT_TAC;;

let do_app_inc_clock_IMP = cake_theorem "do_app_inc_clock_IMP[local]"
  (fun () ->
    `(do_app op vs s = Rval (v,s1) ==>
        do_app op vs (inc_clock n s) = Rval (v,inc_clock n s1)) /\
     (do_app op vs s = Rerr e ==> do_app op vs (inc_clock n s) =
       Rerr e)`)
  CHEAT_TAC;;

let evaluate_inv_clock = cake_theorem "evaluate_inv_clock"
  (fun () ->
    `!xs env t1 res t2 n.
        (evaluate (xs,env,t1) = (res,t2)) /\ ~(res = Rerr (Rabort
          Rtimeout_error)) ==>
        (evaluate (xs,env,inc_clock n t1) = (res,inc_clock n t2))`)
  CHEAT_TAC;;

let do_app_code = cake_theorem "do_app_code"
  (fun () ->
    `!op s1 s2. (do_app op a s1 = Rval (x0,s2)) /\ ~(op =
  closLang_Install) ==> (state_code s2 = state_code s1)`)
  CHEAT_TAC;;

let do_app_oracle = cake_theorem "do_app_oracle"
  (fun () ->
    `!op s1 s2. (do_app op a s1 = Rval (x0,s2)) /\ ~(op =
  closLang_Install) ==>
      (compile_oracle s2 = compile_oracle s1) /\
      (compile s2 = compile s1)`)
  CHEAT_TAC;;

let GENLIST_add_split = cake_theorem "GENLIST_add_split[local]"
  (fun () ->
    `!f a b. GENLIST f a ++ GENLIST (\i. f (a + i)) b = GENLIST f (a +
  b)`)
  CHEAT_TAC;;

let FOLDL_union_GENLIST_split =
  cake_theorem "FOLDL_union_GENLIST_split[local]"
  (fun () ->
    `FOLDL sptree_union (FOLDL sptree_union c (MAP (fromAList o SND)
  (GENLIST f a))) (MAP (fromAList o SND) (GENLIST (\i. f (i + a)) b)) =
     FOLDL sptree_union c (MAP (fromAList o SND) (GENLIST f (a +
       b)))`)
  CHEAT_TAC;;

let bviProps_evaluate_code = cake_theorem "evaluate_code"
  (fun () ->
    `!xs env s1 vs s2.
       (evaluate (xs,env,s1) = (vs,s2)) ==>
       (?n. compile_oracle
         s2 = misc_shift_seq n (compile_oracle s1) /\ state_code
         s2 = FOLDL sptree_union (state_code s1) (MAP (fromAList o
           SND)
           (GENLIST (compile_oracle s1) n)))`)
  CHEAT_TAC;;

let evaluate_code_mono = cake_theorem "evaluate_code_mono"
  (fun () ->
    `!xs env s1 vs s2.
       (evaluate (xs,env,s1) = (vs,s2)) ==>
       subspt (state_code s1) (state_code s2)`)
  CHEAT_TAC;;

let evaluate_global_mono_lemma =
  cake_theorem "evaluate_global_mono_lemma[local]"
  (fun () ->
    `!xs env s. IS_SOME (bviSem_state_global s) ==> IS_SOME
  (bviSem_state_global (SND (evaluate (xs,env,s))))`)
  CHEAT_TAC;;

let evaluate_global_mono = cake_theorem "evaluate_global_mono"
  (fun () ->
    `!xs env s res t. (evaluate (xs,env,s) = (res,t)) ==> IS_SOME
  (bviSem_state_global s) ==> IS_SOME (bviSem_state_global t)`)
  CHEAT_TAC;;

let bviProps_do_app_err = cake_theorem "do_app_err"
  (fun () ->
    `do_app op vs s = Rerr e ==>
                              (e = Rabort Rtype_error) \/
                              (?i x. op = FFI i /\ e = Rabort
                                (Rffi_error x))`)
  CHEAT_TAC;;

let do_app_aux_const = cake_theorem "do_app_aux_const"
  (fun () ->
    `bviSem_do_app_aux op vs s = SOME (SOME (y,z)) ==> state_clock
     z = state_clock s`)
  CHEAT_TAC;;

let bviProps_do_app_with_code = cake_theorem "do_app_with_code"
  (fun () ->
    `bviSem_do_app op vs s = Rval (r,s') ==>
     domain (state_code s) SUBSET domain c /\ ~(op =
       closLang_Install) ==>
     do_app op vs (state_code_fupd (K c) s) = Rval
       (r,state_code_fupd (K c) s')`)
  CHEAT_TAC;;

let bviProps_do_app_with_code_err = cake_theorem "do_app_with_code_err"
  (fun () ->
    `bviSem_do_app op vs s = Rerr e ==>
     (domain c SUBSET domain (state_code s) \/ ~(e = Rabort
       Rtype_error)) /\ ~(op = closLang_Install) ==>
     do_app op vs (state_code_fupd (K c) s) = Rerr e`)
  CHEAT_TAC;;

let do_app_aux_with_clock = cake_theorem "do_app_aux_with_clock"
  (fun () ->
    `bviSem_do_app_aux op vs (state_clock_fupd (K c) s) =
     OPTION_MAP (OPTION_MAP (\(x,y). (x,state_clock_fupd (K c)
       y))) (bviSem_do_app_aux op vs s)`)
  CHEAT_TAC;;

let bviProps_do_app_change_clock = cake_theorem "do_app_change_clock"
  (fun () ->
    `(do_app op args s1 = Rval (res,s2)) ==>
     (do_app op args (state_clock_fupd (K ck) s1) = Rval
       (res,state_clock_fupd (K ck) s2))`)
  CHEAT_TAC;;

let bviProps_do_app_change_clock_err =
  cake_theorem "do_app_change_clock_err"
  (fun () ->
    `bviSem_do_app op vs s = Rerr e ==>
     do_app op vs (state_clock_fupd (K c) s) = Rerr e`)
  CHEAT_TAC;;

let bviProps_evaluate_add_clock = cake_theorem "evaluate_add_clock"
  (fun () ->
    `!exps env s1 res s2.
      evaluate (exps,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
        Rtimeout_error)) ==>
      (!ck. evaluate (exps,env,inc_clock ck s1) = (res,inc_clock
        ck s2))`)
  CHEAT_TAC;;

let do_app_aux_io_events_mono = cake_theorem "do_app_aux_io_events_mono"
  (fun () ->
    `bviSem_do_app_aux op vs s = SOME (SOME (x,y)) ==>
  ffi_state_io_events (state_ffi
     s) <<= ffi_state_io_events (state_ffi y)`)
  CHEAT_TAC;;

let bviProps_do_app_io_events_mono =
  cake_theorem "do_app_io_events_mono"
  (fun () ->
    `do_app op vs s1 = Rval (x,s2) ==> ffi_state_io_events (state_ffi
     s1) <<= ffi_state_io_events (state_ffi s2)`)
  CHEAT_TAC;;

let bviProps_evaluate_io_events_mono =
  cake_theorem "evaluate_io_events_mono"
  (fun () ->
    `!exps env s1 res s2.
      evaluate (exps,env,s1) = (res,s2) ==> ffi_state_io_events
        (state_ffi
      s1) <<= ffi_state_io_events (state_ffi s2)`)
  CHEAT_TAC;;

let bviProps_do_app_inc_clock = cake_theorem "do_app_inc_clock[local]"
  (fun () ->
    `do_app op vs (inc_clock x y) =
      map_result (\(v,s). (v,state_clock_fupd (K (x + state_clock
        y)) s)) I (do_app op vs y)`)
  CHEAT_TAC;;

let bviProps_dec_clock_1_inc_clock =
  cake_theorem "dec_clock_1_inc_clock[local]"
  (fun () ->
    `~(x = 0) ==> dec_clock 1 (inc_clock x s) = inc_clock (x - 1) s`)
  CHEAT_TAC;;

let bviProps_dec_clock_1_inc_clock2 =
  cake_theorem "dec_clock_1_inc_clock2[local]"
  (fun () ->
    `~(state_clock
       s = 0) ==> dec_clock 1 (inc_clock x s) = inc_clock x
         (dec_clock 1 s)`)
  CHEAT_TAC;;

let bviProps_dec_clock_inc_clock =
  cake_theorem "dec_clock_inc_clock[local]"
  (fun () ->
    `~(state_clock s < n) ==> dec_clock n (inc_clock x s) = inc_clock
  x (dec_clock n s)`)
  CHEAT_TAC;;

let inc_clock_eq_0 = cake_theorem "inc_clock_eq_0[simp]"
  (fun () ->
    `state_clock
        (inc_clock extra s) = 0 <=> state_clock s = 0 /\ extra =
          0`)
  CHEAT_TAC;;

let bviProps_evaluate_add_to_clock_io_events_mono =
  cake_theorem "evaluate_add_to_clock_io_events_mono"
  (fun () ->
    `!exps env s extra. ffi_state_io_events (state_ffi
      (SND (evaluate (exps,env,s)))) <<= ffi_state_io_events
        (state_ffi
      (SND (evaluate (exps,env,inc_clock extra s))))`)
  CHEAT_TAC;;

let bviProps_take_drop_lem = cake_theorem "take_drop_lem[local]"
  (fun () ->
    `!skip env.
       skip < LENGTH env /\
       skip + SUC n <= LENGTH env /\ ~(DROP skip env = []) ==>
       EL skip env :: TAKE n (DROP (1 + skip) env) = TAKE (n + 1)
         (DROP skip env)`)
  CHEAT_TAC;;

let bviProps_evaluate_genlist_vars =
  cake_theorem "evaluate_genlist_vars"
  (fun () ->
    `!skip env n (st:('c,'ffi)bviSem_state).
      n + skip <= LENGTH env ==>
      evaluate (GENLIST (\arg. Var (arg + skip)) n,env,st) =
      (Rval (TAKE n (DROP skip env)),st)`)
  CHEAT_TAC;;

let _ = size_thms "flatLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bviPropsScript.sml:711-718: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let get_code_labels_def = cake_define_list_try_tac (fun () ->
  `MEASURE flatLang_exp_size`)
  CHEAT_TAC
  [`bviProps_get_code_labels (Var _2:bvi_exp) = {}`;
   `bviProps_get_code_labels (If e1 e2 e3:bvi_exp) =
  bviProps_get_code_labels e1 UNION bviProps_get_code_labels e2 UNION
  bviProps_get_code_labels e3`;
   `bviProps_get_code_labels (Let es e:bvi_exp) = BIGUNION
  (set_of_list (MAP bviProps_get_code_labels es)) UNION
  bviProps_get_code_labels e`;
   `bviProps_get_code_labels (Raise e:bvi_exp) =
  bviProps_get_code_labels e`;
   `bviProps_get_code_labels (Tick e:bvi_exp) =
  bviProps_get_code_labels e`;
   `bviProps_get_code_labels (Force loc v:bvi_exp) = {loc}`;
   `bviProps_get_code_labels (Call _4 d es h:bvi_exp) =
        (match d with NONE -> {} | SOME n -> {n}) UNION
        (match h with NONE -> {} | SOME e ->
          bviProps_get_code_labels e) UNION
        BIGUNION (set_of_list (MAP bviProps_get_code_labels es))`;
   `bviProps_get_code_labels (Op op es:bvi_exp) =
  assign_get_code_label op UNION BIGUNION (set_of_list (MAP
  bviProps_get_code_labels es))`;
   `bviProps_get_code_labels (bvi_Return es:bvi_exp) = BIGUNION
  (set_of_list (MAP bviProps_get_code_labels es))`;
   `bviProps_get_code_labels (bvi_LetCall _5 _6 d es y) =
        {d} UNION bviProps_get_code_labels y UNION BIGUNION
          (set_of_list (MAP bviProps_get_code_labels es))`];;
hol4_overload "get_code_labels" "bviProps_get_code_labels";;

(* HOL4 bviPropsScript.sml:720-721: a theorem that HOL4 states as the
   value of an ML expression: get_code_labels_def *)

let good_code_labels_def = cake_define
  `bviProps_good_code_labels p elabs <=>
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND) p))
       SUBSET set_of_list (MAP FST p) UNION elabs`;;
hol4_overload "good_code_labels" "bviProps_good_code_labels";;

(* --- switching a compiler pass off --------------------------------------

   A pass that is configured off compiles with CURRY I, i.e. the identity.
   It still wraps the incremental compiler with state_cc/state_co, which
   moves one configuration component between the oracle's state and its
   config.  adj_orac below performs that move on a state; it is the BVI
   analogue of closProps' adj_orac_rel.                                    *)

let adj_orac_def = cake_define
  `(adj_orac cc f (s:('a,'ffi)bviSem_state):('b,'ffi)bviSem_state) =
     mk_bviSem_state (bviSem_state_refs s) (bviSem_state_clock s)
       (bviSem_state_global s) cc ((f ## I) o
       bviSem_state_compile_oracle s) (bviSem_state_code s)
       (bviSem_state_ffi s)`;;

let adj_orac_ok_def = cake_define
  `adj_orac_ok cc f (s:('a,'ffi)bviSem_state) <=>
     (!n x y. bviSem_state_compile_oracle s n = (x,y) ==>
       OPTION_MAP (I ## (I ## f)) (bviSem_state_compile s x y) =
         cc (f x) y)`;;

let adj_orac_simps = cake_theorem "adj_orac_simps[local]"
  (fun () ->
    `state_clock
       (adj_orac cc f s) = state_clock s /\ state_code
       (adj_orac cc f s) = state_code s /\ state_refs
       (adj_orac cc f s) = state_refs s /\ bviSem_state_global
       (adj_orac cc f s) = bviSem_state_global s /\ state_ffi
       (adj_orac cc f s) = state_ffi s /\
       dec_clock n (adj_orac cc f s) = adj_orac cc f (dec_clock n
         s) /\
       (state_clock_fupd (K k) (adj_orac cc f s)) = adj_orac cc f
         (state_clock_fupd (K k) s) /\
       (adj_orac_ok cc f (dec_clock n s) <=> adj_orac_ok cc f s) /\
       (adj_orac_ok cc f (state_clock_fupd (K k) s) <=>
         adj_orac_ok cc f s)`)
  CHEAT_TAC;;

let adj_orac_rel_def = cake_define
  `bviProps_adj_orac_rel cc f (s1:('a,'ffi)bviSem_state)
  (s2:('b,'ffi)bviSem_state) <=>
     adj_orac_ok cc f s1 /\ s2 = adj_orac cc f s1`;;
hol4_overload "adj_orac_rel" "bviProps_adj_orac_rel";;

let do_app_cfg_swap = cake_theorem "do_app_cfg_swap[local]"
  (fun () ->
    `~(op = closLang_Install) ==>
         ((do_app op args s = Rval (value,s1) /\
           domain (state_code s) SUBSET domain (state_code t) ==>
           do_app op args
             (state_ffi_fupd (K (state_ffi s))
               (bviSem_state_global_fupd (K (bviSem_state_global s))
               (state_clock_fupd (K (state_clock s)) (state_refs_fupd (K
               (state_refs s)) t)))) =
           Rval
             (value,state_ffi_fupd (K (state_ffi s1))
               (bviSem_state_global_fupd (K (bviSem_state_global s1))
               (state_clock_fupd (K (state_clock s1)) (state_refs_fupd
               (K (state_refs s1))
              t))))) /\
          (do_app op args s = Rerr error /\
           (domain (state_code t) SUBSET domain (state_code s) \/
             ~(error = Rabort Rtype_error)) ==>
           do_app op args
             (state_ffi_fupd (K (state_ffi s))
               (bviSem_state_global_fupd (K (bviSem_state_global s))
               (state_clock_fupd (K (state_clock s)) (state_refs_fupd (K
               (state_refs s)) t)))) =
           Rerr error))`)
  CHEAT_TAC;;

let do_app_cfg_swap_Rval = cake_theorem "do_app_cfg_swap_Rval[local]"
  (fun () ->
    `!op args (s) (s1)
         (t) value. ~(op = closLang_Install) /\ domain
           (bviSem_state_code s) = domain (bviSem_state_code t) /\
       do_app op args s = Rval (value,s1) ==>
       do_app op args
         (bviSem_state_ffi_fupd (K (bviSem_state_ffi s))
           (bviSem_state_global_fupd (K (bviSem_state_global s))
           (bviSem_state_clock_fupd (K (bviSem_state_clock s))
           (bviSem_state_refs_fupd (K (bviSem_state_refs s)) t)))) =
       Rval (value,bviSem_state_ffi_fupd (K (bviSem_state_ffi
         s1)) (bviSem_state_global_fupd (K (bviSem_state_global s1))
         (bviSem_state_clock_fupd (K (bviSem_state_clock s1))
         (bviSem_state_refs_fupd (K (bviSem_state_refs s1)) t))))`)
  CHEAT_TAC;;

let do_app_cfg_swap_Rerr = cake_theorem "do_app_cfg_swap_Rerr[local]"
  (fun () ->
    `!op args (s) (t) error'. ~(op = closLang_Install) /\ domain
  (bviSem_state_code s) = domain (bviSem_state_code t) /\
       do_app op args s = Rerr error' ==>
       do_app op args
         (bviSem_state_ffi_fupd (K (bviSem_state_ffi s))
           (bviSem_state_global_fupd (K (bviSem_state_global s))
           (bviSem_state_clock_fupd (K (bviSem_state_clock s))
           (bviSem_state_refs_fupd (K (bviSem_state_refs s)) t)))) =
           Rerr error'`)
  CHEAT_TAC;;

let do_install_Rerr_type = cake_theorem "do_install_Rerr_type[local]"
  (fun () ->
    `do_install args s = Rerr e ==> e = Rabort Rtype_error`)
  CHEAT_TAC;;

let do_install_adj_orac = cake_theorem "do_install_adj_orac[local]"
  (fun () ->
    `!args (s) v t cc (f).
       adj_orac_ok cc f s /\
       (do_install args s) =
         Rval (v,t) ==>
       (do_install args (adj_orac cc f s)) =
         Rval (v,adj_orac cc f t) /\
       adj_orac_ok cc f t`)
  CHEAT_TAC;;

let do_app_adj_orac = cake_theorem "do_app_adj_orac[local]"
  (fun () ->
    `adj_orac_ok cc f s ==>
       (!v t. do_app op args s = Rval (v,t) ==>
          do_app op args (adj_orac cc f s) = Rval (v,adj_orac cc f
            t) /\
          adj_orac_ok cc f t) /\
       (!e. do_app op args s = Rerr e /\ ~(e = Rabort Rtype_error)
         ==>
          do_app op args (adj_orac cc f s) = Rerr e)`)
  CHEAT_TAC;;

let evaluate_adj_orac_rel = cake_theorem "evaluate_adj_orac_rel[local]"
  (fun () ->
    `!xs env (s).
       !res t1 cc f (s2).
         evaluate (xs,env,s) = (res,t1) /\ ~(res = Rerr (Rabort
           Rtype_error)) /\
         bviProps_adj_orac_rel cc f s s2 ==>
         (?t2. evaluate (xs,env,s2) = (res,t2) /\
           bviProps_adj_orac_rel cc f t1 t2)`)
  CHEAT_TAC;;

let evaluate_adj_orac = cake_theorem "evaluate_adj_orac"
  (fun () ->
    `evaluate (xs,env,(s:('a,'ffi)bviSem_state)) = (res,t1) /\ ~(res =
  Rerr (Rabort Rtype_error)) /\
     adj_orac_ok cc (f:'a->'b) s ==>
     evaluate (xs,env,adj_orac cc f s) = (res,adj_orac cc f t1) /\
     adj_orac_ok cc f t1`)
  CHEAT_TAC;;

let adj_orac_initial_state =
  cake_theorem "adj_orac_initial_state[local]"
  (fun () ->
    `adj_orac cc SND (initial_state ffi code co (state_cc (CURRY I) cc)
  k) =
     initial_state ffi code (state_co (CURRY I) co) cc k`)
  CHEAT_TAC;;

let adj_orac_ok_initial_state =
  cake_theorem "adj_orac_ok_initial_state[local]"
  (fun () ->
    `adj_orac_ok cc SND (initial_state ffi code co (state_cc (CURRY I)
  cc) k)`)
  CHEAT_TAC;;

let evaluate_CURRY_I = cake_theorem "evaluate_CURRY_I[local]"
  (fun () ->
    `evaluate (es,env,initial_state ffi code co (state_cc (CURRY I) cc)
  k) = (r,s) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
     (?s2.
       evaluate (es,env,initial_state ffi code (state_co (CURRY I)
         co) cc k) =
         (r,s2) /\ state_ffi s2 = state_ffi s)`)
  CHEAT_TAC;;

let semantics_CURRY_I = cake_theorem "semantics_CURRY_I"
  (fun () ->
    `~(semantics ffi code co (state_cc (CURRY I) cc) start = ffi_Fail)
  ==>
       semantics ffi code co (state_cc (CURRY I) cc) start =
       semantics ffi code (state_co (CURRY I) co) cc start`)
  CHEAT_TAC;;

cake_hide [];;
