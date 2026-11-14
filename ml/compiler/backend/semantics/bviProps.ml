(* ======================================================== *)
(*  bviProps: ported from HOL4's
    compiler/backend/semantics/bviPropsScript.sml
    A proof theory about bvi.ml, with 6 definitions and 82 theorems.
    Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  Properties about BVI and its semantics
*)

needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "lib/sptree.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bviProps"
  ["backendProps"; "bviSem"; "bvlProps"];;

let _ = do_list hide_constant ["error"];;

(* initial_state_simp[simp] *)
let bviProps_initial_state_simp = prove
 (`state_code
      (bviSem_initial_state f c co cc k) = c /\ state_ffi
      (bviSem_initial_state f c co cc k) = f /\ state_clock
      (bviSem_initial_state f c co cc k) = k /\ compile
      (bviSem_initial_state f c co cc k) = cc /\ compile_oracle
      (bviSem_initial_state f c co cc k) = co /\ state_refs
      (bviSem_initial_state f c co cc k) = FEMPTY /\
        bviSem_state_global
      (bviSem_initial_state f c co cc k) = NONE`,
  CHEAT_TAC);;

(* initial_state_with_simp[simp] *)
let bviProps_initial_state_with_simp = prove
 (`state_clock_fupd (K k1)
      (bviSem_initial_state f c co cc k) = bviSem_initial_state f c
        co cc k1 /\ state_code_fupd (K c1)
      (bviSem_initial_state f c co cc k) = bviSem_initial_state f
        c1 co cc k`,
  CHEAT_TAC);;

let bvl_to_bvi_id = prove
 (`bvl_to_bvi (bvi_to_bvl s) s = s`,
  CHEAT_TAC);;

let bvl_to_bvi_with_refs = prove
 (`bvl_to_bvi (state_refs_fupd (K y) x) z = state_refs_fupd (K y)
  (bvl_to_bvi x z)`,
  CHEAT_TAC);;

let bvl_to_bvi_with_clock = prove
 (`bvl_to_bvi (state_clock_fupd (K y) x) z = state_clock_fupd (K y)
  (bvl_to_bvi x z)`,
  CHEAT_TAC);;

let bvl_to_bvi_with_ffi = prove
 (`bvl_to_bvi (state_ffi_fupd (K y) x) z = state_ffi_fupd (K y)
  (bvl_to_bvi x z)`,
  CHEAT_TAC);;

(* [simp] *)
let bvl_to_bvi_code = prove
 (`state_code
      (bvl_to_bvi x y) = state_code y`,
  CHEAT_TAC);;

(* [simp] *)
let bvl_to_bvi_clock = prove
 (`state_clock
      (bvl_to_bvi x y) = state_clock x`,
  CHEAT_TAC);;

(* [simp] *)
let bvi_to_bvl_refs = prove
 (`state_refs
      (bvi_to_bvl x) = state_refs x`,
  CHEAT_TAC);;

(* [simp] *)
let bvi_to_bvl_code = prove
 (`state_code
      (bvi_to_bvl x) = sptree_map (K ARB) (state_code x)`,
  CHEAT_TAC);;

(* [simp] *)
let bvi_to_bvl_clock = prove
 (`state_clock
      (bvi_to_bvl x) = state_clock x`,
  CHEAT_TAC);;

(* [simp] *)
let bvi_to_bvl_ffi = prove
 (`state_ffi
      (bvi_to_bvl x) = state_ffi x`,
  CHEAT_TAC);;

let bvi_to_bvl_to_bvi_with_ffi = prove
 (`bvl_to_bvi (state_ffi_fupd (K f) (bvi_to_bvl x)) x = state_ffi_fupd
  (K f) x`,
  CHEAT_TAC);;

(* [simp] *)
let domain_bvi_to_bvl_code = prove
 (`domain (state_code (bvi_to_bvl s)) = domain (state_code s)`,
  CHEAT_TAC);;

(* HOL4 bviPropsScript.sml:103-108: ML code, not ported *)

(* [local] *)
let pair_case_elim = prove
 (`pair_CASE p f <=> (?x y. p = (x,y) /\ f x y)`,
  CHEAT_TAC);;

(* HOL4 bviPropsScript.sml:116-119: a theorem that HOL4 states as the
   value of an ML expression: case_elim_thms *)

(* HOL4 bviPropsScript.sml:121-125: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

(* HOL4 bviPropsScript.sml:127-137: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

(* HOL4 bviPropsScript.sml:139-140: a theorem that HOL4 states as the
   value of an ML expression: evaluate_LENGTH *)

(* evaluate_IMP_LENGTH *)
let bviProps_evaluate_IMP_LENGTH = prove
 (`(bviSem_evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs =
  LENGTH res)`,
  CHEAT_TAC);;

let evaluate_SING_IMP = prove
 (`(bviSem_evaluate ([x],env,s1) = (Rval vs,s2)) ==> (?w. vs = [w])`,
  CHEAT_TAC);;

(* evaluate_CONS *)
let bviProps_evaluate_CONS = prove
 (`bviSem_evaluate (CONS x xs,env,s) =
      (match bviSem_evaluate ([x],env,s) with (Rval v,s2) ->
         (match bviSem_evaluate (xs,env,s2) with (Rval vs,s1) ->
           (Rval (CONS (HD v) vs),s1) | t -> t) | t -> t)`,
  CHEAT_TAC);;

(* evaluate_SNOC *)
let bviProps_evaluate_SNOC = prove
 (`!xs env s x.
      bviSem_evaluate (SNOC x xs,env,s) =
      (match bviSem_evaluate (xs,env,s) with (Rval vs,s2) ->
         (match bviSem_evaluate ([x],env,s2) with (Rval v,s1) ->
           (Rval (APPEND vs v),s1) | t -> t) | t -> t)`,
  CHEAT_TAC);;

(* evaluate_APPEND *)
let bviProps_evaluate_APPEND = prove
 (`!xs env s ys.
      bviSem_evaluate (APPEND xs ys,env,s) =
      (match bviSem_evaluate (xs,env,s) with
        (Rval vs,s2) ->
          (match bviSem_evaluate (ys,env,s2) with
             (Rval ws,s1) -> (Rval (APPEND vs ws),s1) | res -> res)
               | res -> res)`,
  CHEAT_TAC);;

let bviProps_inc_clock_def = new_definition
  `bviProps_inc_clock n (s:('c,'ffi)bviSem_state) =
  bviSem_state_clock_fupd (K (bviSem_state_clock s + n)) s`;;

let inc_clock_ZERO = prove
 (`!s. bviProps_inc_clock 0 s = s`,
  CHEAT_TAC);;

let inc_clock_ADD = prove
 (`bviProps_inc_clock n (bviProps_inc_clock m s) = bviProps_inc_clock
  (n + m) s`,
  CHEAT_TAC);;

(* inc_clock_refs[simp] *)
let bviProps_inc_clock_refs = prove
 (`state_refs
      (bviProps_inc_clock n s) = state_refs s`,
  CHEAT_TAC);;

(* inc_clock_code[simp] *)
let bviProps_inc_clock_code = prove
 (`state_code
      (bviProps_inc_clock n s) = state_code s`,
  CHEAT_TAC);;

(* [simp] *)
let inc_clock_global = prove
 (`bviSem_state_global
      (bviProps_inc_clock n s) = bviSem_state_global s`,
  CHEAT_TAC);;

(* inc_clock_ffi[simp] *)
let bviProps_inc_clock_ffi = prove
 (`state_ffi
      (bviProps_inc_clock n s) = state_ffi s`,
  CHEAT_TAC);;

(* inc_clock_clock[simp] *)
let bviProps_inc_clock_clock = prove
 (`state_clock
      (bviProps_inc_clock n s) = state_clock s + n`,
  CHEAT_TAC);;

(* [simp] *)
let dec_clock_global = prove
 (`bviSem_state_global
      (bviSem_dec_clock n s) = bviSem_state_global s`,
  CHEAT_TAC);;

(* dec_clock_ffi[simp] *)
let bviProps_dec_clock_ffi = prove
 (`state_ffi
      (bviSem_dec_clock n s) = state_ffi s`,
  CHEAT_TAC);;

(* dec_clock_refs[simp] *)
let bviProps_dec_clock_refs = prove
 (`state_refs
      (bviSem_dec_clock n s) = state_refs s`,
  CHEAT_TAC);;

(* dec_clock_with_code[simp] *)
let bviProps_dec_clock_with_code = prove
 (`bviSem_dec_clock n (state_code_fupd (K c) s) = state_code_fupd (K
  c) (bviSem_dec_clock n s)`,
  CHEAT_TAC);;

(* dec_clock_code[simp] *)
let bviProps_dec_clock_code = prove
 (`state_code
      (bviSem_dec_clock n s) = state_code s`,
  CHEAT_TAC);;

let dec_clock_inv_clock = prove
 (`~(state_clock t1 < ticks + 1) ==>
    (bviSem_dec_clock (ticks + 1) (bviProps_inc_clock c t1) =
      bviProps_inc_clock c (bviSem_dec_clock (ticks + 1) t1))`,
  CHEAT_TAC);;

let dec_clock_inv_clock1 = prove
 (`~(state_clock
      t1 = 0) ==>
       (bviSem_dec_clock 1 (bviProps_inc_clock c t1) =
         bviProps_inc_clock c (bviSem_dec_clock 1 t1))`,
  CHEAT_TAC);;

(* dec_clock0[simp] *)
let bviProps_dec_clock0 = prove
 (`!n (s:('c,'ffi)bviSem_state). bviSem_dec_clock 0 s = s`,
  CHEAT_TAC);;

(* [local] *)
let do_app_inv_clock = prove
 (`match bviSem_do_app op (REVERSE a) s with Rerr e -> (bviSem_do_app
  op (REVERSE a) (bviProps_inc_clock n s) = Rerr e) | Rval (v,s1) ->
  (bviSem_do_app op (REVERSE a) (bviProps_inc_clock n s) = Rval
  (v,bviProps_inc_clock n s1))`,
  CHEAT_TAC);;

(* [local] *)
let do_app_inc_clock_IMP = prove
 (`(bviSem_do_app op vs s = Rval (v,s1) ==>
      bviSem_do_app op vs (bviProps_inc_clock n s) = Rval
        (v,bviProps_inc_clock n s1)) /\
   (bviSem_do_app op vs s = Rerr e ==> bviSem_do_app op vs
     (bviProps_inc_clock n s) = Rerr e)`,
  CHEAT_TAC);;

let evaluate_inv_clock = prove
 (`!xs env t1 res t2 n.
      (bviSem_evaluate (xs,env,t1) = (res,t2)) /\ ~(res = Rerr
        (Rabort Rtimeout_error)) ==>
      (bviSem_evaluate (xs,env,bviProps_inc_clock n t1) =
        (res,bviProps_inc_clock n t2))`,
  CHEAT_TAC);;

let do_app_code = prove
 (`!op s1 s2. (bviSem_do_app op a s1 = Rval (x0,s2)) /\ ~(op =
  closLang_Install) ==> (state_code s2 = state_code s1)`,
  CHEAT_TAC);;

let do_app_oracle = prove
 (`!op s1 s2. (bviSem_do_app op a s1 = Rval (x0,s2)) /\ ~(op =
  closLang_Install) ==>
    (compile_oracle s2 = compile_oracle s1) /\
    (compile s2 = compile s1)`,
  CHEAT_TAC);;

(* [local] *)
let GENLIST_add_split = prove
 (`!f a b. APPEND (list_of_seq f a) (list_of_seq (\i. f (a + i)) b) =
  list_of_seq f (a + b)`,
  CHEAT_TAC);;

(* [local] *)
let FOLDL_union_GENLIST_split = prove
 (`FOLDL sptree_union (FOLDL sptree_union c (MAP (fromAList o SND)
  (list_of_seq f a))) (MAP (fromAList o SND) (list_of_seq (\i. f (i +
  a)) b)) =
   FOLDL sptree_union c (MAP (fromAList o SND) (list_of_seq f (a +
     b)))`,
  CHEAT_TAC);;

(* evaluate_code *)
let bviProps_evaluate_code = prove
 (`!xs env s1 vs s2.
     (bviSem_evaluate (xs,env,s1) = (vs,s2)) ==>
     (?n. compile_oracle
       s2 = misc_shift_seq n (compile_oracle s1) /\ state_code
       s2 = FOLDL sptree_union (state_code s1) (MAP (fromAList o SND)
         (list_of_seq (compile_oracle s1) n)))`,
  CHEAT_TAC);;

let evaluate_code_mono = prove
 (`!xs env s1 vs s2.
     (bviSem_evaluate (xs,env,s1) = (vs,s2)) ==>
     subspt (state_code s1) (state_code s2)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_global_mono_lemma = prove
 (`!xs env s. IS_SOME (bviSem_state_global s) ==> IS_SOME
  (bviSem_state_global (SND (bviSem_evaluate (xs,env,s))))`,
  CHEAT_TAC);;

let evaluate_global_mono = prove
 (`!xs env s res t. (bviSem_evaluate (xs,env,s) = (res,t)) ==> IS_SOME
  (bviSem_state_global s) ==> IS_SOME (bviSem_state_global t)`,
  CHEAT_TAC);;

(* do_app_err *)
let bviProps_do_app_err = prove
 (`bviSem_do_app op vs s = Rerr e ==>
                             (e = Rabort Rtype_error) \/
                             (?i x. op = closLang_FFI i /\ e =
                               Rabort (Rffi_error x))`,
  CHEAT_TAC);;

let do_app_aux_const = prove
 (`bviSem_do_app_aux op vs s = SOME (SOME (y,z)) ==> state_clock
   z = state_clock s`,
  CHEAT_TAC);;

(* do_app_with_code *)
let bviProps_do_app_with_code = prove
 (`bviSem_do_app op vs s = Rval (r,s') ==>
   domain (state_code s) SUBSET domain c /\ ~(op = closLang_Install)
     ==>
   bviSem_do_app op vs (state_code_fupd (K c) s) = Rval
     (r,state_code_fupd (K c) s')`,
  CHEAT_TAC);;

(* do_app_with_code_err *)
let bviProps_do_app_with_code_err = prove
 (`bviSem_do_app op vs s = Rerr e ==>
   (domain c SUBSET domain (state_code s) \/ ~(e = Rabort
     Rtype_error)) /\ ~(op = closLang_Install) ==>
   bviSem_do_app op vs (state_code_fupd (K c) s) = Rerr e`,
  CHEAT_TAC);;

let do_app_aux_with_clock = prove
 (`bviSem_do_app_aux op vs (state_clock_fupd (K c) s) =
   OPTION_MAP (OPTION_MAP (\(x,y). (x,state_clock_fupd (K c) y)))
     (bviSem_do_app_aux op vs s)`,
  CHEAT_TAC);;

(* do_app_change_clock *)
let bviProps_do_app_change_clock = prove
 (`(bviSem_do_app op args s1 = Rval (res,s2)) ==>
   (bviSem_do_app op args (state_clock_fupd (K ck) s1) = Rval
     (res,state_clock_fupd (K ck) s2))`,
  CHEAT_TAC);;

(* do_app_change_clock_err *)
let bviProps_do_app_change_clock_err = prove
 (`bviSem_do_app op vs s = Rerr e ==>
   bviSem_do_app op vs (state_clock_fupd (K c) s) = Rerr e`,
  CHEAT_TAC);;

(* evaluate_add_clock *)
let bviProps_evaluate_add_clock = prove
 (`!exps env s1 res s2.
    bviSem_evaluate (exps,env,s1) = (res,s2) /\ ~(res = Rerr (Rabort
      Rtimeout_error)) ==>
    (!ck. bviSem_evaluate (exps,env,bviProps_inc_clock ck s1) =
      (res,bviProps_inc_clock ck s2))`,
  CHEAT_TAC);;

let do_app_aux_io_events_mono = prove
 (`bviSem_do_app_aux op vs s = SOME (SOME (x,y)) ==> ffi_state_io_events
  (state_ffi
   s) <<= ffi_state_io_events (state_ffi y)`,
  CHEAT_TAC);;

(* do_app_io_events_mono *)
let bviProps_do_app_io_events_mono = prove
 (`bviSem_do_app op vs s1 = Rval (x,s2) ==> ffi_state_io_events
  (state_ffi
   s1) <<= ffi_state_io_events (state_ffi s2)`,
  CHEAT_TAC);;

(* evaluate_io_events_mono *)
let bviProps_evaluate_io_events_mono = prove
 (`!exps env s1 res s2.
    bviSem_evaluate (exps,env,s1) = (res,s2) ==> ffi_state_io_events
      (state_ffi
    s1) <<= ffi_state_io_events (state_ffi s2)`,
  CHEAT_TAC);;

(* do_app_inc_clock[local] *)
let bviProps_do_app_inc_clock = prove
 (`bviSem_do_app op vs (bviProps_inc_clock x y) =
    map_result (\(v,s). (v,state_clock_fupd (K (x + state_clock y))
      s)) I (bviSem_do_app op vs y)`,
  CHEAT_TAC);;

(* dec_clock_1_inc_clock[local] *)
let bviProps_dec_clock_1_inc_clock = prove
 (`~(x = 0) ==> bviSem_dec_clock 1 (bviProps_inc_clock x s) =
  bviProps_inc_clock (x - 1) s`,
  CHEAT_TAC);;

(* dec_clock_1_inc_clock2[local] *)
let bviProps_dec_clock_1_inc_clock2 = prove
 (`~(state_clock
     s = 0) ==> bviSem_dec_clock 1 (bviProps_inc_clock x s) =
       bviProps_inc_clock x (bviSem_dec_clock 1 s)`,
  CHEAT_TAC);;

(* dec_clock_inc_clock[local] *)
let bviProps_dec_clock_inc_clock = prove
 (`~(state_clock s < n) ==> bviSem_dec_clock n (bviProps_inc_clock x
  s) = bviProps_inc_clock x (bviSem_dec_clock n s)`,
  CHEAT_TAC);;

(* [simp] *)
let inc_clock_eq_0 = prove
 (`state_clock
      (bviProps_inc_clock extra s) = 0 <=> state_clock s = 0 /\
        extra = 0`,
  CHEAT_TAC);;

(* evaluate_add_to_clock_io_events_mono *)
let bviProps_evaluate_add_to_clock_io_events_mono = prove
 (`!exps env s extra. ffi_state_io_events (state_ffi
    (SND (bviSem_evaluate (exps,env,s)))) <<= ffi_state_io_events
      (state_ffi
    (SND (bviSem_evaluate (exps,env,bviProps_inc_clock extra s))))`,
  CHEAT_TAC);;

(* take_drop_lem[local] *)
let bviProps_take_drop_lem = prove
 (`!skip env.
     skip < LENGTH env /\
     skip + SUC n <= LENGTH env /\ ~(DROP skip env = []) ==> CONS
       (EL skip env) (TAKE n (DROP (1 + skip) env)) = TAKE (n + 1)
       (DROP skip env)`,
  CHEAT_TAC);;

(* evaluate_genlist_vars *)
let bviProps_evaluate_genlist_vars = prove
 (`!skip env n (st:('c,'ffi)bviSem_state).
    n + skip <= LENGTH env ==>
    bviSem_evaluate (list_of_seq (\arg. db_vars_Var (arg + skip))
      n,env,st) =
    (Rval (TAKE n (DROP skip env)),st)`,
  CHEAT_TAC);;

let bviProps_get_code_labels_def,bviProps_get_code_labels_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`bviProps_get_code_labels (bvi_Var _2:bvi_exp) = {}`;
   `bviProps_get_code_labels (bvi_If e1 e2 e3:bvi_exp) =
  bviProps_get_code_labels e1 UNION bviProps_get_code_labels e2 UNION
  bviProps_get_code_labels e3`;
   `bviProps_get_code_labels (bvi_Let es e:bvi_exp) = UNIONS
  (set_of_list (MAP bviProps_get_code_labels es)) UNION
  bviProps_get_code_labels e`;
   `bviProps_get_code_labels (bvi_Raise e:bvi_exp) =
  bviProps_get_code_labels e`;
   `bviProps_get_code_labels (bvi_Tick e:bvi_exp) =
  bviProps_get_code_labels e`;
   `bviProps_get_code_labels (bvi_Force loc v:bvi_exp) = {loc}`;
   `bviProps_get_code_labels (bvi_Call _4 d es h:bvi_exp) =
        (match d with NONE -> {} | SOME n -> {n}) UNION
        (match h with NONE -> {} | SOME e ->
          bviProps_get_code_labels e) UNION
        UNIONS (set_of_list (MAP bviProps_get_code_labels es))`;
   `bviProps_get_code_labels (bvi_Op op es:bvi_exp) =
  assign_get_code_label op UNION UNIONS (set_of_list (MAP
  bviProps_get_code_labels es))`;
   `bviProps_get_code_labels (bvi_Return es:bvi_exp) = UNIONS
  (set_of_list (MAP bviProps_get_code_labels es))`;
   `bviProps_get_code_labels (bvi_LetCall _5 _6 d es y) =
        {d} UNION bviProps_get_code_labels y UNION UNIONS
          (set_of_list (MAP bviProps_get_code_labels es))`];;

(* HOL4 bviPropsScript.sml:720-721: a theorem that HOL4 states as the
   value of an ML expression: get_code_labels_def *)

let bviProps_good_code_labels_def = new_definition
  `bviProps_good_code_labels p elabs <=>
     UNIONS (set_of_list (MAP (bviProps_get_code_labels o SND o
       SND) p)) SUBSET set_of_list (MAP FST p) UNION elabs`;;

(* --- switching a compiler pass off --------------------------------------

   A pass that is configured off compiles with CURRY I, i.e. the identity.
   It still wraps the incremental compiler with state_cc/state_co, which
   moves one configuration component between the oracle's state and its
   config.  adj_orac below performs that move on a state; it is the BVI
   analogue of closProps' adj_orac_rel.                                    *)

let adj_orac_def = new_definition
  `(adj_orac cc f (s:('a,'ffi)bviSem_state):('b,'ffi)bviSem_state) =
     mk_bviSem_state (bviSem_state_refs s) (bviSem_state_clock s)
       (bviSem_state_global s) cc ((f ## I) o
       bviSem_state_compile_oracle s) (bviSem_state_code s)
       (bviSem_state_ffi s)`;;

let adj_orac_ok_def = new_definition
  `adj_orac_ok cc f (s:('a,'ffi)bviSem_state) <=>
     (!n x y. bviSem_state_compile_oracle s n = (x,y) ==>
       OPTION_MAP (I ## (I ## f)) (bviSem_state_compile s x y) =
         cc (f x) y)`;;

(* [local] *)
let adj_orac_simps = prove
 (`state_clock
     (adj_orac cc f s) = state_clock s /\ state_code
     (adj_orac cc f s) = state_code s /\ state_refs
     (adj_orac cc f s) = state_refs s /\ bviSem_state_global
     (adj_orac cc f s) = bviSem_state_global s /\ state_ffi
     (adj_orac cc f s) = state_ffi s /\
     bviSem_dec_clock n (adj_orac cc f s) = adj_orac cc f
       (bviSem_dec_clock n s) /\
     (state_clock_fupd (K k) (adj_orac cc f s)) = adj_orac cc f
       (state_clock_fupd (K k) s) /\
     (adj_orac_ok cc f (bviSem_dec_clock n s) <=> adj_orac_ok cc f s)
       /\
     (adj_orac_ok cc f (state_clock_fupd (K k) s) <=> adj_orac_ok
       cc f s)`,
  CHEAT_TAC);;

let adj_orac_rel_def = new_definition
  `bviProps_adj_orac_rel cc f (s1:('a,'ffi)bviSem_state)
  (s2:('b,'ffi)bviSem_state) <=>
     adj_orac_ok cc f s1 /\ s2 = adj_orac cc f s1`;;

(* [local] *)
let do_app_cfg_swap = prove
 (`~(op = closLang_Install) ==>
       ((bviSem_do_app op args s = Rval (value,s1) /\
         domain (state_code s) SUBSET domain (state_code t) ==>
         bviSem_do_app op args
           (state_ffi_fupd (K (state_ffi s))
             (bviSem_state_global_fupd (K (bviSem_state_global s))
             (state_clock_fupd (K (state_clock s)) (state_refs_fupd (K
             (state_refs s)) t)))) =
         Rval
           (value,state_ffi_fupd (K (state_ffi s1))
             (bviSem_state_global_fupd (K (bviSem_state_global s1))
             (state_clock_fupd (K (state_clock s1)) (state_refs_fupd (K
             (state_refs s1))
            t))))) /\
        (bviSem_do_app op args s = Rerr error /\
         (domain (state_code t) SUBSET domain (state_code s) \/
           ~(error = Rabort Rtype_error)) ==>
         bviSem_do_app op args
           (state_ffi_fupd (K (state_ffi s))
             (bviSem_state_global_fupd (K (bviSem_state_global s))
             (state_clock_fupd (K (state_clock s)) (state_refs_fupd (K
             (state_refs s)) t)))) =
         Rerr error))`,
  CHEAT_TAC);;

(* [local] *)
let do_app_cfg_swap_Rval = prove
 (`!op args (s) (s1)
       (t) value. ~(op = closLang_Install) /\ domain
         (bviSem_state_code s) = domain (bviSem_state_code t) /\
     bviSem_do_app op args s = Rval (value,s1) ==>
     bviSem_do_app op args
       (bviSem_state_ffi_fupd (K (bviSem_state_ffi s))
         (bviSem_state_global_fupd (K (bviSem_state_global s))
         (bviSem_state_clock_fupd (K (bviSem_state_clock s))
         (bviSem_state_refs_fupd (K (bviSem_state_refs s)) t)))) =
     Rval (value,bviSem_state_ffi_fupd (K (bviSem_state_ffi s1))
       (bviSem_state_global_fupd (K (bviSem_state_global s1))
       (bviSem_state_clock_fupd (K (bviSem_state_clock s1))
       (bviSem_state_refs_fupd (K (bviSem_state_refs s1)) t))))`,
  CHEAT_TAC);;

(* [local] *)
let do_app_cfg_swap_Rerr = prove
 (`!op args (s) (t) error'. ~(op = closLang_Install) /\ domain
  (bviSem_state_code s) = domain (bviSem_state_code t) /\
     bviSem_do_app op args s = Rerr error' ==>
     bviSem_do_app op args
       (bviSem_state_ffi_fupd (K (bviSem_state_ffi s))
         (bviSem_state_global_fupd (K (bviSem_state_global s))
         (bviSem_state_clock_fupd (K (bviSem_state_clock s))
         (bviSem_state_refs_fupd (K (bviSem_state_refs s)) t)))) =
         Rerr error'`,
  CHEAT_TAC);;

(* [local] *)
let do_install_Rerr_type = prove
 (`bviSem_do_install args s = Rerr e ==> e = Rabort Rtype_error`,
  CHEAT_TAC);;

(* [local] *)
let do_install_adj_orac = prove
 (`!args (s) v t cc (f).
     adj_orac_ok cc f s /\
     (bviSem_do_install args s) =
       Rval (v,t) ==>
     (bviSem_do_install args (adj_orac cc f s)) =
       Rval (v,adj_orac cc f t) /\
     adj_orac_ok cc f t`,
  CHEAT_TAC);;

(* [local] *)
let do_app_adj_orac = prove
 (`adj_orac_ok cc f s ==>
     (!v t. bviSem_do_app op args s = Rval (v,t) ==>
        bviSem_do_app op args (adj_orac cc f s) = Rval (v,adj_orac cc
          f t) /\
        adj_orac_ok cc f t) /\
     (!e. bviSem_do_app op args s = Rerr e /\ ~(e = Rabort
       Rtype_error) ==>
        bviSem_do_app op args (adj_orac cc f s) = Rerr e)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_adj_orac_rel = prove
 (`!xs env (s).
     !res t1 cc f (s2).
       bviSem_evaluate (xs,env,s) = (res,t1) /\ ~(res = Rerr (Rabort
         Rtype_error)) /\
       bviProps_adj_orac_rel cc f s s2 ==>
       (?t2. bviSem_evaluate (xs,env,s2) = (res,t2) /\
         bviProps_adj_orac_rel cc f t1 t2)`,
  CHEAT_TAC);;

let evaluate_adj_orac = prove
 (`bviSem_evaluate (xs,env,(s:('a,'ffi)bviSem_state)) = (res,t1) /\
  ~(res = Rerr (Rabort Rtype_error)) /\
   adj_orac_ok cc (f:'a->'b) s ==>
   bviSem_evaluate (xs,env,adj_orac cc f s) = (res,adj_orac cc f t1)
     /\
   adj_orac_ok cc f t1`,
  CHEAT_TAC);;

(* [local] *)
let adj_orac_initial_state = prove
 (`adj_orac cc SND (bviSem_initial_state ffi code co (state_cc (CURRY I)
  cc) k) =
   bviSem_initial_state ffi code (state_co (CURRY I) co) cc k`,
  CHEAT_TAC);;

(* [local] *)
let adj_orac_ok_initial_state = prove
 (`adj_orac_ok cc SND (bviSem_initial_state ffi code co (state_cc
  (CURRY I) cc) k)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_CURRY_I = prove
 (`bviSem_evaluate (es,env,bviSem_initial_state ffi code co (state_cc
  (CURRY I) cc) k) = (r,s) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
   (?s2.
     bviSem_evaluate (es,env,bviSem_initial_state ffi code (state_co
       (CURRY I) co) cc k) =
       (r,s2) /\ state_ffi s2 = state_ffi s)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let semantics_CURRY_I = prove
 (cake_as_vars (fun () ->
    `~(bviSem_semantics ffi code co (state_cc (CURRY I) cc) start =
  ffi_Fail) ==>
       bviSem_semantics ffi code co (state_cc (CURRY I) cc) start =
       bviSem_semantics ffi code (state_co (CURRY I) co) cc start`),
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["error"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
