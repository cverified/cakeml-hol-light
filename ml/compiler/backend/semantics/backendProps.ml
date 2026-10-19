(* ======================================================== *)
(*  backendProps: ported from HOL4's
    compiler/backend/semantics/backendPropsScript.sml
    A proof theory about backend.ml, with 14 definitions and 49
    theorems.  Needed by 34 files of the port.  *)
(* ======================================================== *)

(*
  General definitions and theorems that are useful within the proofs
  about the compiler backend.
*)

needs "misc/misc.ml";;
needs "semantics/typeSystem.ml";;

let state_cc_def = cake_define
  `state_cc f cc =
     (\(state,cfg) prog.
        let (state1,prog1) = f state prog in
          match cc cfg prog1 with NONE -> NONE | SOME
            (code,data,cfg1) -> SOME (code,data,state1,cfg1))`;;

let pure_cc_def = cake_define
  `pure_cc f cc =
     (\cfg prog.
        let prog1 = f prog in
          cc cfg prog1)`;;

let state_co_def = cake_define
  `state_co f co =
      (\n.
         (let
            ((state,cfg),progs) = co n in let
            (state1,progs) = f state progs in
            (cfg,progs)))`;;

let FST_state_co = cake_theorem "FST_state_co"
  (fun () ->
    `FST (state_co f co n) = SND (FST (co n))`)
  CHEAT_TAC;;

let SND_state_co = cake_theorem "SND_state_co"
  (fun () ->
    `SND (state_co f co n) = SND (f (FST (FST (co n))) (SND (co n)))`)
  CHEAT_TAC;;

let the_eqn = cake_theorem "the_eqn"
  (fun () ->
    `the x y = (match y with NONE -> x | SOME z -> z)`)
  CHEAT_TAC;;

let the_F_eq = cake_theorem "the_F_eq"
  (fun () ->
    `the F opt = (?x. (opt = SOME x) /\ x)`)
  CHEAT_TAC;;

let pure_co_def = cake_define
  `pure_co f = I ## f`;;

let SND_pure_co = cake_theorem "SND_pure_co[simp]"
  (fun () ->
    `SND (pure_co co x) = co (SND x)`)
  CHEAT_TAC;;

let FST_pure_co = cake_theorem "FST_pure_co[simp]"
  (fun () ->
    `FST (pure_co co x) = FST x`)
  CHEAT_TAC;;

let pure_co_comb_pure_co = cake_theorem "pure_co_comb_pure_co"
  (fun () ->
    `pure_co f o pure_co g o co = pure_co (f o g) o co`)
  CHEAT_TAC;;

let pure_co_I = cake_theorem "pure_co_I"
  (fun () ->
    `pure_co I = I`)
  CHEAT_TAC;;

let pure_cc_I = cake_theorem "pure_cc_I"
  (fun () ->
    `pure_cc I = I`)
  CHEAT_TAC;;

(* somewhat generic wrappers for defining standard properties about oracles *)

(* identifiers that appear in the initial state and in oracle steps
   increase monotonically in some sense. *)
let oracle_monotonic_def = cake_define
  `oracle_monotonic (f:'a->'b->bool) (R:'b->'b->bool) (S:'b->bool)
  (orac:num->'a) =
     (
         (!i j x y. i < j /\ x IN f (orac i) /\ y IN f (orac j)
           ==> R x y) /\ (!i x y. x IN S /\ y IN f (orac i) ==> R x
           y))`;;

(* HOL4 backendPropsScript.sml:108-109: ML code, not ported *)

(* HOL4 backendPropsScript.sml:111: a theorem that HOL4 states as the
   value of an ML expression: oracle_monotonic_step *)
(* HOL4 backendPropsScript.sml:112: a theorem that HOL4 states as the
   value of an ML expression: oracle_monotonic_init *)

let oracle_monotonic_step2 = cake_theorem "oracle_monotonic_step2"
  (fun () ->
    `oracle_monotonic f R St orac ==>
        (!i j x y. x IN f (orac i) /\ y IN f (orac j) /\ i < j
          ==> R x y)`)
  CHEAT_TAC;;

let oracle_monotonic_subset = cake_theorem "oracle_monotonic_subset"
  (fun () ->
    `((St' SUBSET St) /\ (!n. f' (co' n) SUBSET f (co n))) ==>
     oracle_monotonic f R St co ==>
     oracle_monotonic f' R St' co'`)
  CHEAT_TAC;;

let oracle_monotonic_shift_subset =
  cake_theorem "oracle_monotonic_shift_subset"
  (fun () ->
    `((St' SUBSET (IMAGE ((+) (i:num)) St UNION count i)) /\
       (!n. f' (co' n) SUBSET (IMAGE ((+) i) (f (co n))))) ==>
     oracle_monotonic f (<) St co ==>
     oracle_monotonic f' (<) St' co'`)
  CHEAT_TAC;;

let oracle_monotonic_shift_seq =
  cake_theorem "oracle_monotonic_shift_seq"
  (fun () ->
    `!i. (oracle_monotonic f R St co /\ i > 0 /\
       St' SUBSET f (co (i - 1)) UNION St ==>
       oracle_monotonic f R St' (misc_shift_seq i co))`)
  CHEAT_TAC;;

let oracle_monotonic_DISJOINT_init =
  cake_theorem "oracle_monotonic_DISJOINT_init"
  (fun () ->
    `!i.
       oracle_monotonic f R St co /\ irreflexive R ==> DISJOINT
         St (f (co i))`)
  CHEAT_TAC;;

(* check that an oracle with config values lists the config values that
   would be produced by the incremental compiler. *)
let is_state_oracle_def = cake_define
  `is_state_oracle compile_inc_f co =
     (!n.
         FST (FST (co (SUC n))) = FST (compile_inc_f (FST (FST (co
           n))) (SND (co n))))`;;

let is_state_oracle_shift = cake_theorem "is_state_oracle_shift"
  (fun () ->
    `is_state_oracle compile_inc_f co =
     (is_state_oracle compile_inc_f (misc_shift_seq 1 co) /\
           FST (FST (co 1)) = FST (compile_inc_f (FST (FST (co
             0))) (SND (co 0))))`)
  CHEAT_TAC;;

let is_state_oracle_shift_imp = cake_theorem "is_state_oracle_shift_imp"
  (fun () ->
    `is_state_oracle compile_inc_f co ==>
     is_state_oracle compile_inc_f (misc_shift_seq n co)`)
  CHEAT_TAC;;

let is_state_oracle_k = cake_theorem "is_state_oracle_k"
  (fun () ->
    `!k. is_state_oracle compile_inc_f co ==>
     (?st oth_st prog.
       co k = ((st,oth_st),prog) /\ FST (FST (co (SUC k))) = FST
         (compile_inc_f st prog))`)
  CHEAT_TAC;;

(* constructive combinators for building up the config part of an oracle *)

let syntax_to_full_oracle_def = cake_define
  `syntax_to_full_oracle mk progs i = (mk progs i,progs i)`;;

let state_orac_states_def = cake_define_list
  [`state_orac_states f st progs 0 = st`;
   `state_orac_states f st progs (SUC n) =
      FST (f (state_orac_states f st progs n) (progs n))`];;

let state_co_progs_def = cake_define
  `state_co_progs f st orac = (let
     states = state_orac_states f st orac in \i. SND (f (states i)
       (orac i)))`;;

let add_state_co_def = cake_define
  `add_state_co f st mk progs = (let
     states = state_orac_states f st progs in let
     next_progs = state_co_progs f st progs in let
     next_orac = mk next_progs in
     (\i. (states i,next_orac i)))`;;

let state_co_add_state_co = cake_theorem "state_co_add_state_co"
  (fun () ->
    `state_co f (syntax_to_full_oracle (add_state_co f st mk) progs) =
  syntax_to_full_oracle mk (state_co_progs f st progs)`)
  CHEAT_TAC;;

let pure_co_progs_def = cake_define
  `pure_co_progs f (orac:num->'a) = f o orac`;;

let pure_co_syntax_to_full_oracle =
  cake_theorem "pure_co_syntax_to_full_oracle"
  (fun () ->
    `pure_co f o (syntax_to_full_oracle (mk o pure_co_progs f) progs) =
       syntax_to_full_oracle mk (pure_co_progs f progs)`)
  CHEAT_TAC;;

let syntax_to_full_oracle_o_assoc =
  cake_theorem "syntax_to_full_oracle_o_assoc"
  (fun () ->
    `syntax_to_full_oracle (f o g o h) progs =
     syntax_to_full_oracle ((f o g) o h) progs`)
  CHEAT_TAC;;

let oracle_monotonic_SND_syntax_to_full =
  cake_theorem "oracle_monotonic_SND_syntax_to_full"
  (fun () ->
    `oracle_monotonic (f o SND) R St (syntax_to_full_oracle mk progs) =
     oracle_monotonic (f o SND) R St (I syntax_to_full_oracle I
       progs) /\
     oracle_monotonic (a o b o c) = oracle_monotonic ((a o b) o
       c)`)
  CHEAT_TAC;;

let is_state_oracle_add_state_co =
  cake_theorem "is_state_oracle_add_state_co"
  (fun () ->
    `is_state_oracle f (syntax_to_full_oracle (add_state_co f st mk)
  progs)`)
  CHEAT_TAC;;

(* HOL4 backendPropsScript.sml:283-287: a theorem that HOL4 states as
   the value of an ML expression: syntax_oracle_unpack *)

let FST_add_state_co_0 = cake_theorem "FST_add_state_co_0"
  (fun () ->
    `FST (add_state_co f st mk orac 0) = st`)
  CHEAT_TAC;;

let state_orac_states_inv = cake_theorem "state_orac_states_inv"
  (fun () ->
    `P st /\
     (!st prog st' prog'. f_inc st prog = (st',prog') /\ P st ==> P
       st') ==>
     P (state_orac_states f_inc st orac i)`)
  CHEAT_TAC;;

let oracle_monotonic_state_with_inv =
  cake_theorem "oracle_monotonic_state_with_inv"
  (fun () ->
    `!P n_f. P (FST (FST (orac 0))) /\
     (!x. x IN St ==> x < n_f (FST (FST (orac 0)))) /\
     (!st prog st' prog'. f_inc st prog = (st',prog') /\ P st ==>
       P st' /\ n_f st <= n_f st' /\
       (!cfg x. x IN f (cfg,prog') ==> n_f st <= x /\ x < n_f st'))
         /\
     is_state_oracle f_inc orac ==>
     oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`)
  CHEAT_TAC;;

let oracle_monotonic_state_with_inv_init =
  cake_theorem "oracle_monotonic_state_with_inv_init"
  (fun () ->
    `!P n_f. f_inc st0 prog0 = (st,prog) /\ P st0 /\
     St SUBSET f (cfg,prog) /\ FST (FST (orac 0)) = st /\
     (!st prog st' prog'. f_inc st prog = (st',prog') /\ P st ==>
       P st' /\ n_f st <= n_f st' /\
       (!cfg x. x IN f (cfg,prog') ==> n_f st <= x /\ x < n_f st'))
         /\
     is_state_oracle f_inc orac ==>
     oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`)
  CHEAT_TAC;;

(* HOL4 backendPropsScript.sml:348-349: a theorem that HOL4 states as
   the value of an ML expression: oracle_monotonic_state *)

(* HOL4 backendPropsScript.sml:351-352: a theorem that HOL4 states as
   the value of an ML expression: oracle_monotonic_state_init *)

let restrict_zero_def = cake_define
  `restrict_zero (labels:num#num->bool) =
     {l | l IN labels /\ SND l = 0}`;;

let restrict_nonzero_def = cake_define
  `restrict_nonzero (labels:num#num->bool) =
     {l | l IN labels /\ ~(SND l = 0)}`;;

let restrict_nonzero_SUBSET = cake_theorem "restrict_nonzero_SUBSET"
  (fun () ->
    `restrict_nonzero l SUBSET l`)
  CHEAT_TAC;;

let restrict_nonzero_SUBSET_left =
  cake_theorem "restrict_nonzero_SUBSET_left"
  (fun () ->
    `s SUBSET t ==>
     restrict_nonzero s SUBSET t`)
  CHEAT_TAC;;

let restrict_nonzero_left_union =
  cake_theorem "restrict_nonzero_left_union"
  (fun () ->
    `restrict_nonzero s SUBSET a UNION b ==>
     restrict_nonzero s SUBSET restrict_nonzero a UNION b`)
  CHEAT_TAC;;

let restrict_nonzero_right_union =
  cake_theorem "restrict_nonzero_right_union"
  (fun () ->
    `restrict_nonzero s SUBSET a UNION b ==>
     restrict_nonzero s SUBSET a UNION restrict_nonzero b`)
  CHEAT_TAC;;

let restrict_nonzero_mono = cake_theorem "restrict_nonzero_mono"
  (fun () ->
    `s SUBSET t ==>
     restrict_nonzero s SUBSET restrict_nonzero t`)
  CHEAT_TAC;;

let restrict_nonzero_BIGUNION = cake_theorem "restrict_nonzero_BIGUNION"
  (fun () ->
    `restrict_nonzero (BIGUNION ss) = BIGUNION (IMAGE restrict_nonzero
  ss)`)
  CHEAT_TAC;;

let option_le_def = cake_define
  `option_le x1 x2 =
      match (x1,x2) with
        (_1,NONE) -> T
      | (NONE,(SOME _2)) -> F
      | ((SOME n1),(SOME n2)) -> (n1 <= (n2:num))`;;

let option_le_refl = cake_theorem "option_le_refl[simp]"
  (fun () ->
    `!x. option_le x x`)
  CHEAT_TAC;;

let option_le_SOME_0 = cake_theorem "option_le_SOME_0[simp]"
  (fun () ->
    `option_le (SOME 0) x`)
  CHEAT_TAC;;

let option_le_trans = cake_theorem "option_le_trans"
  (fun () ->
    `!x y z. option_le x y /\ option_le y z ==> option_le x z`)
  CHEAT_TAC;;

let option_le_max = cake_theorem "option_le_max"
  (fun () ->
    `option_le (OPTION_MAP2 MAX n m) x <=> option_le n x /\ option_le
  m x`)
  CHEAT_TAC;;

let option_le_max_right = cake_theorem "option_le_max_right"
  (fun () ->
    `option_le x (OPTION_MAP2 MAX n m) <=> option_le x n \/ option_le
  x m`)
  CHEAT_TAC;;

let option_add_comm = cake_theorem "option_add_comm"
  (fun () ->
    `OPTION_MAP2 (+) (n:num option) m = OPTION_MAP2 ((+)) m n`)
  CHEAT_TAC;;

let option_add_assoc = cake_theorem "option_add_assoc"
  (fun () ->
    `OPTION_MAP2 (+) (n:num option) (OPTION_MAP2 ((+)) m p) =
  OPTION_MAP2 ((+)) (OPTION_MAP2 ((+)) n m) p`)
  CHEAT_TAC;;

let option_le_eq_eqns = cake_theorem "option_le_eq_eqns"
  (fun () ->
    `(
      option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) n p) <=> (n
        = NONE \/ option_le m p)) /\
     (
      option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) p n) <=> (n
        = NONE \/ option_le m p)) /\
     (
      option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) p m) <=> (m
        = NONE \/ option_le n p)) /\
     (
      option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) m p) <=>
        (m = NONE \/ option_le n p))`)
  CHEAT_TAC;;

let option_map2_max_add = cake_theorem "option_map2_max_add"
  (fun () ->
    `(OPTION_MAP2 (+) n (OPTION_MAP2 MAX m p) =
      OPTION_MAP2 MAX (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) n p))
        /\
     (OPTION_MAP2 (+) (OPTION_MAP2 MAX m p) n =
      OPTION_MAP2 MAX (OPTION_MAP2 (+) m n) (OPTION_MAP2 (+) p
        n))`)
  CHEAT_TAC;;

let option_le_add = cake_theorem "option_le_add"
  (fun () ->
    `option_le n (OPTION_MAP2 (+) n m)`)
  CHEAT_TAC;;

let OPTION_MAP2_MAX_COMM = cake_theorem "OPTION_MAP2_MAX_COMM"
  (fun () ->
    `OPTION_MAP2 MAX x y = OPTION_MAP2 MAX y x`)
  CHEAT_TAC;;

let OPTION_MAP2_MAX_ASSOC = cake_theorem "OPTION_MAP2_MAX_ASSOC"
  (fun () ->
    `OPTION_MAP2 MAX x (OPTION_MAP2 MAX y z) =
     OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) z`)
  CHEAT_TAC;;
