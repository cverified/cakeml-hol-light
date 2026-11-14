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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "backendProps"
  ["misc"];;

let state_cc_def = new_definition
  `state_cc f cc =
     (\(state,cfg) prog.
        let (state1,prog1) = f state prog in
          match cc cfg prog1 with NONE -> NONE | SOME
            (code,data,cfg1) -> SOME (code,data,state1,cfg1))`;;

let pure_cc_def = new_definition
  `pure_cc f cc =
     (\cfg prog.
        let prog1 = f prog in
          cc cfg prog1)`;;

let state_co_def = new_definition
  `state_co f co =
      (\n.
         (let
            ((state,cfg),progs) = co n in let
            (state1,progs) = f state progs in
            (cfg,progs)))`;;

let FST_state_co = prove
 (`FST (state_co f co n) = SND (FST (co n))`,
  CHEAT_TAC);;

let SND_state_co = prove
 (`SND (state_co f co n) = SND (f (FST (FST (co n))) (SND (co n)))`,
  CHEAT_TAC);;

let the_eqn = prove
 (`the x y = (match y with NONE -> x | SOME z -> z)`,
  CHEAT_TAC);;

let the_F_eq = prove
 (`the F opt = (?x. (opt = SOME x) /\ x)`,
  CHEAT_TAC);;

let pure_co_def = new_definition
  `pure_co f = I ## f`;;

(* [simp] *)
let SND_pure_co = prove
 (`SND (pure_co co x) = co (SND x)`,
  (CASES_ON_TAC `x:C#P` THEN REWRITE_TAC[pure_co_def; PAIR_MAP_THM;
    SND]));;

(* [simp] *)
let FST_pure_co = prove
 (`FST (pure_co co x) = FST x`,
  (CASES_ON_TAC `x:C#P` THEN REWRITE_TAC[pure_co_def; PAIR_MAP_THM;
    FST; I_THM]));;

let pure_co_comb_pure_co = prove
 (`pure_co f o pure_co g o co = pure_co (f o g) o co`,
  (REWRITE_TAC[FUN_EQ_THM; o_THM; pure_co_def] THEN GEN_TAC THEN
   CASES_ON_TAC `(co:A->C#P) x` THEN REWRITE_TAC[PAIR_MAP_THM; I_THM;
     o_THM]));;

let pure_co_I = prove
 (`pure_co I = I`,
  (REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; pure_co_def;
    PAIR_MAP_THM; I_THM]));;

let pure_cc_I = prove
 (`pure_cc I = I`,
  (REWRITE_TAC[FUN_EQ_THM; pure_cc_def; I_THM; LET_DEF; LET_END_DEF]));;

(* somewhat generic wrappers for defining standard properties about oracles *)

(* identifiers that appear in the initial state and in oracle steps
   increase monotonically in some sense. *)
let oracle_monotonic_def = new_definition
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

let oracle_monotonic_step2 = prove
 (`oracle_monotonic f R St orac ==>
      (!i j x y. x IN f (orac i) /\ y IN f (orac j) /\ i < j ==> R
        x y)`,
  CHEAT_TAC);;

let oracle_monotonic_subset = prove
 (`((St' SUBSET St) /\ (!n. f' (co' n) SUBSET f (co n))) ==>
   oracle_monotonic f R St co ==>
   oracle_monotonic f' R St' co'`,
  (REWRITE_TAC[oracle_monotonic_def; SUBSET] THEN MESON_TAC[]));;

let oracle_monotonic_shift_subset = prove
 (`((St' SUBSET (IMAGE ((+) (i:num)) St UNION count i)) /\
     (!n. f' (co' n) SUBSET (IMAGE ((+) i) (f (co n))))) ==>
   oracle_monotonic f (<) St co ==>
   oracle_monotonic f' (<) St' co'`,
  (REWRITE_TAC[oracle_monotonic_def; SUBSET; IN_UNION; IN_IMAGE;
    count_def;
               IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THENL
    [SUBGOAL_THEN `?x0. x = i + x0 /\ x0 IN (f:A->num->bool)
      ((co:num->A) i')`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `?y0. y = i + y0 /\ y0 IN (f:A->num->bool)
       ((co:num->A) j)`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN ASM_MESON_TAC[];
     SUBGOAL_THEN `?y0. y = i + y0 /\ y0 IN (f:A->num->bool)
       ((co:num->A) i')`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `(?x0. x = i + x0 /\ x0 IN St) \/ x < i`
       STRIP_ASSUME_TAC THENL
      [ASM_MESON_TAC[];
       ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN ASM_MESON_TAC[];
       ASM_ARITH_TAC]]));;

let oracle_monotonic_shift_seq = prove
 (`!i. (oracle_monotonic f R St co /\ i > 0 /\
     St' SUBSET f (co (i - 1)) UNION St ==>
     oracle_monotonic f R St' (misc_shift_seq i co))`,
  CHEAT_TAC);;

let oracle_monotonic_DISJOINT_init = prove
 (`!i.
     oracle_monotonic f R St co /\ irreflexive R ==> DISJOINT St (f
       (co i))`,
  CHEAT_TAC);;

(* check that an oracle with config values lists the config values that
   would be produced by the incremental compiler. *)
let is_state_oracle_def = new_definition
  `is_state_oracle compile_inc_f co =
     (!n.
         FST (FST (co (SUC n))) = FST (compile_inc_f (FST (FST (co
           n))) (SND (co n))))`;;

let is_state_oracle_shift = prove
 (`is_state_oracle compile_inc_f co =
   (is_state_oracle compile_inc_f (misc_shift_seq 1 co) /\
         FST (FST (co 1)) = FST (compile_inc_f (FST (FST (co 0)))
           (SND (co 0))))`,
  (REWRITE_TAC[is_state_oracle_def; shift_seq_def; GSYM ADD1] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL
    [ASM_REWRITE_TAC[];
     ASM_REWRITE_TAC[ONE];
     STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
       ASM_REWRITE_TAC[GSYM ONE]]));;

let is_state_oracle_shift_imp = prove
 (`is_state_oracle compile_inc_f co ==>
   is_state_oracle compile_inc_f (misc_shift_seq n co)`,
  (REWRITE_TAC[is_state_oracle_def; shift_seq_def; ADD_CLAUSES] THEN
   SIMP_TAC[]));;

let is_state_oracle_k = prove
 (`!k. is_state_oracle compile_inc_f co ==>
   (?st oth_st prog.
     co k = ((st,oth_st),prog) /\ FST (FST (co (SUC k))) = FST
       (compile_inc_f st prog))`,
  CHEAT_TAC);;

(* constructive combinators for building up the config part of an oracle *)

let syntax_to_full_oracle_def = new_definition
  `syntax_to_full_oracle mk progs i = (mk progs i,progs i)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let state_orac_states_def,state_orac_states_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). (\n. n) x3)`
  [`state_orac_states f st progs 0 = st`;
   `state_orac_states f st progs (SUC n) =
      FST (f (state_orac_states f st progs n) (progs n))`];;

let state_co_progs_def = new_definition
  `state_co_progs f st orac = (let
     states = state_orac_states f st orac in \i. SND (f (states i)
       (orac i)))`;;

let add_state_co_def = new_definition
  `add_state_co f st mk progs = (let
     states = state_orac_states f st progs in let
     next_progs = state_co_progs f st progs in let
     next_orac = mk next_progs in
     (\i. (states i,next_orac i)))`;;

let state_co_add_state_co = prove
 (`state_co f (syntax_to_full_oracle (add_state_co f st mk) progs) =
  syntax_to_full_oracle mk (state_co_progs f st progs)`,
  CHEAT_TAC);;

let pure_co_progs_def = new_definition
  `pure_co_progs f (orac:num->'a) = f o orac`;;

let pure_co_syntax_to_full_oracle = prove
 (`pure_co f o (syntax_to_full_oracle (mk o pure_co_progs f) progs) =
     syntax_to_full_oracle mk (pure_co_progs f progs)`,
  CHEAT_TAC);;

let syntax_to_full_oracle_o_assoc = prove
 (`syntax_to_full_oracle (f o g o h) progs =
   syntax_to_full_oracle ((f o g) o h) progs`,
  CHEAT_TAC);;

let oracle_monotonic_SND_syntax_to_full = prove
 (`oracle_monotonic (f o SND) R St (syntax_to_full_oracle mk progs) =
   oracle_monotonic (f o SND) R St (I syntax_to_full_oracle I progs)
     /\
   oracle_monotonic (a o b o c) = oracle_monotonic ((a o b) o c)`,
  CHEAT_TAC);;

let is_state_oracle_add_state_co = prove
 (`is_state_oracle f (syntax_to_full_oracle (add_state_co f st mk)
  progs)`,
  CHEAT_TAC);;

(* HOL4 backendPropsScript.sml:283-287: a theorem that HOL4 states as
   the value of an ML expression: syntax_oracle_unpack *)

let FST_add_state_co_0 = prove
 (`FST (add_state_co f st mk orac 0) = st`,
  CHEAT_TAC);;

let state_orac_states_inv = prove
 (`P st /\
   (!st prog st' prog'. f_inc st prog = (st',prog') /\ P st ==> P
     st') ==>
   P (state_orac_states f_inc st orac i)`,
  CHEAT_TAC);;

let oracle_monotonic_state_with_inv = prove
 (`!P n_f. P (FST (FST (orac 0))) /\
   (!x. x IN St ==> x < n_f (FST (FST (orac 0)))) /\
   (!st prog st' prog'. f_inc st prog = (st',prog') /\ P st ==>
     P st' /\ n_f st <= n_f st' /\
     (!cfg x. x IN f (cfg,prog') ==> n_f st <= x /\ x < n_f st')) /\
   is_state_oracle f_inc orac ==>
   oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  CHEAT_TAC);;

let oracle_monotonic_state_with_inv_init = prove
 (`!P n_f. f_inc st0 prog0 = (st,prog) /\ P st0 /\
   St SUBSET f (cfg,prog) /\ FST (FST (orac 0)) = st /\
   (!st prog st' prog'. f_inc st prog = (st',prog') /\ P st ==>
     P st' /\ n_f st <= n_f st' /\
     (!cfg x. x IN f (cfg,prog') ==> n_f st <= x /\ x < n_f st')) /\
   is_state_oracle f_inc orac ==>
   oracle_monotonic f (<) (St:num->bool) (state_co f_inc orac)`,
  (REPEAT GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC oracle_monotonic_state_with_inv THEN
   MAP_EVERY EXISTS_TAC [`P:S->bool`; `n_f:S->num`] THEN
   FIRST_ASSUM(MP_TAC o SPECL [`st0:S`; `prog0:Q`; `st:S`; `prog:R`]
     o
     check (is_forall o concl)) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]));;

(* HOL4 backendPropsScript.sml:348-349: a theorem that HOL4 states as
   the value of an ML expression: oracle_monotonic_state *)

(* HOL4 backendPropsScript.sml:351-352: a theorem that HOL4 states as
   the value of an ML expression: oracle_monotonic_state_init *)

let restrict_zero_def = new_definition
  `restrict_zero (labels:num#num->bool) =
     {l | l IN labels /\ SND l = 0}`;;

let restrict_nonzero_def = new_definition
  `restrict_nonzero (labels:num#num->bool) =
     {l | l IN labels /\ ~(SND l = 0)}`;;

let restrict_nonzero_SUBSET = prove
 (`restrict_nonzero l SUBSET l`,
  (REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[]));;

let restrict_nonzero_SUBSET_left = prove
 (`s SUBSET t ==>
   restrict_nonzero s SUBSET t`,
  (MESON_TAC[restrict_nonzero_SUBSET; SUBSET_TRANS]));;

let restrict_nonzero_left_union = prove
 (`restrict_nonzero s SUBSET a UNION b ==>
   restrict_nonzero s SUBSET restrict_nonzero a UNION b`,
  (REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_UNION; IN_ELIM_THM]
    THEN
   MESON_TAC[]));;

let restrict_nonzero_right_union = prove
 (`restrict_nonzero s SUBSET a UNION b ==>
   restrict_nonzero s SUBSET a UNION restrict_nonzero b`,
  (REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_UNION; IN_ELIM_THM]
    THEN
   MESON_TAC[]));;

let restrict_nonzero_mono = prove
 (`s SUBSET t ==>
   restrict_nonzero s SUBSET restrict_nonzero t`,
  (REWRITE_TAC[restrict_nonzero_def; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[]));;

let restrict_nonzero_BIGUNION = prove
 (`restrict_nonzero (UNIONS ss) = UNIONS (IMAGE restrict_nonzero ss)`,
  (REWRITE_TAC[restrict_nonzero_def; EXTENSION; IN_UNIONS;
    EXISTS_IN_IMAGE;
               IN_ELIM_THM] THEN
   MESON_TAC[]));;

let option_le_def = new_definition
  `option_le x1 x2 =
      match (x1,x2) with
        (_1,NONE) -> T
      | (NONE,(SOME _2)) -> F
      | ((SOME n1),(SOME n2)) -> (n1 <= (n2:num))`;;

(* [simp] *)
let option_le_refl = prove
 (`!x. option_le x x`,
  CHEAT_TAC);;

(* [simp] *)
let option_le_SOME_0 = prove
 (`option_le (SOME 0) x`,
  CHEAT_TAC);;

let option_le_trans = prove
 (`!x y z. option_le x y /\ option_le y z ==> option_le x z`,
  CHEAT_TAC);;

let option_le_max = prove
 (`option_le (OPTION_MAP2 MAX n m) x <=> option_le n x /\ option_le m
  x`,
  CHEAT_TAC);;

let option_le_max_right = prove
 (`option_le x (OPTION_MAP2 MAX n m) <=> option_le x n \/ option_le x
  m`,
  CHEAT_TAC);;

let option_add_comm = prove
 (`OPTION_MAP2 (+) (n:num option) m = OPTION_MAP2 ((+)) m n`,
  CHEAT_TAC);;

let option_add_assoc = prove
 (`OPTION_MAP2 (+) (n:num option) (OPTION_MAP2 ((+)) m p) =
  OPTION_MAP2 ((+)) (OPTION_MAP2 ((+)) n m) p`,
  CHEAT_TAC);;

let option_le_eq_eqns = prove
 (`(
    option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) n p) <=> (n =
      NONE \/ option_le m p)) /\
   (
    option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) p n) <=> (n =
      NONE \/ option_le m p)) /\
   (
    option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) p m) <=> (m =
      NONE \/ option_le n p)) /\
   (
    option_le (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) m p) <=> (m =
      NONE \/ option_le n p))`,
  CHEAT_TAC);;

let option_map2_max_add = prove
 (`(OPTION_MAP2 (+) n (OPTION_MAP2 MAX m p) =
    OPTION_MAP2 MAX (OPTION_MAP2 (+) n m) (OPTION_MAP2 (+) n p)) /\
   (OPTION_MAP2 (+) (OPTION_MAP2 MAX m p) n =
    OPTION_MAP2 MAX (OPTION_MAP2 (+) m n) (OPTION_MAP2 (+) p n))`,
  CHEAT_TAC);;

let option_le_add = prove
 (`option_le n (OPTION_MAP2 (+) n m)`,
  CHEAT_TAC);;

let OPTION_MAP2_MAX_COMM = prove
 (`OPTION_MAP2 MAX x y = OPTION_MAP2 MAX y x`,
  CHEAT_TAC);;

let OPTION_MAP2_MAX_ASSOC = prove
 (`OPTION_MAP2 MAX x (OPTION_MAP2 MAX y z) =
   OPTION_MAP2 MAX (OPTION_MAP2 MAX x y) z`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
