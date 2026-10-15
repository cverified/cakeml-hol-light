(* ======================================================== *)
(*  backendProps: ported from HOL4's
    compiler/backend/semantics/backendPropsScript.sml  *)
(* ======================================================== *)

(*
  General definitions and theorems that are useful within the proofs
  about the compiler backend.
*)

needs "misc/misc.ml";;

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

let pure_co_def = cake_define
  `pure_co f = I ## f`;;

(* somewhat generic wrappers for defining standard properties about
   oracles *)

(* identifiers that appear in the initial state and in oracle steps
   increase monotonically in some sense. *)
let oracle_monotonic_def = cake_define
  `oracle_monotonic (f:'a->'b->bool) (R:'b->'b->bool) (S:'b->bool)
  (orac:num->'a) =
     (
         (!i j x y. i < j /\ x IN f (orac i) /\ y IN f (orac j)
           ==> R x y) /\ (!i x y. x IN S /\ y IN f (orac i) ==> R x
           y))`;;

(* HOL4 ML code, not ported:
val conjs = MATCH_MP quotientTheory.EQ_IMPLIES (SPEC_ALL
  oracle_monotonic_def)
  |> UNDISCH_ALL |> CONJUNCTS |> map DISCH_ALL
*)

(* check that an oracle with config values lists the config values that
   would be produced by the incremental compiler. *)
let is_state_oracle_def = cake_define
  `is_state_oracle compile_inc_f co =
     (!n.
         FST (FST (co (SUC n))) = FST (compile_inc_f (FST (FST (co
           n))) (SND (co n))))`;;

(* constructive combinators for building up the config part of an oracle
   *)

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

let pure_co_progs_def = cake_define
  `pure_co_progs f (orac:num->'a) = f o orac`;;

let restrict_zero_def = cake_define
  `restrict_zero (labels:num#num->bool) =
     {l | l IN labels /\ SND l = 0}`;;

let restrict_nonzero_def = cake_define
  `restrict_nonzero (labels:num#num->bool) =
     {l | l IN labels /\ ~(SND l = 0)}`;;

let option_le_def = cake_define
  `option_le x1 x2 =
      match (x1,x2) with
        (_1,NONE) -> T
      | (NONE,(SOME _2)) -> F
      | ((SOME n1),(SOME n2)) -> (n1 <= (n2:num))`;;
