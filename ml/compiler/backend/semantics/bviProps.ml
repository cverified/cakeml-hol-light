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
needs "semantics/ast.ml";;

(* HOL4 bviPropsScript.sml:103-108: ML code, not ported *)

(* HOL4 bviPropsScript.sml:127-137: ML code, not ported *)

let inc_clock_def = cake_define
  `bviProps_inc_clock n (s:('c,'ffi)bviSem_state) = state_clock_fupd
  (K (state_clock s + n)) s`;;
hol4_overload "inc_clock" "bviProps_inc_clock";;

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

let good_code_labels_def = cake_define
  `bviProps_good_code_labels p elabs <=>
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND) p))
       SUBSET set_of_list (MAP FST p) UNION elabs`;;
hol4_overload "good_code_labels" "bviProps_good_code_labels";;

(* --- switching a compiler pass off
   --------------------------------------

   A pass that is configured off compiles with CURRY I, i.e. the
     identity.
   It still wraps the incremental compiler with state_cc/state_co, which
   moves one configuration component between the oracle's state and its
   config.  adj_orac below performs that move on a state; it is the BVI
   analogue of closProps' adj_orac_rel.
       *)

let adj_orac_def = cake_define
  `(adj_orac cc f (s:('a,'ffi)bviSem_state):('b,'ffi)bviSem_state) =
     mk_bviSem_state (state_refs s) (state_clock s)
       (bviSem_state_global s) cc ((f ## I) o compile_oracle s)
       (state_code s) (state_ffi s)`;;

let adj_orac_ok_def = cake_define
  `adj_orac_ok cc f (s:('a,'ffi)bviSem_state) <=>
     (!n x y. compile_oracle s n = (x,y) ==>
       OPTION_MAP (I ## (I ## f)) (compile s x y) = cc (f x) y)`;;

let adj_orac_rel_def = cake_define
  `bviProps_adj_orac_rel cc f (s1:('a,'ffi)bviSem_state)
  (s2:('b,'ffi)bviSem_state) <=>
     adj_orac_ok cc f s1 /\ s2 = adj_orac cc f s1`;;
hol4_overload "adj_orac_rel" "bviProps_adj_orac_rel";;
