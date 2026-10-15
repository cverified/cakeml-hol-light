(* ======================================================== *)
(*  bviProps: ported from HOL4's
    compiler/backend/semantics/bviPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about BVI and its semantics
*)

needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "semantics/ast.ml";;

(* HOL4 ML code, not ported:
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def };
val option_thms = { nchotomy = option_nchotomy, case_def =
  option_case_def };
val result_thms = { nchotomy = semanticPrimitivesTheory.result_nchotomy,
                    case_def = semanticPrimitivesTheory.result_case_def
                      };
val ffi_result_thms = { nchotomy = ffiTheory.ffi_result_nchotomy,
                        case_def = ffiTheory.ffi_result_case_def };
*)

(* HOL4 ML code, not ported:
val evaluate_LENGTH = Q.prove(
  `!xs s env. (\(xs,s,env).
      (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH
        res)
            | _ => T))
      (xs,s,env)`,
  HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def,case_elim_thms]
  \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[]
  \\ first_x_assum drule \\ rw [])
  |> SIMP_RULE std_ss [];
*)

let inc_clock_def = cake_define
  `bviProps_inc_clock n (s:('c,'ffi)bviSem_state) = ?_clock_fupd (K
  (?_clock s + n)) s`;;
hol4_overload "inc_clock" "bviProps_inc_clock";;

(* TERMINATION: wf_rel_tac`measure exp_size`
  \\ simp[bviTheory.exp_size_def]
  \\ rpt conj_tac \\ rpt gen_tac
  \\ Induct_on`es`
  \\ rw[bviTheory.exp_size_def]
  \\ simp[] \\ res_tac \\ simp[] *)
let get_code_labels_def = cake_define
  `(bviProps_get_code_labels (Var _1) = {}) /\
   (bviProps_get_code_labels (If e1 e2 e3) = bviProps_get_code_labels
     e1 UNION bviProps_get_code_labels e2 UNION bviProps_get_code_labels
     e3) /\
   (bviProps_get_code_labels (Let es e) = BIGUNION (set_of_list (MAP
     bviProps_get_code_labels es)) UNION bviProps_get_code_labels e) /\
   (bviProps_get_code_labels (Raise e) = bviProps_get_code_labels e)
     /\
   (bviProps_get_code_labels (Tick e) = bviProps_get_code_labels e)
     /\
   (bviProps_get_code_labels (Force loc v) = {loc}) /\
   (bviProps_get_code_labels (Call _2 d es h) =
     (match d with NONE -> {} | SOME n -> {n}) UNION
     (match h with NONE -> {} | SOME e -> bviProps_get_code_labels e)
       UNION
     BIGUNION (set_of_list (MAP bviProps_get_code_labels es))) /\
   (bviProps_get_code_labels (Op op es) = assign_get_code_label op
     UNION BIGUNION (set_of_list (MAP bviProps_get_code_labels es))) /\
   (bviProps_get_code_labels (Return es) = BIGUNION (set_of_list (MAP
     bviProps_get_code_labels es))) /\
   (bviProps_get_code_labels (LetCall _3 _4 d es y) =
     {d} UNION bviProps_get_code_labels y UNION BIGUNION
       (set_of_list (MAP bviProps_get_code_labels es)))`;;
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
     mk_? (?_refs s) (?_clock s) (bviSem_state_global s) (?_code
       s) (?_ffi s) cc ((f ## I) o ?_compile_oracle s)`;;

let adj_orac_ok_def = cake_define
  `adj_orac_ok cc f (s:('a,'ffi)bviSem_state) <=>
     (!n x y. ?_compile_oracle s n = (x,y) ==>
       OPTION_MAP (I ## (I ## f)) (?_compile s x y) = cc (f x) y)`;;

let adj_orac_rel_def = cake_define
  `bviProps_adj_orac_rel cc f (s1:('a,'ffi)bviSem_state)
  (s2:('b,'ffi)bviSem_state) <=>
     adj_orac_ok cc f s1 /\ s2 = adj_orac cc f s1`;;
hol4_overload "adj_orac_rel" "bviProps_adj_orac_rel";;
