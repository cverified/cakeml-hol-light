(* ======================================================== *)
(*  dataProps: ported from HOL4's
    compiler/backend/semantics/dataPropsScript.sml  *)
(* ======================================================== *)

(*
  Properties about dataLang and its semantics
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let _ = size_thms "dataSem_v";;
(* HOL4 dataPropsScript.sml:43-48: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let approx_of_def = cake_define_try_tac (fun () ->
  `(inv_image (MEASURE I LEX MEASURE (list_size dataSem_v_size))
                             (\(lims,vs,refs). (sptree_size
                               refs,vs)))`)
  CHEAT_TAC
  `approx_of lims x2 refs =
        match x2 with
          [] -> 0
        | (x :: y :: ys) ->
       approx_of lims [x] refs + approx_of lims (y :: ys) refs
        | [(Word64 _2:dataSem_v)] -> 3
        | [Number i] ->
       (if small_num (limits_arch_64_bit lims) i then 0 else
         bignum_size (limits_arch_64_bit lims) i)
        | [CodePtr _3] -> 0
        | [RefPtr _4 r] ->
        (match lookup r refs with NONE -> 0 | SOME (ByteArray _5 bs)
          -> LENGTH bs DIV (arch_size lims DIV 8) + 2 | SOME (ValueArray
          vs) ->
            approx_of lims vs (delete r refs) + LENGTH vs + 1 | SOME
              (Thunk _6 v) ->
            approx_of lims [v] (delete r refs) + 2 | SOME
              (bvlSem_MutBlock tg fin ls c rs) ->
            approx_of lims (ls ++ [c] ++ rs) (delete r refs) +
            LENGTH ls + LENGTH rs + 2)
        | [Block ts tag []] -> 0
        | [Block ts tag vs] ->
       approx_of lims vs refs + LENGTH vs + 1`;;

(* HOL4 dataPropsScript.sml:85: the ML values that the definitions
   below antiquote *)

(* ops that are not allowed_op have stack_consumed = NONE, which has to
   propagate through do_stack's safe_for_space computation *)
(* HOL4 dataPropsScript.sml:133-153: code that the source has in a
   comment *)

let var_corr_def = cake_define
  `var_corr env corr t <=>
     EVERY2 (\v x. get_var v t = SOME x) corr env`;;

(* INFO: only used in bvi_to_dataProof *)

(* HOL4 dataPropsScript.sml:263: code that the source has in a
   comment *)
(* HOL4 dataPropsScript.sml:264-268: a proof *)

(* HOL4 dataPropsScript.sml:270: code that the source has in a
   comment *)

(* HOL4 dataPropsScript.sml:296: code that the source has in a
   comment *)

(* HOL4 dataPropsScript.sml:324: code that the source has in a
   comment *)

(* HOL4 dataPropsScript.sml:342: code that the source has in a
   comment *)

(* HOL4 dataPropsScript.sml:360: code that the source has in a
   comment *)

(* HOL4 dataPropsScript.sml:484: code that the source has in a
   comment *)
(* HOL4 dataPropsScript.sml:485-509: a proof *)

(* HOL4 dataPropsScript.sml:663-676: a proof *)

(* HOL4 dataPropsScript.sml:678-686: a proof *)

(* HOL4 dataPropsScript.sml:688-691: a proof *)


(* The field-swap (stack_max/safe_for_space/peak_heap_length) commutes
   through
   the narrow cut in evaluate(Assign), since cut_state_opt only touches
     locals. *)

(* When the swap leaves stack_max at its original value (the fl=F case),
   the merged input update collapses to just
     safe_for_space/peak_heap_length. *)

let same_stack_size_def = cake_define
  `same_stack_size x y <=> size_of_stack_frame x =
  size_of_stack_frame y`;;

let locals_ok_def = cake_define
  `locals_ok l1 l2 =
     (!v x. (sptree_lookup v l1 = SOME x) ==> (sptree_lookup v l2
       = SOME x))`;;

(* Under locals_ok, the narrow cut in evaluate(Assign) succeeds on the
   larger
   locals and yields a state equal up to (and locals_ok on) its locals.
     *)

(* HOL4 dataPropsScript.sml:1868: code that the source has in a
   comment *)

let get_code_labels_def = cake_define
  `dataProps_get_code_labels x1 =
        match x1 with
          (Call r d a h:dataLang_prog) ->
       (match d with SOME x -> {x} | _7 -> {}) UNION
       (match h with SOME (n,p) -> dataProps_get_code_labels p | _8
         -> {})
        | (Force _9 loc _10) -> {loc}
        | (Seq p1 p2) -> dataProps_get_code_labels p1 UNION
          dataProps_get_code_labels p2
        | (If _11 p1 p2) -> dataProps_get_code_labels p1 UNION
          dataProps_get_code_labels p2
        | (Assign _12 op _13 _14) -> assign_get_code_label op
        | _15 -> {}`;;
hol4_overload "get_code_labels" "dataProps_get_code_labels";;

let good_code_labels_def = cake_define
  `dataProps_good_code_labels p elabs <=>
     (BIGUNION (set_of_list (MAP (\(n,m,pp).
       (dataProps_get_code_labels pp)) p))) SUBSET
     (set_of_list (MAP FST p)) UNION elabs`;;
hol4_overload "good_code_labels" "dataProps_good_code_labels";;

(* HOL4 dataPropsScript.sml:2259: code that the source has in a
   comment *)

let zero_limits_def = cake_define
  `zero_limits = (mk_limits 0 0 0 ARB ARB ARB:limits)`;;


(* HOL4 dataPropsScript.sml:2311-2314: a proof *)

(* The limits-swap commutes through the narrow cut in evaluate(Assign).
   *)

(* Stack frames equal up-to size component*)
let stack_frame_size_rel_def = cake_define
  `stack_frame_size_rel x1 x2 =
        match (x1,x2) with
          (dataSem_Exc opt spt num',dataSem_Exc opt' spt' num') ->
       spt = spt' /\ num' = num'
        | ((Env opt spt),(Env opt' spt')) ->
       spt = spt'
        | (_16,_17) -> F`;;

(* HOL4 dataPropsScript.sml:2541-2545: a proof *)

(* The locals_size/stack/stack_frame_sizes-swap commutes through the
   narrow
   cut in evaluate(Assign), and the cut preserves the stack. *)

let cc_co_only_diff_def = cake_define
  `cc_co_only_diff (s:('a,'ffi)dataSem_state) (t:('b,'ffi)dataSem_state)
  <=> dataSem_state_locals
     s = dataSem_state_locals t /\ dataSem_state_locals_size
     s = dataSem_state_locals_size t /\ stack
     s = stack t /\ dataSem_state_stack_max
     s = dataSem_state_stack_max t /\ dataSem_state_stack_frame_sizes
     s = dataSem_state_stack_frame_sizes t /\ dataSem_state_global
     s = dataSem_state_global t /\ dataSem_state_handler
     s = dataSem_state_handler t /\ state_refs
     s = state_refs t /\ state_clock
     s = state_clock t /\ state_code
     s = state_code t /\ state_ffi
     s = state_ffi t /\ dataSem_state_space
     s = dataSem_state_space t /\ dataSem_state_tstamps
     s = dataSem_state_tstamps t /\ dataSem_state_limits
     s = dataSem_state_limits t /\ dataSem_state_safe_for_space
     s = dataSem_state_safe_for_space t /\
       dataSem_state_peak_heap_length
     s = dataSem_state_peak_heap_length t`;;

(* HOL4 dataPropsScript.sml:2992: code that the source has in a
   comment *)

(* HOL4 dataPropsScript.sml:3027: code that the source has in a
   comment *)

(* The narrow cut in evaluate(Assign) only depends on locals (equal
   under
   cc_co_only_diff), so the t-side cut is determined by the s-side cut
     and
   preserves cc_co_only_diff. *)

(* TODO: move *)

(* HOL4 dataPropsScript.sml:3303: code that the source has in a
   comment *)
