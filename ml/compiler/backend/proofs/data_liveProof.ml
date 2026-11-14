(* ======================================================== *)
(*  data_liveProof: ported from HOL4's
    compiler/backend/proofs/data_liveProofScript.sml
    A proof theory about data_live.ml, with 1 definition and 14
    theorems.  Needed by bvi_to_dataProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for data_live
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "data_liveProof"
  ["dataProps"; "dataSem"; "data_live"];;

(* HOL4 data_liveProofScript.sml:12-13: an overload that the source
   brings to the front: get_vars, written out as dataSem_get_vars *)
(* HOL4 data_liveProofScript.sml:12-13: an overload that the source
   brings to the front: cut_env, written out as dataSem_cut_env *)

(* [local] *)
let SPLIT_PAIR = prove
 (`!x y z. (x = (y,z)) <=> (y = FST x) /\ (z = SND x)`,
  CHEAT_TAC);;

let state_rel_def = new_definition
  `data_liveProof_state_rel (s1:('a,'ffi)dataSem_state)
  (t1:('a,'ffi)dataSem_state) (live:1 spt) <=> dataSem_state_code
     s1 = dataSem_state_code t1 /\ dataSem_state_clock s1 =
       dataSem_state_clock t1 /\ dataSem_state_space s1 =
       dataSem_state_space t1 /\ dataSem_state_ffi
     s1 = dataSem_state_ffi t1 /\ dataSem_state_refs s1 =
       dataSem_state_refs t1 /\ dataSem_state_global s1 =
       dataSem_state_global t1 /\ dataSem_state_handler
     s1 = dataSem_state_handler t1 /\ (LENGTH (dataSem_state_stack
       s1) = LENGTH (dataSem_state_stack t1)) /\ dataSem_state_compile
     s1 = dataSem_state_compile t1 /\ dataSem_state_compile_oracle s1
       = dataSem_state_compile_oracle t1 /\ dataSem_state_tstamps
     s1 = dataSem_state_tstamps t1 /\ dataSem_state_limits
     s1 = dataSem_state_limits t1 /\ dataSem_state_stack_frame_sizes
     s1 = dataSem_state_stack_frame_sizes t1 /\
     (
      // s1.safe_for_space = t1.safe_for_space /\
      // ASK: Probably don't need it
      !x. x IN domain live ==> (sptree_lookup x
        (dataSem_state_locals s1) = sptree_lookup x
        (dataSem_state_locals t1)))`;;

(* [local] *)
let state_rel_ID = prove
 (`!s live. data_liveProof_state_rel s s live`,
  CHEAT_TAC);;

(* [local] *)
let jump_exc_IMP_state_rel = prove
 (`!s1 t1 s2 t2.
       (dataSem_jump_exc s1 = SOME s2) /\ (dataSem_jump_exc t1 = SOME
         t2) /\
       data_liveProof_state_rel s1 t1 LN /\ (LENGTH (stack s2) =
         LENGTH (stack t2)) ==>
       data_liveProof_state_rel (dataSem_state_handler_fupd (K
         (dataSem_state_handler s1)) s2)
                 (dataSem_state_handler_fupd (K
                   (dataSem_state_handler t1)) t2) LN`,
  CHEAT_TAC);;

(* HOL4 data_liveProofScript.sml:53-54: ML code, not ported *)

(* [local] *)
let state_rel_IMP_do_app_aux = prove
 (`(dataSem_do_app_aux op args s1 = Rval (v,s2)) /\
     data_liveProof_state_rel s1 t1 anything ==>
     (dataSem_state_handler s1 = dataSem_state_handler s2) /\ (stack
       s1 = stack s2) /\
     (?safe peak smx lss.
        dataSem_do_app_aux op args t1 =
          Rval (v,dataSem_state_peak_heap_length_fupd (K peak)
            (dataSem_state_safe_for_space_fupd (K safe)
            (dataSem_state_handler_fupd (K (dataSem_state_handler t1))
            (dataSem_state_stack_max_fupd (K smx) (stack_fupd (K
            (stack t1)) (dataSem_state_locals_size_fupd (K lss)
            (dataSem_state_locals_fupd (K (dataSem_state_locals t1))
            s2))))))))`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_IMP_do_app = prove
 (`(dataSem_do_app op args s1 = Rval (v,s2)) /\
     data_liveProof_state_rel s1 t1 anything ==>
     (dataSem_state_handler s1 = dataSem_state_handler s2) /\ (stack
       s1 = stack s2) /\
     (?safe peak smx lss. dataSem_do_app op args t1 = Rval
       (v,dataSem_state_peak_heap_length_fupd (K peak)
       (dataSem_state_safe_for_space_fupd (K safe)
       (dataSem_state_handler_fupd (K (dataSem_state_handler t1))
       (dataSem_state_stack_max_fupd (K smx) (stack_fupd (K (stack
       t1)) (dataSem_state_locals_size_fupd (K lss)
       (dataSem_state_locals_fupd (K (dataSem_state_locals t1))
       s2))))))))`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_IMP_do_app_aux_err = prove
 (`(dataSem_do_app_aux op args s1 = Rerr e) /\ data_liveProof_state_rel
  s1 t1 anything ==>
     (dataSem_do_app_aux op args t1 = Rerr e)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_IMP_do_app_err = prove
 (`(dataSem_do_app op args s1 = Rerr e) /\ data_liveProof_state_rel s1
  t1 anything ==>
     (dataSem_do_app op args t1 = Rerr e)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_IMP_get_vars = prove
 (`!args s1 t1 t xs.
       data_liveProof_state_rel s1 t1 (list_insert args t) /\
       (dataSem_get_vars args (dataSem_state_locals s1) = SOME xs)
         ==>
       (dataSem_get_vars args (dataSem_state_locals t1) = SOME xs)`,
  CHEAT_TAC);;

(* [local] *)
let is_pure_do_app_Rerr_IMP = prove
 (`data_live_is_pure op /\ dataSem_do_app op xs s = Rerr e ==>
     Rabort Rtype_error = e`,
  CHEAT_TAC);;

(* [local] *)
let is_pure_do_app_Rval_IMP = prove
 (`data_live_is_pure op /\ dataSem_do_app op x s = Rval (q,r) ==>
  (?safe smax. r = dataSem_state_stack_max_fupd (K smax)
  (dataSem_state_safe_for_space_fupd (K safe) s))`,
  CHEAT_TAC);;

(* [local] *)
let domain_list_delete = prove
 (`domain (list_delete xs l) = domain l DIFF set_of_list xs`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_compile = prove
 (`!c s1 res s2 l2 t1 l1 d.
       (dataSem_evaluate (c,s1) = (res,s2)) /\
         data_liveProof_state_rel s1 t1 l1 /\
       (data_live_compile c l2 = (d,l1)) /\ (~(res = SOME (Rerr
         (Rabort Rtype_error)))) /\
       (!s3. (dataSem_jump_exc s1 = SOME s3) ==>
             (?t3. (dataSem_jump_exc t1 = SOME t3) /\
               data_liveProof_state_rel s3 t3 LN /\
                  (dataSem_state_handler t3 = dataSem_state_handler
                    s3) /\
                  (LENGTH (stack t3) = LENGTH (stack s3)))) ==>
       (?t2. (dataSem_evaluate (d,t1) = (res,t2)) /\
            data_liveProof_state_rel s2 t2 (match res with NONE ->
              l2 | _1 -> LN))`,
  CHEAT_TAC);;

(* HOL4 data_liveProofScript.sml:212-214: a proof *)

(* HOL4 data_liveProofScript.sml:216-220: a proof *)

(* HOL4 data_liveProofScript.sml:222-289: a proof *)

(* HOL4 data_liveProofScript.sml:291-295: a proof *)

(* HOL4 data_liveProofScript.sml:297-305: a proof *)

(* HOL4 data_liveProofScript.sml:307-315: a proof *)

(* HOL4 data_liveProofScript.sml:317-322: a proof *)

(* HOL4 data_liveProofScript.sml:324-348: a proof *)

(* HOL4 data_liveProofScript.sml:350-372: a proof *)

(* HOL4 data_liveProofScript.sml:374-378: a proof *)

(* HOL4 data_liveProofScript.sml:380-456: a proof *)

(* HOL4 data_liveProofScript.sml:458-472: a proof *)

(* HOL4 data_liveProofScript.sml:474-488: a proof *)

(* HOL4 data_liveProofScript.sml:490-492: a proof *)

(* HOL4 data_liveProofScript.sml:494-538: a proof *)

(* HOL4 data_liveProofScript.sml:540-593: a proof *)

(* HOL4 data_liveProofScript.sml:595-616: a proof *)

(* HOL4 data_liveProofScript.sml:618: a proof *)
  (* Call from here onwards *)
(* HOL4 data_liveProofScript.sml:620-621: a proof *)
  (* Call with SOME ret *)
(* HOL4 data_liveProofScript.sml:623-628: a proof *)

(* HOL4 data_liveProofScript.sml:630-705: a proof *)

(* HOL4 data_liveProofScript.sml:707-847: a proof *)

(* HOL4 data_liveProofScript.sml:849-1002: a proof *)

(* HOL4 data_liveProofScript.sml:1004: a proof *)


let compile_correct = prove
 (`!c s. ~(FST (dataSem_evaluate (c,s)) = SOME (Rerr (Rabort
  Rtype_error))) /\ ~(FST (dataSem_evaluate (c,s)) = NONE) ==>
           (?ls sm safe peak.
             dataSem_evaluate (FST (data_live_compile c LN),s) =
               (I ## (\s. dataSem_state_peak_heap_length_fupd (K
                 peak) (dataSem_state_safe_for_space_fupd (K safe)
                 (dataSem_state_stack_max_fupd (K sm)
                 (dataSem_state_locals_size_fupd (K ls) s)))))
                 (dataSem_evaluate (c,s)))`,
  CHEAT_TAC);;

let get_code_labels_compile = prove
 (`!x y. dataProps_get_code_labels (FST (data_live_compile x y))
  SUBSET dataProps_get_code_labels x`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
