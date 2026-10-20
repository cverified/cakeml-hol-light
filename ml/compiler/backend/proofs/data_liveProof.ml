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
needs "semantics/evaluate.ml";;
needs "semantics/semanticPrimitives.ml";;

hol4_overload "get_vars" "dataSem_get_vars";;
hol4_overload "cut_env" "dataSem_cut_env";;

let SPLIT_PAIR = cake_theorem "SPLIT_PAIR[local]"
  (fun () ->
    `!x y z. (x = (y,z)) <=> (y = FST x) /\ (z = SND x)`)
  CHEAT_TAC;;

let state_rel_def = cake_define
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
      !x. x IN domain live ==> (lookup x (dataSem_state_locals s1)
        = lookup x (dataSem_state_locals t1)))`;;
hol4_overload "state_rel" "data_liveProof_state_rel";;

let state_rel_ID = cake_theorem "state_rel_ID[local]"
  (fun () ->
    `!s live. data_liveProof_state_rel s s live`)
  CHEAT_TAC;;

let jump_exc_IMP_state_rel =
  cake_theorem "jump_exc_IMP_state_rel[local]"
  (fun () ->
    `!s1 t1 s2 t2.
         (dataSem_jump_exc s1 = SOME s2) /\ (dataSem_jump_exc t1 =
           SOME t2) /\
         data_liveProof_state_rel s1 t1 LN /\ (LENGTH (stack s2) =
           LENGTH (stack t2)) ==>
         data_liveProof_state_rel (dataSem_state_handler_fupd (K
           (dataSem_state_handler s1)) s2)
                   (dataSem_state_handler_fupd (K
                     (dataSem_state_handler t1)) t2) LN`)
  CHEAT_TAC;;

(* HOL4 data_liveProofScript.sml:53-54: ML code, not ported *)

let state_rel_IMP_do_app_aux =
  cake_theorem "state_rel_IMP_do_app_aux[local]"
  (fun () ->
    `(dataSem_do_app_aux op args s1 = Rval (v,s2)) /\
       data_liveProof_state_rel s1 t1 anything ==>
       (dataSem_state_handler s1 = dataSem_state_handler s2) /\
         (stack s1 = stack s2) /\
       (?safe peak smx lss.
          dataSem_do_app_aux op args t1 =
            Rval (v,dataSem_state_peak_heap_length_fupd (K peak)
              (dataSem_state_safe_for_space_fupd (K safe)
              (dataSem_state_handler_fupd (K (dataSem_state_handler
              t1)) (dataSem_state_stack_max_fupd (K smx) (stack_fupd
              (K (stack t1)) (dataSem_state_locals_size_fupd (K lss)
              (dataSem_state_locals_fupd (K (dataSem_state_locals t1))
              s2))))))))`)
  CHEAT_TAC;;

let state_rel_IMP_do_app = cake_theorem "state_rel_IMP_do_app[local]"
  (fun () ->
    `(do_app op args s1 = Rval (v,s2)) /\
       data_liveProof_state_rel s1 t1 anything ==>
       (dataSem_state_handler s1 = dataSem_state_handler s2) /\
         (stack s1 = stack s2) /\
       (?safe peak smx lss. do_app op args t1 = Rval
         (v,dataSem_state_peak_heap_length_fupd (K peak)
         (dataSem_state_safe_for_space_fupd (K safe)
         (dataSem_state_handler_fupd (K (dataSem_state_handler t1))
         (dataSem_state_stack_max_fupd (K smx) (stack_fupd (K (stack
         t1)) (dataSem_state_locals_size_fupd (K lss)
         (dataSem_state_locals_fupd (K (dataSem_state_locals t1))
         s2))))))))`)
  CHEAT_TAC;;

let state_rel_IMP_do_app_aux_err =
  cake_theorem "state_rel_IMP_do_app_aux_err[local]"
  (fun () ->
    `(dataSem_do_app_aux op args s1 = Rerr e) /\
  data_liveProof_state_rel s1 t1 anything ==>
       (dataSem_do_app_aux op args t1 = Rerr e)`)
  CHEAT_TAC;;

let state_rel_IMP_do_app_err =
  cake_theorem "state_rel_IMP_do_app_err[local]"
  (fun () ->
    `(do_app op args s1 = Rerr e) /\ data_liveProof_state_rel s1 t1
  anything ==>
       (do_app op args t1 = Rerr e)`)
  CHEAT_TAC;;

let state_rel_IMP_get_vars =
  cake_theorem "state_rel_IMP_get_vars[local]"
  (fun () ->
    `!args s1 t1 t xs.
         data_liveProof_state_rel s1 t1 (list_insert args t) /\
         (dataSem_get_vars args (dataSem_state_locals s1) = SOME
           xs) ==>
         (dataSem_get_vars args (dataSem_state_locals t1) = SOME
           xs)`)
  CHEAT_TAC;;

let is_pure_do_app_Rerr_IMP =
  cake_theorem "is_pure_do_app_Rerr_IMP[local]"
  (fun () ->
    `data_live_is_pure op /\ do_app op xs s = Rerr e ==>
       Rabort Rtype_error = e`)
  CHEAT_TAC;;

let is_pure_do_app_Rval_IMP =
  cake_theorem "is_pure_do_app_Rval_IMP[local]"
  (fun () ->
    `data_live_is_pure op /\ do_app op x s = Rval (q,r) ==> (?safe
  smax. r = dataSem_state_stack_max_fupd (K smax)
  (dataSem_state_safe_for_space_fupd (K safe) s))`)
  CHEAT_TAC;;

let domain_list_delete = cake_theorem "domain_list_delete[local]"
  (fun () ->
    `domain (list_delete xs l) = domain l DIFF set_of_list xs`)
  CHEAT_TAC;;

let evaluate_compile = cake_theorem "evaluate_compile[local]"
  (fun () ->
    `!c s1 res s2 l2 t1 l1 d.
         (evaluate (c,s1) = (res,s2)) /\ data_liveProof_state_rel
           s1 t1 l1 /\
         (compile c l2 = (d,l1)) /\ (~(res = SOME (Rerr (Rabort
           Rtype_error)))) /\
         (!s3. (dataSem_jump_exc s1 = SOME s3) ==>
               (?t3. (dataSem_jump_exc t1 = SOME t3) /\
                 data_liveProof_state_rel s3 t3 LN /\
                    (dataSem_state_handler t3 =
                      dataSem_state_handler s3) /\
                    (LENGTH (stack t3) = LENGTH (stack s3)))) ==>
         (?t2. (evaluate (d,t1) = (res,t2)) /\
              data_liveProof_state_rel s2 t2 (match res with NONE
                -> l2 | _1 -> LN))`)
  CHEAT_TAC;;

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


let compile_correct = cake_theorem "compile_correct"
  (fun () ->
    `!c s. ~(FST (evaluate (c,s)) = SOME (Rerr (Rabort Rtype_error))) /\
  ~(FST (evaluate (c,s)) = NONE) ==>
             (?ls sm safe peak.
               evaluate (FST (compile c LN),s) =
                 (I ## (\s. dataSem_state_peak_heap_length_fupd (K
                   peak) (dataSem_state_safe_for_space_fupd (K safe)
                   (dataSem_state_stack_max_fupd (K sm)
                   (dataSem_state_locals_size_fupd (K ls) s)))))
                   (evaluate (c,s)))`)
  CHEAT_TAC;;

let get_code_labels_compile = cake_theorem "get_code_labels_compile"
  (fun () ->
    `!x y. dataProps_get_code_labels (FST (compile x y)) SUBSET
  dataProps_get_code_labels x`)
  CHEAT_TAC;;
