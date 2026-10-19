(* ======================================================== *)
(*  lab_filterProof: ported from HOL4's
    compiler/backend/proofs/lab_filterProofScript.sml
    A proof theory about lab_filter.ml, with 3 definitions and 22
    theorems.  Needed by lab_to_targetProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for lab_filter
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_filter.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "lib/pegexec.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semantics.ml";;

cake_hide_consts
  ["failed","pegexec_failed"];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let adjust_pc_def = cake_define_cheat CHEAT_TAC
  `adjust_pc p xs =
     (if p = 0 then 0 else
       match xs with [] -> p | (Section n [] :: rest) -> adjust_pc p
         rest | (Section n (l :: lines) :: rest) ->
           (if is_Label l then
             adjust_pc p (Section n lines :: rest) else if not_skip l
               then
             adjust_pc (p - 1) (Section n lines :: rest) + 1 else
               adjust_pc (p - 1) (Section n lines :: rest)))`;;

(*All skips for the next k*)
let all_skips_def = cake_define
  `all_skips pc' code k <=>
   (!x y. ~(asm_fetch_aux (pc' + k) code = SOME (labLang_Asm (Asmi
     (asm_Inst asm_Skip)) x y))) /\
   (!i. i < k ==>
     (?x y.
     asm_fetch_aux (pc' + i) code = SOME (labLang_Asm (Asmi
       (asm_Inst asm_Skip)) x y)))`;;

let is_Label_not_skip = cake_theorem "is_Label_not_skip[local]"
  (fun () ->
    `is_Label y ==> not_skip y`)
  CHEAT_TAC;;

(*
Proof plan:
1)
For any pc, code,
there exists a k such that
asmfetch (pc+k) code = asmfetch (adjust pc) (adjust code)
and
for all i < k
  asmfetch (pc+i) code = Skip

2)
for all i < k.
  asmfetch(pc+i) code = Skip
⇒
evaluate pc code with k for a clock = evaluate (pc+k) code

*)

(* 1)
There is probably a neater way to prove this*)
let asm_fetch_aux_eq = cake_theorem "asm_fetch_aux_eq"
  (fun () ->
    `!pc' code.
     ?k.
       asm_fetch_aux (pc' + k) code = asm_fetch_aux (adjust_pc pc'
         code) (filter_skip code) /\
       all_skips pc' code k`)
  CHEAT_TAC;;
(*For any adjusted fetch, the original fetch is either equal or is a skip
This is probably the wrong direction*)
let asm_fetch_not_skip_adjust_pc =
  cake_theorem "asm_fetch_not_skip_adjust_pc[local]"
  (fun () ->
    `!pc' code inst'.
     (!x y. ~(asm_fetch_aux pc' code = SOME (labLang_Asm (Asmi
       (asm_Inst asm_Skip)) x y))) ==>
     asm_fetch_aux pc' code = asm_fetch_aux (adjust_pc pc' code)
       (filter_skip code)`)
  CHEAT_TAC;;

let state_rw = cake_theorem "state_rw[local]"
  (fun () ->
    `state_clock_fupd (K (state_clock s))
       s = s /\ pc_fupd (K (pc s))
       s = s /\ state_clock_fupd (K (state_clock s + k')) (pc_fupd
         (K (pc s))
       s) = state_clock_fupd (K (state_clock s + k')) s`)
  CHEAT_TAC;;

(* 2) all_skips allow swapping pc for clock*)
let all_skips_evaluate = cake_theorem "all_skips_evaluate[local]"
  (fun () ->
    `!k s.
     all_skips (pc s) (state_code s) k /\
     ~(failed s) ==>
     (!k'.
     evaluate (state_clock_fupd (K (state_clock s + k' + k)) s) =
     evaluate (state_clock_fupd (K (state_clock s + k')) (pc_fupd
       (K (pc s + k)) s)))`)
  CHEAT_TAC;;

let state_rel_def = cake_define
  `lab_filterProof_state_rel (s1:('a,'c,'ffi)labSem_state) t1 <=>
     (?s1compile.
      s1 = compile_fupd (K s1compile) (compile_oracle_fupd (K (\n.
        (\(a,b). (a,filter_skip b)) (compile_oracle t1 n))) (pc_fupd (K
        (adjust_pc (pc t1) (state_code t1))) (state_code_fupd (K
        (filter_skip (state_code t1))) t1))) /\ compile
     t1 = (\c p. s1compile c (filter_skip p))) /\
     ~(failed t1)`;;
hol4_overload "state_rel" "lab_filterProof_state_rel";;

let adjust_pc_all_skips = cake_theorem "adjust_pc_all_skips[local]"
  (fun () ->
    `!k pc' code.
     all_skips pc' code k ==>
     adjust_pc pc' code + 1 = adjust_pc (pc' + k + 1) code`)
  CHEAT_TAC;;

let asm_fetch_aux_eq2 = cake_theorem "asm_fetch_aux_eq2[local]"
  (fun () ->
    `asm_fetch_aux (adjust_pc pc code) (filter_skip code) = x ==>
     (?k.
     asm_fetch_aux (pc + k) code = x /\
     all_skips pc code k)`)
  CHEAT_TAC;;

(* HOL4 lab_filterProofScript.sml:261: ML code, not ported *)

let all_skips_evaluate_rw = cake_theorem "all_skips_evaluate_rw[local]"
  (fun () ->
    `all_skips (pc s) (state_code s) k /\ ~(failed s) /\ state_clock
     s = clk + k /\
     t = state_clock_fupd (K clk) (pc_fupd (K (pc s + k)) s) ==>
     evaluate s = evaluate t`)
  CHEAT_TAC;;

(*For all initial code there is some all_skips*)
let all_skips_initial_adjust =
  cake_theorem "all_skips_initial_adjust[local]"
  (fun () ->
    `!code.
     ?k. all_skips 0 code k /\ adjust_pc k code = 0`)
  CHEAT_TAC;;

(*May need strengthening*)
let loc_to_pc_eq_NONE = cake_theorem "loc_to_pc_eq_NONE[local]"
  (fun () ->
    `!n1 n2 code.
     loc_to_pc n1 n2 (filter_skip code) = NONE ==>
     loc_to_pc n1 n2 code = NONE`)
  CHEAT_TAC;;

let loc_to_pc_eq_SOME = cake_theorem "loc_to_pc_eq_SOME[local]"
  (fun () ->
    `!n1 n2 code pc'.
     loc_to_pc n1 n2 (filter_skip code) = SOME pc' ==>
     (?pc'.
     loc_to_pc n1 n2 code = SOME pc' /\
     adjust_pc pc' code = pc')`)
  CHEAT_TAC;;

let next_label_filter_skip =
  cake_theorem "next_label_filter_skip[local]"
  (fun () ->
    `!code.
     next_label code = next_label (filter_skip code)`)
  CHEAT_TAC;;

let all_skips_get_lab_after =
  cake_theorem "all_skips_get_lab_after[local]"
  (fun () ->
    `!code k.
     all_skips 0 code k ==>
     get_lab_after k code =
     get_lab_after 0 (filter_skip code)`)
  CHEAT_TAC;;

let get_lab_after_adjust = cake_theorem "get_lab_after_adjust[local]"
  (fun () ->
    `!pc' code k.
     all_skips pc' code k ==>
     get_lab_after (pc' + k) code = get_lab_after (adjust_pc pc'
       code) (filter_skip code)`)
  CHEAT_TAC;;

let loc_to_pc_adjust_pc_append =
  cake_theorem "loc_to_pc_adjust_pc_append[local]"
  (fun () ->
    `!n1 n2 code pc' ls.
     loc_to_pc n1 n2 code = SOME pc' ==>
     adjust_pc pc' code = adjust_pc pc' (code ++ ls)`)
  CHEAT_TAC;;

(* HOL4 lab_filterProofScript.sml:556-563: a proof *)

(* HOL4 lab_filterProofScript.sml:565-576: a proof *)

let share_mem_op_NONE_filter_correct =
  cake_theorem "share_mem_op_NONE_filter_correct"
  (fun () ->
    `all_skips (pc t1) (state_code t1) k /\
     share_mem_op m r a
       (compile_oracle_fupd (K arb_oracle) (compile_fupd (K
         arb_compile) (state_code_fupd (K (filter_skip (state_code t1)))
         (pc_fupd (K (adjust_pc (pc t1) (state_code t1))) t1)))) = NONE
         ==>
     share_mem_op m r a (pc_fupd (K (k + pc t1)) t1) = NONE`)
  CHEAT_TAC;;

(* HOL4 lab_filterProofScript.sml:594-602: a proof *)

(* HOL4 lab_filterProofScript.sml:604-612: a proof *)

let share_mem_op_FFI_return_filter_correct =
  cake_theorem "share_mem_op_FFI_return_filter_correct"
  (fun () ->
    `(all_skips (pc t1) (state_code t1) k /\ ~(state_clock t1 = 0) /\
  compile
     t1 = (\c p. s1compile c (filter_skip p)) /\ ~(failed t1) /\
     share_mem_op m r a
       (compile_oracle_fupd (K (\n. (\(a,b). (a,filter_skip b))
         (compile_oracle t1 n))) (compile_fupd (K s1compile)
         (state_code_fupd (K (filter_skip (state_code t1))) (pc_fupd (K
         (adjust_pc (pc t1) (state_code t1))) t1)))) = SOME (FFI_return
         f l,s)) ==>
     (?s2. !k'. share_mem_op m r a (pc_fupd (K (k + pc t1)) t1) =
       SOME (FFI_return f l,s2) /\
     lab_filterProof_state_rel s s2 /\ ~(failed s) /\ ~(failed s2)
       /\
     share_mem_op m r a (state_clock_fupd (K (k' + state_clock t1))
       (pc_fupd (K (k + pc t1)) t1)) =
       SOME (FFI_return f l,state_clock_fupd (K (k' + state_clock
         s2)) s2))`)
  CHEAT_TAC;;

let share_mem_op_FFI_final_filter_correct =
  cake_theorem "share_mem_op_FFI_final_filter_correct"
  (fun () ->
    `(all_skips (pc t1) (state_code t1) k /\ ~(state_clock t1 = 0) /\
  compile
     t1 = (\c p. s1compile c (filter_skip p)) /\ ~(failed t1) /\
     share_mem_op m r a
       (compile_oracle_fupd (K (\n. (\(a,b). (a,filter_skip b))
         (compile_oracle t1 n))) (compile_fupd (K s1compile)
         (state_code_fupd (K (filter_skip (state_code t1))) (pc_fupd (K
         (adjust_pc (pc t1) (state_code t1))) t1)))) = SOME (FFI_final
         f,s)) ==>
     (?s2. share_mem_op m r a (pc_fupd (K (k + pc t1)) t1) = SOME
       (FFI_final f,s2) /\ state_ffi
     s = state_ffi s2)`)
  CHEAT_TAC;;

let filter_correct = cake_theorem "filter_correct"
  (fun () ->
    `!(s1:('a,'c,'ffi)labSem_state) t1 res s2.
        (evaluate s1 = (res,s2)) /\ lab_filterProof_state_rel s1 t1
          /\ ~(failed t1) ==>
        (?k t2.
          (evaluate (state_clock_fupd (K (labSem_state_clock s1 +
            k)) t1) = (res,t2)) /\
          (state_ffi s2 = state_ffi t2))`)
  CHEAT_TAC;;

let state_rel_IMP_sem_EQ_sem =
  cake_theorem "state_rel_IMP_sem_EQ_sem[local]"
  (fun () ->
    `!s t. lab_filterProof_state_rel s t ==> semantics s = semantics t`)
  CHEAT_TAC;;

let filter_skip_semantics = cake_theorem "filter_skip_semantics"
  (fun () ->
    `!s t. (pc t = 0) /\ ~(failed t) /\
     (?scompile.
       s = compile_fupd (K scompile) (compile_oracle_fupd (K
         ((\(a,b). (a,filter_skip b)) o compile_oracle t))
         (state_code_fupd (K (filter_skip (state_code t))) t)) /\
         compile
      t = (\c p. scompile c (filter_skip p))) /\
      ~(failed t) ==>
     semantics s = semantics t`)
  CHEAT_TAC;;

let sec_ends_with_label_filter_skip =
  cake_theorem "sec_ends_with_label_filter_skip"
  (fun () ->
    `!code.
     EVERY sec_ends_with_label code ==>
     EVERY sec_ends_with_label (filter_skip code)`)
  CHEAT_TAC;;

cake_hide_consts [];;
