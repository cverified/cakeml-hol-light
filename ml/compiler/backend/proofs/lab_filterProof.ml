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
needs "semantics/ffi/ffi.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "lab_filterProof"
  ["labProps"; "labSem"; "lab_filter"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["failed","pegexec_failed"];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let adjust_pc_def,adjust_pc_ind = define_rec
  [`adjust_pc p xs =
     (if p = 0 then 0 else
       match xs with [] -> p | (Section n [] :: rest) -> adjust_pc p
         rest | (Section n (l :: lines) :: rest) ->
           (if is_Label l then
             adjust_pc p (Section n lines :: rest) else if not_skip
               l then
             adjust_pc (p - 1) (Section n lines :: rest) + 1
               else adjust_pc (p - 1) (Section n lines :: rest)))`];;

(*All skips for the next k*)
let all_skips_def = new_definition
  `all_skips pc' code k <=>
   (!x y. ~(asm_fetch_aux (pc' + k) code = SOME (labLang_Asm (Asmi
     (asm_Inst asm_Skip)) x y))) /\
   (!i. i < k ==>
     (?x y.
     asm_fetch_aux (pc' + i) code = SOME (labLang_Asm (Asmi
       (asm_Inst asm_Skip)) x y)))`;;

(* [local] *)
let is_Label_not_skip = prove
 (`is_Label y ==> not_skip y`,
  CHEAT_TAC);;

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
let asm_fetch_aux_eq = prove
 (`!pc' code.
   ?k.
     asm_fetch_aux (pc' + k) code = asm_fetch_aux (adjust_pc pc'
       code) (filter_skip code) /\
     all_skips pc' code k`,
  CHEAT_TAC);;
(*For any adjusted fetch, the original fetch is either equal or is a skip
This is probably the wrong direction*)
(* [local] *)
let asm_fetch_not_skip_adjust_pc = prove
 (`!pc' code inst'.
   (!x y. ~(asm_fetch_aux pc' code = SOME (labLang_Asm (Asmi
     (asm_Inst asm_Skip)) x y))) ==>
   asm_fetch_aux pc' code = asm_fetch_aux (adjust_pc pc' code)
     (filter_skip code)`,
  CHEAT_TAC);;

(* [local] *)
let state_rw = prove
 (`state_clock_fupd (K (state_clock s))
     s = s /\ pc_fupd (K (pc s))
     s = s /\ state_clock_fupd (K (state_clock s + k')) (pc_fupd (K
       (pc s))
     s) = state_clock_fupd (K (state_clock s + k')) s`,
  CHEAT_TAC);;

(* 2) all_skips allow swapping pc for clock*)
(* HOL4 lab_filterProofScript.sml:170-197: a theorem whose statement
   HOL Light does not read (tools/unstated.py): all_skips_evaluate *)

let lab_filterProof_state_rel_def = new_definition
  `lab_filterProof_state_rel (s1:('a,'c,'ffi)labSem_state) t1 <=>
     (?s1compile.
      s1 = compile_fupd (K s1compile) (compile_oracle_fupd (K (\n.
        (\(a,b). (a,filter_skip b)) (compile_oracle t1 n))) (pc_fupd (K
        (adjust_pc (pc t1) (state_code t1))) (state_code_fupd (K
        (filter_skip (state_code t1))) t1))) /\ compile
     t1 = (\c p. s1compile c (filter_skip p))) /\
     ~(failed t1)`;;
hol4_overload "state_rel" "lab_filterProof_state_rel";;

(* [local] *)
let adjust_pc_all_skips = prove
 (`!k pc' code.
   all_skips pc' code k ==>
   adjust_pc pc' code + 1 = adjust_pc (pc' + k + 1) code`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let asm_fetch_aux_eq2 = prove
 (cake_as_vars (fun () ->
    `asm_fetch_aux (adjust_pc pc code) (filter_skip code) = x ==>
     (?k.
     asm_fetch_aux (pc + k) code = x /\
     all_skips pc code k)`),
  CHEAT_TAC);;

(* HOL4 lab_filterProofScript.sml:261: ML code, not ported *)

(* HOL4 lab_filterProofScript.sml:263-278: a theorem whose statement
   HOL Light does not read (tools/unstated.py): all_skips_evaluate_rw *)

(*For all initial code there is some all_skips*)
(* [local] *)
let all_skips_initial_adjust = prove
 (`!code.
   ?k. all_skips 0 code k /\ adjust_pc k code = 0`,
  CHEAT_TAC);;

(*May need strengthening*)
(* [local] *)
let loc_to_pc_eq_NONE = prove
 (`!n1 n2 code.
   loc_to_pc n1 n2 (filter_skip code) = NONE ==>
   loc_to_pc n1 n2 code = NONE`,
  CHEAT_TAC);;

(* [local] *)
let loc_to_pc_eq_SOME = prove
 (`!n1 n2 code pc'.
   loc_to_pc n1 n2 (filter_skip code) = SOME pc' ==>
   (?pc'.
   loc_to_pc n1 n2 code = SOME pc' /\
   adjust_pc pc' code = pc')`,
  CHEAT_TAC);;

(* [local] *)
let next_label_filter_skip = prove
 (`!code.
   next_label code = next_label (filter_skip code)`,
  CHEAT_TAC);;

(* [local] *)
let all_skips_get_lab_after = prove
 (`!code k.
   all_skips 0 code k ==>
   get_lab_after k code =
   get_lab_after 0 (filter_skip code)`,
  CHEAT_TAC);;

(* [local] *)
let get_lab_after_adjust = prove
 (`!pc' code k.
   all_skips pc' code k ==>
   get_lab_after (pc' + k) code = get_lab_after (adjust_pc pc'
     code) (filter_skip code)`,
  CHEAT_TAC);;

(* [local] *)
let loc_to_pc_adjust_pc_append = prove
 (`!n1 n2 code pc' ls.
   loc_to_pc n1 n2 code = SOME pc' ==>
   adjust_pc pc' code = adjust_pc pc' (code ++ ls)`,
  CHEAT_TAC);;

(* HOL4 lab_filterProofScript.sml:556-563: a proof *)

(* HOL4 lab_filterProofScript.sml:565-576: a proof *)

let share_mem_op_NONE_filter_correct = prove
 (`all_skips (pc t1) (state_code t1) k /\
   share_mem_op m r a
     (compile_oracle_fupd (K arb_oracle) (compile_fupd (K
       arb_compile) (state_code_fupd (K (filter_skip (state_code t1)))
       (pc_fupd (K (adjust_pc (pc t1) (state_code t1))) t1)))) = NONE
       ==>
   share_mem_op m r a (pc_fupd (K (k + pc t1)) t1) = NONE`,
  CHEAT_TAC);;

(* HOL4 lab_filterProofScript.sml:594-602: a proof *)

(* HOL4 lab_filterProofScript.sml:604-612: a proof *)

let share_mem_op_FFI_return_filter_correct = prove
 (`(all_skips (pc t1) (state_code t1) k /\ ~(state_clock t1 = 0) /\
  compile
   t1 = (\c p. s1compile c (filter_skip p)) /\ ~(failed t1) /\
   share_mem_op m r a
     (compile_oracle_fupd (K (\n. (\(a,b). (a,filter_skip b))
       (compile_oracle t1 n))) (compile_fupd (K s1compile)
       (state_code_fupd (K (filter_skip (state_code t1))) (pc_fupd (K
       (adjust_pc (pc t1) (state_code t1))) t1)))) = SOME (FFI_return f
       l,s)) ==>
   (?s2. !k'. share_mem_op m r a (pc_fupd (K (k + pc t1)) t1) =
     SOME (FFI_return f l,s2) /\
   lab_filterProof_state_rel s s2 /\ ~(failed s) /\ ~(failed s2) /\
   share_mem_op m r a (state_clock_fupd (K (k' + state_clock t1))
     (pc_fupd (K (k + pc t1)) t1)) =
     SOME (FFI_return f l,state_clock_fupd (K (k' + state_clock
       s2)) s2))`,
  CHEAT_TAC);;

let share_mem_op_FFI_final_filter_correct = prove
 (`(all_skips (pc t1) (state_code t1) k /\ ~(state_clock t1 = 0) /\
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
   s = state_ffi s2)`,
  CHEAT_TAC);;

(* HOL4 lab_filterProofScript.sml:669-1037: a theorem whose statement
   HOL Light does not read (tools/unstated.py): filter_correct *)

(* HOL4 lab_filterProofScript.sml:1039-1152: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   state_rel_IMP_sem_EQ_sem *)

(* HOL4 lab_filterProofScript.sml:1154-1167: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   filter_skip_semantics *)

let sec_ends_with_label_filter_skip = prove
 (`!code.
   EVERY sec_ends_with_label code ==>
   EVERY sec_ends_with_label (filter_skip code)`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
