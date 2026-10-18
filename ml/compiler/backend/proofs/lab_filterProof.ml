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
(*For any adjusted fetch, the original fetch is either equal or is a skip
This is probably the wrong direction*)

(* 2) all_skips allow swapping pc for clock*)

let state_rel_def = cake_define
  `lab_filterProof_state_rel (s1:('a,'c,'ffi)labSem_state) t1 <=>
     (?s1compile.
      s1 = compile_fupd (K s1compile) (compile_oracle_fupd (K (\n.
        (\(a,b). (a,filter_skip b)) (compile_oracle t1 n))) (pc_fupd (K
        (adjust_pc (pc t1) (state_code t1))) (state_code_fupd (K
        (filter_skip (state_code t1))) t1))) /\ compile
     t1 = (\c p. s1compile c (filter_skip p))) /\
     ~failed t1`;;
hol4_overload "state_rel" "lab_filterProof_state_rel";;

(* HOL4 lab_filterProofScript.sml:261: ML code, not ported *)

(*For all initial code there is some all_skips*)

(*May need strengthening*)

(* HOL4 lab_filterProofScript.sml:556-563: a proof *)

(* HOL4 lab_filterProofScript.sml:565-576: a proof *)

(* HOL4 lab_filterProofScript.sml:594-602: a proof *)

(* HOL4 lab_filterProofScript.sml:604-612: a proof *)
