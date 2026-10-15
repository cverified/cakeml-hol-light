(* ======================================================== *)
(*  lab_filterProof: ported from HOL4's
    compiler/backend/proofs/lab_filterProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for lab_filter
*)

needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_filter.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/pegexec.ml";;

let adjust_pc_def = cake_define
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
  `all_skips pc code k <=>
   (!x y. ~(asm_fetch_aux (pc + k) code = SOME (labLang_Asm (Asmi
     (Inst Skip)) x y))) /\
   (!i. i < k ==>
     (?x y.
     asm_fetch_aux (pc + i) code = SOME (labLang_Asm (Asmi (Inst
       Skip)) x y)))`;;

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
(*For any adjusted fetch, the original fetch is either equal or is a
   skip
This is probably the wrong direction*)

(* 2) all_skips allow swapping pc for clock*)

let state_rel_def = cake_define
  `lab_filterProof_state_rel (s1:('a,'c,'ffi)labSem_state) t1 <=>
     (?s1compile.
      s1 = ?_compile_fupd (K s1compile) (?_compile_oracle_fupd (K
        (\n. (\(a,b). (a,filter_skip b)) (?_compile_oracle t1 n)))
        (?_pc_fupd (K (adjust_pc (?_pc t1) (?_code t1))) (?_code_fupd (K
        (filter_skip (?_code t1))) t1))) /\ ?_compile
     t1 = (\c p. s1compile c (filter_skip p))) /\
     ~?_failed t1`;;

(* HOL4 ML code, not ported:
val all_skips_evaluate_0 = all_skips_evaluate |>SIMP_RULE std_ss
  [PULL_FORALL]|>(Q.SPECL[`k`,`s`,`0`])|>GEN_ALL|>SIMP_RULE std_ss[]
*)

(*For all initial code there is some all_skips*)

(*May need strengthening*)

(* HOL4 ML code, not ported:
val same_inst_tac =
  full_simp_tac(srw_ss())[asm_fetch_def,state_rel_def
    ,state_component_equality]>>
  rev_full_simp_tac(srw_ss())[]>>
  imp_res_tac asm_fetch_aux_eq2>>
  imp_res_tac all_skips_evaluate_0>>
  srw_tac[][]>>qexists_tac`k`>>full_simp_tac(srw_ss())[]>>
  rev_full_simp_tac(srw_ss())[ADD_COMM]>>
  simp[Once evaluate_def,asm_fetch_def];
*)

(* HOL4 ML code, not ported:
val upd_pc_tac =
  first_assum(qspec_then`0` assume_tac)>>full_simp_tac(srw_ss())[]>>
  qmatch_assum_abbrev_tac`evaluate aa = evaluate bb`>>
  first_x_assum(qspec_then`bb` mp_tac)>>
  impl_tac>-
  (simp[inc_pc_def,dec_clock_def,Abbr`bb`,state_component_equality])>>
  srw_tac[][Abbr`bb`]>>
  qexists_tac`k+k'`>>qexists_tac`t2`>>full_simp_tac(srw_ss())[]>>
  first_x_assum(qspec_then`k'` assume_tac)>>
  `k'+t1.clock-1 = k'+(t1.clock -1)` by DECIDE_TAC>>
  full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
  metis_tac[arithmeticTheory.ADD_COMM,arithmeticTheory.ADD_ASSOC];
*)

(* HOL4 ML code, not ported:
val share_mem_load_filter_correct_tac =
  qexists `t1 with
          <|regs := t1.regs⦇r ↦ Word (word_of_bytes F 0w l)⦈;
            pc := k + (t1.pc + 1); ffi := f; clock := t1.clock − 1|>` >>
  rw[] >>
  qexists `s1compile` >>
  rw[state_component_equality] >>
  drule adjust_pc_all_skips >>
  gvs[];
*)

(* HOL4 ML code, not ported:
val share_mem_store_filter_correct_tac =
  qexists `t1 with
          <|pc := k + (t1.pc + 1); ffi := f;
            clock := t1.clock − 1|>` >>
  rw[] >>
  qexists `s1compile` >>
  rw[state_component_equality] >>
  drule adjust_pc_all_skips >>
  gvs[];
*)
