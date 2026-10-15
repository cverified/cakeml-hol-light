(* ======================================================== *)
(*  word_removeProof: ported from HOL4's
    compiler/backend/proofs/word_removeProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_remove
*)

needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/word_remove.ml";;

let compile_state_def = cake_define
  `compile_state clk c s = wordSem_state_compile_fupd (K c)
  (wordSem_state_compile_oracle_fupd (K ((I ## (MAP (I ## I ##
  remove_must_terminate))) o wordSem_state_compile_oracle s))
  (wordSem_state_code_fupd (K (sptree_map (I ## remove_must_terminate)
  (wordSem_state_code s))) (wordSem_state_termdep_fupd (K 0) (clock_fupd
  (K (clock s + clk))
     s))))`;;

(* HOL4 ML code, not ported:
Resume word_remove_correct[Loop]:
  Cases_on `cut_state (names,LN) s` \\ fs[] \\
  pairarg_tac \\ fs[] \\
  `x.compile = s.compile` by
    (fs[cut_state_def,cut_env_def] \\ every_case_tac \\ gvs[]) \\
  reverse (Cases_on `cont_loop res'` \\ fs[])
  >- ( (* not cont_loop *)
    Cases_on `res' = SOME Error` \\
    gvs[exit_loop_def,cont_loop_def] \\
    fs[] \\ qexists_tac `clk` \\ fs[cont_loop_def] \\
    every_case_tac \\ gvs[cont_loop_def,exit_loop_def] )
  >- ( (* cont_loop *)
    `res' <> SOME Error /\ res' <> SOME TimeOut` by
      (Cases_on `res'` \\ gvs[cont_loop_def] \\
       Cases_on `x'` \\ gvs[cont_loop_def]) \\
    `s1.compile = x.compile` by (imp_res_tac evaluate_consts \\ fs[]) \\
    fs[] \\
    reverse (Cases_on `s1.clock = 0` \\ fs[])
    >- ( (* clock <> 0, recursive *)
      fs[STOP_def,remove_must_terminate_def] \\
      qexists_tac `clk + clk'` \\
      drule_all evaluate_add_clock_compile_state \\
      disch_then (qspec_then `clk'` (fn th => simp[th]))  \\
      simp[cont_loop_def])
    >- ( (* clock = 0, TimeOut *)
      qexists_tac `clk` \\ simp[cont_loop_def] \\
      every_case_tac \\ gvs[cont_loop_def]) )
QED
*)

(* HOL4 ML code, not ported:
Finalise word_remove_correct;
*)
