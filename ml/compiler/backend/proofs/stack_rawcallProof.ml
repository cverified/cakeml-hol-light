(* ======================================================== *)
(*  stack_rawcallProof: ported from HOL4's
    compiler/backend/proofs/stack_rawcallProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for stack_rawcall
*)

needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/semantics/labProps.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_rawcall.ml";;
needs "lib/sptree.ml";;


(* HOL4 ML code, not ported:
val _ = (max_print_depth := 18);
*)

(* HOL4 ML code, not ported:
val word_shift_def = backend_commonTheory.word_shift_def
val theWord_def = wordSemTheory.theWord_def;
val isWord_def = wordSemTheory.isWord_def;
*)

(* HOL4 overload (expanded in the port):
     good_dimindex = misc$good_dimindex *)
(* HOL4 overload (expanded in the port):
     comp = stack_rawcall$comp *)
(* HOL4 overload (expanded in the port):
     compile = stack_rawcall$compile *)
(* HOL4 type abbreviation (expanded in the port):
     prog = α stackLang$prog *)

let state_ok_def = cake_define
  `stack_rawcallProof_state_ok i code <=>
     (!n v.
       sptree_lookup n i = SOME v ==>
       (?p. sptree_lookup n code = SOME (Seq (stackLang_StackAlloc
         v) p)))`;;

let state_rel_def = cake_define
  `stack_rawcallProof_state_rel i s t <=>
     (?c.
       domain c = domain (?_code s) /\
       t = ?_code_fupd (K c) s /\
       stack_rawcallProof_state_ok i (?_code s) /\
       (!n b.
         sptree_lookup n (?_code s) = SOME b ==>
         (?i. stack_rawcallProof_state_ok i (?_code s) /\
             lookup n c = SOME (comp_top i b))))`;;

(* HOL4 ML code, not ported:
val simple_case =
  qexists_tac `0`
  \\ fs [Once
    comp_def,evaluate_def,get_var_def,set_var_def,loc_check_def
    ,mem_load_def,
         alloc_def,gc_def,set_store_def,inst_def,assign_def,word_exp_def
           ,get_vars_def,
         mem_store_def,get_fp_var_def,set_fp_var_def
           ,wordLangTheory.word_op_def,
         store_const_sem_def]
  \\ fs
    [CaseEq"option",CaseEq"word_loc",bool_case_eq,CaseEq"ffi_result"
    ,pair_case_eq,
         CaseEq"inst",CaseEq"arith",IS_SOME_EXISTS,CaseEq"list"
           ,CaseEq"memop",
         CaseEq"addr",CaseEq"fp",CaseEq"binop"] \\ rfs []
  \\ rveq \\ fs []
  \\ simp [state_rel_def,PULL_EXISTS]
  \\ fs [state_rel_thm,state_component_equality,empty_env_def]
  \\ fs
    [state_rel_thm,state_component_equality,empty_env_def,dec_clock_def]
*)
