(* ======================================================== *)
(*  word_instProof: ported from HOL4's
    compiler/backend/proofs/word_instProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_inst
*)

needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "semantics/ast.ml";;

(* resolve ambiguity between semanticsPrimitives$result and
   wordSem$result
   in latter's favour
*)
(* HOL4 word_instProofScript.sml:17: the type abbreviation result,
   which the port expands *)

(* TODO: Move, but some of these are specific instantiations *)

(* Instruction selection and assorted optimisation correctness
0) pull_exp correctness -- this does pull_ops and optimize_consts
1) pull_exp syntax
2) flatten_exp correctness -- makes stuff into binary branching trees
3) flatten_exp syntax -- prove the above property (binary_branch_exp --
  not counted as a "global" syntactic convention since it is only used
  locally here)
4) inst_select_exp and inst_select correctness
5) inst_select syntax -- flat_exp_conventions and full_inst_ok_less
6) three_to_two_reg correctness
7) three_to_two_reg syntax -- two_reg_insts and some preservation ones
*)

(* pull_exp correctness *)

(*In general, any permutation works*)

(*Remove tail recursion to make proof easier...*)
let pull_ops_simp_def = cake_define_list
  [`pull_ops_simp op [] = []`;
   `pull_ops_simp op (x :: xs) =
        (match x with (wordLang_Op op' ls) -> (if op = op' then
          ls ++ (pull_ops_simp op xs) else x :: (pull_ops_simp op
          xs)) | _2 -> x :: (pull_ops_simp op xs))`];;

(* TODO: Maybe move to props, if these are needed elsewhere *)

(* Done with pull_ops, next is optimize_consts *)

(* pull_exp syntax *)

(* HOL4 word_instProofScript.sml:341-346: a proof *)

(* flatten_exp correctness *)

(*All ops are 2 args. Technically, we should probably check that Sub has
   2 args. However, the semantics already checks that and it will get
   removed later*)
let _ = size_thms "wordLang_exp";;
(* HOL4 word_instProofScript.sml:403-409: the tactic that proves the
   termination *)
let binary_branch_exp_def = cake_define_wf
  `MEASURE (wordLang_exp_size ARB)`
  `binary_branch_exp exp =
        match exp with
          wordLang_Op asm_Sub exps -> EVERY (binary_branch_exp) exps
        | (wordLang_Op op xs) -> (LENGTH xs = 2 /\ EVERY
          (binary_branch_exp) xs)
        | (Load exp) -> binary_branch_exp exp
        | (Shift shift' exp nexp) -> (binary_branch_exp exp /\
          binary_branch_exp nexp)
        | exp -> T`;;

(* flatten_exp syntax *)

(* inst_select correctness
  Main difficulty: Dealing with multiple choice of optimizations,
    depending on whether we are allowed to use them w.r.t. to the asm
    configuration
*)

(*  Main semantics theorem for inst selection:
    The inst-selected program gives same result but
    with possibly more locals used
*)

(* HOL4 word_instProofScript.sml:751-767: a proof *)

(* HOL4 word_instProofScript.sml:769-786: a proof *)

(* HOL4 word_instProofScript.sml:788-878: a proof *)

(* HOL4 word_instProofScript.sml:880-888: a proof *)

(* HOL4 word_instProofScript.sml:890-900: a proof *)

(* HOL4 word_instProofScript.sml:902-974: a proof *)

(* HOL4 word_instProofScript.sml:976-982: a proof *)

(* HOL4 word_instProofScript.sml:1006-1021: a proof *)
  (* ret=SOME: full call *)
(* HOL4 word_instProofScript.sml:1023-1064: a proof *)

(* HOL4 word_instProofScript.sml:1133-1138: a proof *)

(* HOL4 word_instProofScript.sml:1140: a proof *)

(* three_to_two_reg semantics *)

(*Semantics preservation*)
