(* ======================================================== *)
(*  word_instProof: ported from HOL4's
    compiler/backend/proofs/word_instProofScript.sml
    A proof theory about word_inst.ml, with 2 definitions and 31
    theorems.  Needed by word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_inst
*)

needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "word_instProof"
  ["asm"; "wordConvs"; "wordLang"; "wordProps"; "wordSem";
   "word_inst"];;

let _ = do_list hide_constant ["C"];;

(* resolve ambiguity between semanticsPrimitives$result and wordSem$result
   in latter's favour
*)
(* HOL4 word_instProofScript.sml:17: the type abbreviation result,
   which the port expands *)

(* TODO: Move, but some of these are specific instantiations *)
(* [local] *)
let PERM_SWAP_SIMP = prove
 (`PERM (A ++ (B :: C)) (B :: (A ++ C))`,
  CHEAT_TAC);;

(* [local] *)
let EL_FILTER = prove
 (`!ls x. x < LENGTH (FILTER P ls) ==> P (EL x (FILTER P ls))`,
  CHEAT_TAC);;

(* [local] *)
let PERM_SWAP = prove
 (`PERM (A ++ B ++ C) (B ++ (A ++ C))`,
  CHEAT_TAC);;

(* Instruction selection and assorted optimisation correctness
0) pull_exp correctness -- this does pull_ops and optimize_consts
1) pull_exp syntax
2) flatten_exp correctness -- makes stuff into binary branching trees
3) flatten_exp syntax -- prove the above property (binary_branch_exp -- not counted as a "global" syntactic convention since it is only used locally here)
4) inst_select_exp and inst_select correctness
5) inst_select syntax -- flat_exp_conventions and full_inst_ok_less
6) three_to_two_reg correctness
7) three_to_two_reg syntax -- two_reg_insts and some preservation ones
*)

(* pull_exp correctness *)
(* [local] *)
let convert_sub_ok = prove
 (`!ls.
   wordSem_word_exp s (convert_sub ls) = wordSem_word_exp s
     (wordLang_Op asm_Sub ls)`,
  CHEAT_TAC);;

(*In general, any permutation works*)
(* [local] *)
let word_exp_op_permute_lem = prove
 (`~(op = Sub) ==>
     (!ls ls'.
     PERM ls ls' ==>
     wordSem_word_exp s (wordLang_Op op ls) = wordSem_word_exp s
       (wordLang_Op op ls'))`,
  CHEAT_TAC);;

(*Remove tail recursion to make proof easier...*)
let pull_ops_simp_def = cake_define_list
  [`pull_ops_simp op [] = []`;
   `pull_ops_simp op (x :: xs) =
        (match x with (wordLang_Op op' ls) -> (if op = op' then
          ls ++ (pull_ops_simp op xs) else x :: (pull_ops_simp op
          xs)) | _2 -> x :: (pull_ops_simp op xs))`];;

(* [local] *)
let pull_ops_simp_pull_ops_perm = prove
 (`!ls x.
   PERM (pull_ops op ls x) ((pull_ops_simp op ls) ++ x)`,
  CHEAT_TAC);;

(* [local] *)
let pull_ops_simp_pull_ops_word_exp = prove
 (`~(op = Sub) ==>
     wordSem_word_exp s (wordLang_Op op (pull_ops op ls [])) =
       wordSem_word_exp s (wordLang_Op op (pull_ops_simp op ls))`,
  CHEAT_TAC);;

(* TODO: Maybe move to props, if these are needed elsewhere *)

(* [local] *)
let word_exp_op_mono = prove
 (`~(op = Sub) ==>
     wordSem_word_exp s (wordLang_Op op ls) = wordSem_word_exp s
       (wordLang_Op op ls') ==>
     wordSem_word_exp s (wordLang_Op op (x :: ls)) =
     wordSem_word_exp s (wordLang_Op op (x :: ls'))`,
  CHEAT_TAC);;

(* [local] *)
let the_words_append = prove
 (`!ls ls'.
   the_words (ls ++ ls') =
   (match the_words ls with
     NONE -> NONE | SOME w ->
     (match the_words ls' with
       NONE -> NONE | SOME w' -> SOME (w ++ w')))`,
  CHEAT_TAC);;

(* [local] *)
let word_exp_op_op = prove
 (`~(op = Sub) ==>
     (!ls ls'.
     wordSem_word_exp s (wordLang_Op op ls) = wordSem_word_exp s
       (wordLang_Op op ls') ==>
     wordSem_word_exp s (wordLang_Op op (l ++ ls)) =
     wordSem_word_exp s (wordLang_Op op ((wordLang_Op op l) ::
       ls')))`,
  CHEAT_TAC);;

(* [local] *)
let pull_ops_ok = prove
 (`~(op = Sub) ==>
     (!ls. wordSem_word_exp s (wordLang_Op op (pull_ops op ls [])) =
            wordSem_word_exp s (wordLang_Op op ls))`,
  CHEAT_TAC);;

(* Done with pull_ops, next is optimize_consts *)

(* [local] *)
let word_exp_swap_head = prove
 (`!B. ~(op = Sub) ==>
   wordSem_word_exp s (wordLang_Op op A) = SOME (wordLang_Word w) ==>
   wordSem_word_exp s (wordLang_Op op (B ++ A)) = wordSem_word_exp
     s (wordLang_Op op (Const w :: B))`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_is_const_word_exp = prove
 (`!ls. EVERY word_inst_is_const ls ==>
   EVERY IS_SOME (MAP (\a. wordSem_word_exp s a) ls)`,
  CHEAT_TAC);;

(* [local] *)
let all_consts_simp = prove
 (`~(op = Sub) ==>
     (!ls.
     EVERY word_inst_is_const ls ==>
     wordSem_word_exp s (wordLang_Op op ls) =
     SOME (wordLang_Word (THE (wordLang_word_op op (MAP rm_const
       ls)))))`,
  CHEAT_TAC);;

(* [local] *)
let word_exp_reduce_const = prove
 (`wordSem_word_exp s (wordLang_Op op (Const w :: rest)) = SOME x ==>
   wordSem_word_exp s (reduce_const op w rest) = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let optimize_consts_ok = prove
 (`~(op = Sub) /\ wordSem_word_exp s (wordLang_Op op ls) = SOME x ==>
     wordSem_word_exp s (optimize_consts op ls) = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let pull_exp_ok = prove
 (`!exp s x.
   wordSem_word_exp s exp = SOME x ==>
   wordSem_word_exp s (pull_exp exp) = SOME x`,
  CHEAT_TAC);;

(* pull_exp syntax *)
(* [local] *)
let convert_sub_every_var_exp = prove
 (`!ls.
   (!x. MEM x ls ==> every_var_exp P x) ==>
   every_var_exp P (convert_sub ls)`,
  CHEAT_TAC);;

(* [local] *)
let optimize_consts_every_var_exp = prove
 (`!ls.
   (!x. MEM x ls ==> every_var_exp P x) ==>
   every_var_exp P (optimize_consts op ls)`,
  CHEAT_TAC);;

(* HOL4 word_instProofScript.sml:341-346: a theorem that HOL4 states
   as the value of an ML expression: pull_ops_every_var_exp *)

(* [local] *)
let pull_exp_every_var_exp = prove
 (`!exp.
   every_var_exp P exp ==>
   every_var_exp P (pull_exp exp)`,
  CHEAT_TAC);;

(* flatten_exp correctness *)
(* [local] *)
let flatten_exp_ok = prove
 (`!exp s x.
   wordSem_word_exp s exp = SOME x ==>
   wordSem_word_exp s (flatten_exp exp) = SOME x`,
  CHEAT_TAC);;

(*All ops are 2 args. Technically, we should probably check that Sub has 2 args. However, the semantics already checks that and it will get removed later*)
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
(* [local] *)
let flatten_exp_binary_branch_exp = prove
 (`!exp.
   binary_branch_exp (flatten_exp exp)`,
  CHEAT_TAC);;

(* [local] *)
let flatten_exp_every_var_exp = prove
 (`!exp.
   every_var_exp P exp ==>
   every_var_exp P (flatten_exp exp)`,
  CHEAT_TAC);;

(* inst_select correctness
  Main difficulty: Dealing with multiple choice of optimizations, depending on whether we are allowed to use them w.r.t. to the asm configuration
*)
(* [local] *)
let inst_select_exp_thm = prove
 (`!c tar temp exp s w loc.
   binary_branch_exp exp /\
   every_var_exp (\x. x < temp) exp /\
   locals_rel temp (wordSem_state_locals s) loc /\
   wordSem_word_exp s exp = SOME w ==>
   (?loc'.
   wordSem_evaluate ((inst_select_exp c tar temp
     exp),wordSem_state_locals_fupd (K loc) s) = ((NONE:('a
     wordSem_result) option),wordSem_state_locals_fupd (K loc') s) /\
   (!x.
     if x = tar then sptree_lookup x loc' = SOME w else if x < temp
       then sptree_lookup x loc' = sptree_lookup x
       (wordSem_state_locals s) else T))`,
  CHEAT_TAC);;

(* [local] *)
let locals_rm = prove
 (`wordSem_state_locals_fupd (K (wordSem_state_locals D))
     D = D`,
  CHEAT_TAC);;

(*  Main semantics theorem for inst selection:
    The inst-selected program gives same result but
    with possibly more locals used
*)
let inst_select_thm = prove
 (`!c temp prog st res rst loc.
   wordSem_evaluate (prog,st) = (res,rst) /\
   wordLang_every_var (\x. x < temp) prog /\ ~(res = SOME
     wordSem_Error) /\
   locals_rel temp (wordSem_state_locals st) loc ==>
   (?loc'.
   wordSem_evaluate (inst_select c temp
     prog,wordSem_state_locals_fupd (K loc) st) =
     (res,wordSem_state_locals_fupd (K loc') rst) /\
   (match res with
     NONE -> locals_rel temp (wordSem_state_locals rst) loc' | SOME
       (Break _3) -> locals_rel temp (wordSem_state_locals rst) loc' |
       SOME (Continue _4) -> locals_rel temp (wordSem_state_locals
       rst) loc' | SOME _5 -> wordSem_state_locals rst = loc'))`,
  CHEAT_TAC);;

(* HOL4 word_instProofScript.sml:751-767: a proof *)

(* HOL4 word_instProofScript.sml:769-786: a proof *)

(* HOL4 word_instProofScript.sml:788-878: a proof *)

(* HOL4 word_instProofScript.sml:880-888: a proof *)

(* HOL4 word_instProofScript.sml:890-900: a proof *)

(* HOL4 word_instProofScript.sml:902-974: a proof *)

(* HOL4 word_instProofScript.sml:976-982: a proof *)


(* [local] *)
let locals_rel_cut_envs_local = prove
 (`locals_rel temp loc loc' /\
   every_name (\x. x < temp) names /\
   cut_envs names loc = SOME x ==>
   cut_envs names loc' = SOME x`,
  CHEAT_TAC);;

(* HOL4 word_instProofScript.sml:1006-1021: a proof *)
  (* ret=SOME: full call *)
(* HOL4 word_instProofScript.sml:1023-1064: a proof *)

let inst_select_Loop_helper = prove
 (`!(s:('a,'c,'ffi)wordSem_state) names prog exit_names res rst c temp
  loc.
     (!(st:('a,'c,'ffi)wordSem_state) res rst loc.
        wordSem_evaluate (prog,st) = (res,rst) /\ ~(res = SOME
          wordSem_Error) /\
        locals_rel temp (wordSem_state_locals st) loc ==>
        (?loc'.
          wordSem_evaluate (inst_select c temp
            prog,wordSem_state_locals_fupd (K loc) st) =
            (res,wordSem_state_locals_fupd (K loc') rst) /\
          (match res with
            NONE -> locals_rel temp (wordSem_state_locals rst) loc' |
              SOME (Break _6) -> locals_rel temp (wordSem_state_locals
              rst) loc' | SOME (Continue _7) -> locals_rel temp
              (wordSem_state_locals rst) loc' | SOME _8 ->
              wordSem_state_locals rst = loc'))) /\
     wordSem_evaluate (Loop names prog exit_names,s) = (res,rst) /\
       ~(res = SOME wordSem_Error) /\
     wordLang_every_var (\x. x < temp) prog /\
     every_name (\x. x < temp) (names,LN) /\
     every_name (\x. x < temp) (exit_names,LN) /\
     locals_rel temp (wordSem_state_locals s) loc ==>
     (?loc'.
       wordSem_evaluate (Loop names (inst_select c temp prog)
         exit_names,wordSem_state_locals_fupd (K loc)
                 s) = (res,wordSem_state_locals_fupd (K loc') rst) /\
       (match res with
         NONE -> locals_rel temp (wordSem_state_locals rst) loc' |
           SOME (Break _9) -> locals_rel temp (wordSem_state_locals
           rst) loc' | SOME (Continue _10) -> locals_rel temp
           (wordSem_state_locals rst) loc' | SOME _11 ->
           wordSem_state_locals rst = loc'))`,
  CHEAT_TAC);;

(* HOL4 word_instProofScript.sml:1133-1138: a proof *)

(* HOL4 word_instProofScript.sml:1140: a proof *)

(* three_to_two_reg semantics *)

let three_to_two_reg_Loop = prove
 (`!(s:('a,'c,'ffi)wordSem_state) names prog exit_names res s'.
     (!(v:('a,'c,'ffi)wordSem_state) res s'.
        wordSem_evaluate (prog,v) = (res,s') /\ ~(res = SOME
          wordSem_Error) ==>
        wordSem_evaluate (three_to_two_reg prog,v) = (res,s')) /\
     wordSem_evaluate (Loop names prog exit_names,s) = (res,s') /\
       ~(res = SOME wordSem_Error) ==>
     wordSem_evaluate (Loop names (three_to_two_reg prog)
       exit_names,s) = (res,s')`,
  CHEAT_TAC);;

(*Semantics preservation*)
let three_to_two_reg_correct = prove
 (`!prog s res s'.
     every_inst distinct_tar_reg prog /\
     wordSem_evaluate (prog,s) = (res,s') /\ ~(res = SOME
       wordSem_Error) ==>
     wordSem_evaluate (three_to_two_reg prog,s) = (res,s')`,
  CHEAT_TAC);;

let evaluate_three_to_two_reg_prog = prove
 (`wordSem_evaluate (prog,s) = (res,s') /\ ~(res = SOME wordSem_Error)
  /\
   every_inst distinct_tar_reg prog ==>
   wordSem_evaluate (three_to_two_reg_prog t prog,s) = (res,s')`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
