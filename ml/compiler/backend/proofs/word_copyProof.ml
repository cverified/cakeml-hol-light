(* ======================================================== *)
(*  word_copyProof: ported from HOL4's
    compiler/backend/proofs/word_copyProofScript.sml
    A proof theory about word_copy.ml, with 3 definitions and 75
    theorems.  Needed by word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_copy
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_copy.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

cake_hide ["addr"; "val"];;

cake_hide_consts
  ["code_buffer","code_buffer";
   "compile","backend_compile";
   "compile","bvi_let_compile";
   "compile","bvi_to_data_compile";
   "compile","bvl_const_compile";
   "compile","bvl_handle_compile";
   "compile","bvl_to_bvi_compile";
   "compile","clos_annotate_compile";
   "compile","clos_call_compile";
   "compile","clos_fvs_compile";
   "compile","clos_known_compile";
   "compile","clos_mti_compile";
   "compile","clos_to_bvl_compile";
   "compile","compiler_compile";
   "compile","data_live_compile";
   "compile","data_space_compile";
   "compile","data_to_word_compile";
   "compile","flat_to_clos_compile";
   "compile","lab_to_target_compile";
   "compile","source_to_flat_compile";
   "compile","source_to_source_compile";
   "compile","stack_alloc_compile";
   "compile","stack_names_compile";
   "compile","stack_rawcall_compile";
   "compile","stack_remove_compile";
   "compile","stack_to_lab_compile";
   "compile","word_bignum_compile";
   "compile","word_to_stack_compile";
   "compile","word_to_word_compile";
   "data_buffer","data_buffer";
   "memory","memory"];;

(* HOL4 word_copyProofScript.sml:10: the ML values that the
   definitions below antiquote *)

let CPstate_inv_def = cake_define
  `CPstate_inv cs = (
    (
     // cs.next is a fresh class
     !v c. sptree_lookup v (copy_state_to_eq cs) = SOME c ==> c <
       copy_state_next cs) /\
    (!c. c IN domain (copy_state_from_eq cs) ==> c < copy_state_next
      cs) /\
    (!s c. ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==> c <
      copy_state_next cs) /\
    (
     // if representative of equiv class c is var v,
     // then class of v is c
     !c v. sptree_lookup c (copy_state_from_eq cs) = SOME v ==>
      sptree_lookup v (copy_state_to_eq cs) = SOME c))`;;

(* As a corollary, different classes have different representatives *)
(* unused *)
let unique_rep = cake_theorem "unique_rep[local]"
  (fun () ->
    `CPstate_inv cs ==>
     c IN domain (copy_state_from_eq cs) /\
     c' IN domain (copy_state_from_eq cs) /\ ~(c = c') ==>
       ~(sptree_lookup c (copy_state_from_eq cs) = sptree_lookup c'
       (copy_state_from_eq cs))`)
  CHEAT_TAC;;

let empty_eq_inv = cake_theorem "empty_eq_inv"
  (fun () ->
    `CPstate_inv empty_eq`)
  CHEAT_TAC;;

let remove_eq_inv = cake_theorem "remove_eq_inv"
  (fun () ->
    `!cs v. CPstate_inv cs ==>
     CPstate_inv (remove_eq cs v)`)
  CHEAT_TAC;;

let remove_eqs_inv = cake_theorem "remove_eqs_inv"
  (fun () ->
    `!vv cs. CPstate_inv cs ==>
       CPstate_inv (remove_eqs cs vv)`)
  CHEAT_TAC;;

let n_lt_n1 = cake_theorem "n_lt_n1[local]"
  (fun () ->
    `(n:num) < n + 1 /\
     ((x:num) < y /\ y < z ==> x < z)`)
  CHEAT_TAC;;

let set_eq_inv = cake_theorem "set_eq_inv"
  (fun () ->
    `CPstate_inv cs /\
     sptree_lookup t (copy_state_to_eq cs) = NONE ==>
     CPstate_inv (set_eq cs t s)`)
  CHEAT_TAC;;

let merge_eqs_inv = cake_theorem "merge_eqs_inv"
  (fun () ->
    `CPstate_inv cs1 /\
     CPstate_inv cs2 ==>
     CPstate_inv (merge_eqs cs1 cs2)`)
  CHEAT_TAC;;

let set_store_eq_inv = cake_theorem "set_store_eq_inv"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_inv (set_store_eq cs name e)`)
  CHEAT_TAC;;

let same_classD = cake_theorem "same_classD"
  (fun () ->
    `CPstate_inv cs /\
     lookup_eq cs x = lookup_eq cs y ==>
     x = y \/ (~(x = y) /\
     (?c rep.
       sptree_lookup x (copy_state_to_eq cs) = SOME c /\
       sptree_lookup y (copy_state_to_eq cs) = SOME c /\
       sptree_lookup c (copy_state_from_eq cs) = SOME rep))`)
  CHEAT_TAC;;

let same_classD' = cake_theorem "same_classD'"
  (fun () ->
    `CPstate_inv cs /\
     lookup_store_eq cs x = SOME (lookup_eq cs y) ==>
     (?c rep.
       ALOOKUP (copy_state_store_to_eq cs) x = SOME c /\
       sptree_lookup y (copy_state_to_eq cs) = SOME c /\
       sptree_lookup c (copy_state_from_eq cs) = SOME rep)`)
  CHEAT_TAC;;

let lookup_eqI = cake_theorem "lookup_eqI"
  (fun () ->
    `!cs r v.
     (r = v /\ sptree_lookup v (copy_state_to_eq cs) = NONE) \/
       (?c. sptree_lookup v (copy_state_to_eq cs) = SOME c /\
       sptree_lookup c (copy_state_from_eq cs) = SOME r) ==>
     lookup_eq cs v = r`)
  CHEAT_TAC;;

let both_alloc_vars_def = cake_define
  `both_alloc_vars (t,s) = (is_alloc_var t /\ is_alloc_var s)`;;

let lookup_eq_set_eq_not_alloc_var =
  cake_theorem "lookup_eq_set_eq_not_alloc_var"
  (fun () ->
    `~(both_alloc_vars (t,s)) ==>
     lookup_eq (set_eq cs t s) v =
     lookup_eq cs v`)
  CHEAT_TAC;;

(* t := s *)
let lookup_eq_set_eq_is_alloc_var1 =
  cake_theorem "lookup_eq_set_eq_is_alloc_var1"
  (fun () ->
    `CPstate_inv cs /\
     both_alloc_vars (t,s) ==>
     sptree_lookup t (copy_state_to_eq cs) = NONE ==>
     lookup_eq cs s = lookup_eq cs v ==>
     lookup_eq (set_eq cs t s) v = t`)
  CHEAT_TAC;;

let lookup_eq_set_eq_is_alloc_var2 =
  cake_theorem "lookup_eq_set_eq_is_alloc_var2"
  (fun () ->
    `CPstate_inv cs /\
     both_alloc_vars (t,s) ==>
     sptree_lookup t (copy_state_to_eq cs) = NONE ==> ~(v = t) ==>
       ~(lookup_eq cs s = lookup_eq cs v) ==>
     lookup_eq (set_eq cs t s) v = lookup_eq cs v`)
  CHEAT_TAC;;

let lookup_eq_set_eq_t = cake_theorem "lookup_eq_set_eq_t"
  (fun () ->
    `CPstate_inv cs /\
     both_alloc_vars (t,s) ==>
     lookup_eq (set_eq cs t s) t = t`)
  CHEAT_TAC;;

let lookup_eq_set_eq_s = cake_theorem "lookup_eq_set_eq_s"
  (fun () ->
    `CPstate_inv cs /\
     both_alloc_vars (t,s) ==>
     sptree_lookup t (copy_state_to_eq cs) = NONE ==>
     lookup_eq (set_eq cs t s) s = t`)
  CHEAT_TAC;;

let lookup_eq_set_eqD = cake_theorem "lookup_eq_set_eqD"
  (fun () ->
    `CPstate_inv cs ==>
     sptree_lookup t (copy_state_to_eq cs) = NONE ==>
     lookup_eq (set_eq cs t s) v = r ==>
     (r = t ==> v = t \/ lookup_eq cs v = lookup_eq cs s) /\
     (~(r = t) ==> r = lookup_eq cs v)`)
  CHEAT_TAC;;

let CPstate_models_def = cake_define
  `CPstate_models cs S <=>
   (!v c vrep.
     sptree_lookup v (copy_state_to_eq cs) = SOME c ==>
     sptree_lookup c (copy_state_from_eq cs) = SOME vrep ==>
     sptree_lookup v (wordSem_state_locals S) = sptree_lookup vrep
       (wordSem_state_locals S)) /\
   (!s c vrep.
     ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==>
     sptree_lookup c (copy_state_from_eq cs) = SOME vrep ==>
     FLOOKUP (wordSem_state_store S) s = sptree_lookup vrep
       (wordSem_state_locals S))`;;

let CPstate_models_with_const =
  cake_theorem "CPstate_models_with_const[simp]"
  (fun () ->
    `CPstate_models cs (wordSem_state_locals_size_fupd (K ls) s) =
  (CPstate_models cs s) /\
     CPstate_models cs (wordSem_state_fp_regs_fupd (K fp) s) =
       CPstate_models cs s /\
     CPstate_models cs (stack_fupd (K xs) s) = CPstate_models cs s
       /\
     CPstate_models cs (wordSem_state_stack_limit_fupd (K sl) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_stack_max_fupd (K sm) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_stack_size_fupd (K ssize) s)
       = CPstate_models cs s /\
     CPstate_models cs (wordSem_state_memory_fupd (K m) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_mdomain_fupd (K md) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_sh_mdomain_fupd (K smd) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_permute_fupd (K p) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_compile_fupd (K c) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_compile_oracle_fupd (K co) s)
       = CPstate_models cs s /\
     CPstate_models cs (wordSem_state_code_buffer_fupd (K cb) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_data_buffer_fupd (K db) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_gc_fun_fupd (K g) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_handler_fupd (K hd) s) =
       CPstate_models cs s /\
     CPstate_models cs (state_clock_fupd (K clk) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_termdep_fupd (K tdep) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_code_fupd (K cd) s) =
       CPstate_models cs s /\
     CPstate_models cs (wordSem_state_be_fupd (K b) s) =
       CPstate_models cs s /\
     CPstate_models cs (state_ffi_fupd (K ffi) s) =
       CPstate_models cs s`)
  CHEAT_TAC;;

let CPstate_model = cake_theorem "CPstate_model"
  (fun () ->
    `CPstate_models cs st ==>
     sptree_lookup (lookup_eq cs v) (wordSem_state_locals st) =
     sptree_lookup v (wordSem_state_locals st)`)
  CHEAT_TAC;;

let CPstate_modelsI = cake_theorem "CPstate_modelsI"
  (fun () ->
    `CPstate_inv cs /\
     (!x y.
       lookup_eq cs x = lookup_eq cs y ==>
       sptree_lookup x (wordSem_state_locals st) = sptree_lookup y
         (wordSem_state_locals st)) /\
     (!x y.
       lookup_store_eq cs x = SOME (lookup_eq cs y) ==>
       FLOOKUP (wordSem_state_store st) x = sptree_lookup y
         (wordSem_state_locals st)) ==>
     CPstate_models cs st`)
  CHEAT_TAC;;

let CPstate_modelsD = cake_theorem "CPstate_modelsD"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st ==>
     (!x y.
       lookup_eq cs x = lookup_eq cs y ==>
       sptree_lookup x (wordSem_state_locals st) = sptree_lookup y
         (wordSem_state_locals st)) /\
     (!x y.
       lookup_store_eq cs x = SOME (lookup_eq cs y) ==>
       FLOOKUP (wordSem_state_store st) x = sptree_lookup y
         (wordSem_state_locals st))`)
  CHEAT_TAC;;

let remove_eq_model = cake_theorem "remove_eq_model"
  (fun () ->
    `CPstate_models cs st ==>
     CPstate_models (remove_eq cs t) st`)
  CHEAT_TAC;;

let remove_eq_model_insert' = cake_theorem "remove_eq_model_insert'"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st /\ wordSem_state_locals
     (st':('a,'b,'c)wordSem_state) =
       sptree_insert t val (wordSem_state_locals
         (st:('a,'b,'c)wordSem_state)) /\ wordSem_state_store
     st' = wordSem_state_store st ==>
     CPstate_models (remove_eq cs t) st'`)
  CHEAT_TAC;;

let remove_eq_model_insert = cake_theorem "remove_eq_model_insert"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     CPstate_models (remove_eq cs t)
     (wordSem_state_locals_fupd (K (sptree_insert t val
       (wordSem_state_locals st))) st)`)
  CHEAT_TAC;;

let remove_eq_model_set_var = cake_theorem "remove_eq_model_set_var"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st ==>
     CPstate_models (remove_eq cs t) (wordSem_set_var t val st)`)
  CHEAT_TAC;;

let CPstate_models_same = cake_theorem "CPstate_models_same"
  (fun () ->
    `CPstate_models cs st /\ wordSem_state_locals
     st' = wordSem_state_locals st /\ wordSem_state_store
     st' = wordSem_state_store st ==>
     CPstate_models cs st'`)
  CHEAT_TAC;;

let set_fp_var_model = cake_theorem "set_fp_var_model"
  (fun () ->
    `CPstate_models cs st ==>
     CPstate_models cs (wordSem_set_fp_var t val st)`)
  CHEAT_TAC;;

let merge_eqs_model1 = cake_theorem "merge_eqs_model1"
  (fun () ->
    `CPstate_models cs1 st ==>
     CPstate_models (merge_eqs cs1 cs2) st`)
  CHEAT_TAC;;

let merge_eqs_model2 = cake_theorem "merge_eqs_model2"
  (fun () ->
    `CPstate_models cs2 st ==>
     CPstate_models (merge_eqs cs1 cs2) st`)
  CHEAT_TAC;;

let set_eq_store_to_eq = cake_theorem "set_eq_store_to_eq[simp]"
  (fun () ->
    `copy_state_store_to_eq
       (set_eq cs t s) = copy_state_store_to_eq cs`)
  CHEAT_TAC;;

let lookup_eq_remove_eq_t = cake_theorem "lookup_eq_remove_eq_t"
  (fun () ->
    `CPstate_inv cs /\
     lookup_eq (remove_eq cs t) x = t ==>
     x = t`)
  CHEAT_TAC;;

let lookup_store_eq_set_eqD = cake_theorem "lookup_store_eq_set_eqD"
  (fun () ->
    `CPstate_inv cs ==>
     sptree_lookup t (copy_state_to_eq cs) = NONE ==>
     lookup_store_eq (set_eq cs t s) v = SOME r ==>
     (r = t ==> lookup_store_eq cs v = SOME (lookup_eq cs s)) /\
     (~(r = t) ==> lookup_store_eq cs v = SOME r)`)
  CHEAT_TAC;;

let copy_prop_move_model_aux = cake_theorem "copy_prop_move_model_aux"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st /\
     both_alloc_vars (t,s) /\
     sptree_lookup s (wordSem_state_locals st) = SOME sval ==>
     CPstate_models (set_eq (remove_eq cs t) t s)
       (wordSem_state_locals_fupd (K (sptree_insert t sval
       (wordSem_state_locals st))) st)`)
  CHEAT_TAC;;

let set_eq_remove_eq_models = cake_theorem "set_eq_remove_eq_models"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st /\
     sptree_lookup s (wordSem_state_locals st) = SOME sval ==>
     CPstate_models (set_eq (remove_eq cs t) t s)
       (wordSem_state_locals_fupd (K (sptree_insert t sval
       (wordSem_state_locals st))) st)`)
  CHEAT_TAC;;

let lookup_eq_idempotent = cake_theorem "lookup_eq_idempotent"
  (fun () ->
    `CPstate_inv cs ==>
     lookup_eq cs (lookup_eq cs x) = lookup_eq cs x`)
  CHEAT_TAC;;

let CPstate_modelsD_get_var = cake_theorem "CPstate_modelsD_get_var"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st ==>
     wordSem_get_var (lookup_eq cs x) st = wordSem_get_var x st`)
  CHEAT_TAC;;

let CPstate_modelsD_get_vars = cake_theorem "CPstate_modelsD_get_vars"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st ==>
     wordSem_get_vars (MAP (lookup_eq cs) xs) st =
       wordSem_get_vars xs st`)
  CHEAT_TAC;;

let CPstate_modelsD_get_var_imm =
  cake_theorem "CPstate_modelsD_get_var_imm"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st ==>
     wordSem_get_var_imm (lookup_eq_imm cs x) st =
       wordSem_get_var_imm x st`)
  CHEAT_TAC;;

let CPstate_modelsD_Var = cake_theorem "CPstate_modelsD_Var"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st ==>
     wordSem_word_exp st (Var (lookup_eq cs x)) =
       wordSem_word_exp st (Var x)`)
  CHEAT_TAC;;

let CPstate_modelsD_lookup_eq_imm =
  cake_theorem "CPstate_modelsD_lookup_eq_imm"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     wordSem_word_exp st (match lookup_eq_imm cs x with Reg r ->
       Var r | Imm w -> Const w) =
     wordSem_word_exp st (match x with Reg r -> Var r | Imm w ->
       Const w)`)
  CHEAT_TAC;;

let MAP_get_var_eqD = cake_theorem "MAP_get_var_eqD"
  (fun () ->
    `MAP (\x. wordSem_get_var x st) xx = MAP (\x. wordSem_get_var x st)
  yy ==>
     wordSem_get_vars xx st = wordSem_get_vars yy st`)
  CHEAT_TAC;;

let copy_prop_move_eval_aux1 = cake_theorem "copy_prop_move_eval_aux1"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     (!moves' cs'.
     copy_prop_move moves cs = (moves',cs') ==>
     MAP (\x. wordSem_get_var x st) (MAP SND moves') = MAP (\x.
       wordSem_get_var x st) (MAP SND moves))`)
  CHEAT_TAC;;

let copy_prop_move_get_vars = cake_theorem "copy_prop_move_get_vars"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     copy_prop_move moves cs = (moves',cs') ==>
     wordSem_get_vars (MAP SND moves') st = wordSem_get_vars (MAP
       SND moves) st`)
  CHEAT_TAC;;

let copy_prop_move_eval_aux2 = cake_theorem "copy_prop_move_eval_aux2"
  (fun () ->
    `MAP FST moves1 = MAP FST moves2 ==>
     wordSem_get_vars (MAP SND moves1) st = wordSem_get_vars (MAP
       SND moves2) st ==>
     wordSem_evaluate (wordLang_Move pri moves1,st) =
       wordSem_evaluate (wordLang_Move pri moves2,st)`)
  CHEAT_TAC;;

let copy_prop_move_eval_aux3 = cake_theorem "copy_prop_move_eval_aux3"
  (fun () ->
    `!moves' cs'.
     copy_prop_move moves cs = (moves',cs') ==>
     MAP FST moves' = MAP FST moves`)
  CHEAT_TAC;;

let copy_prop_move_eval = cake_theorem "copy_prop_move_eval"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     copy_prop_move moves cs = (moves',cs') ==>
     wordSem_evaluate (wordLang_Move pri moves,st) = (err,st') ==>
     wordSem_evaluate (wordLang_Move pri moves',st) = (err,st')`)
  CHEAT_TAC;;

let lookup_alist_insert_same = cake_theorem "lookup_alist_insert_same"
  (fun () ->
    `~(s IN set_of_list tt) ==>
       sptree_lookup s (alist_insert tt values locals) =
         sptree_lookup s locals`)
  CHEAT_TAC;;

let copy_prop_move_inv = cake_theorem "copy_prop_move_inv"
  (fun () ->
    `CPstate_inv cs ==>
     copy_prop_move moves cs = (moves',cs') ==>
     CPstate_inv cs'`)
  CHEAT_TAC;;

let copy_prop_inst_inv = cake_theorem "copy_prop_inst_inv"
  (fun () ->
    `CPstate_inv cs ==>
     copy_prop_inst ins cs = (prog',cs') ==>
     CPstate_inv cs'`)
  CHEAT_TAC;;

let copy_prop_prog_inv = cake_theorem "copy_prop_prog_inv"
  (fun () ->
    `CPstate_inv cs /\
     copy_prop_prog prog cs = (prog',cs') ==>
     CPstate_inv cs'`)
  CHEAT_TAC;;

(* unused *)
(* HOL4 word_copyProofScript.sml:740-750: code that the source has in
   a comment *)

let empty_eq_model = cake_theorem "empty_eq_model"
  (fun () ->
    `CPstate_models empty_eq st`)
  CHEAT_TAC;;

let copy_prop_move_model = cake_theorem "copy_prop_move_model"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     set_of_list (MAP FST moves) INTER set_of_list (MAP SND moves)
       = {} ==>
     copy_prop_move moves cs = (moves',cs') ==>
     wordSem_get_vars (MAP SND moves) st = SOME values ==>
     CPstate_models cs' (wordSem_set_vars (MAP FST moves) values
       st)`)
  CHEAT_TAC;;

let EVERY_NOT_MEM_D = cake_theorem "EVERY_NOT_MEM_D"
  (fun () ->
    `EVERY (\t. ~(MEM t ss)) tt ==> set_of_list tt INTER set_of_list
  ss = {}`)
  CHEAT_TAC;;

let copy_prop_move_correct = cake_theorem "copy_prop_move_correct"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st /\
     copy_prop_prog (wordLang_Move pri moves) cs = (prog',cs') /\
     wordSem_evaluate (wordLang_Move pri moves,st) = (err,st') ==>
     wordSem_evaluate (prog',st) = (err,st') /\
     (err = NONE ==> CPstate_models cs' st')`)
  CHEAT_TAC;;

let word_exp_cong_Var = cake_theorem "word_exp_cong_Var"
  (fun () ->
    `wordSem_get_var x' st = wordSem_get_var x st ==>
     wordSem_word_exp st (Var x') = wordSem_word_exp st (Var x)`)
  CHEAT_TAC;;

let word_exp_cong_Load = cake_theorem "word_exp_cong_Load"
  (fun () ->
    `wordSem_word_exp st addr' = wordSem_word_exp st addr ==>
     wordSem_word_exp st (Load addr') = wordSem_word_exp st (Load
       addr)`)
  CHEAT_TAC;;

let word_exp_cong_Op = cake_theorem "word_exp_cong_Op"
  (fun () ->
    `MAP (wordSem_word_exp st) aa' = MAP (wordSem_word_exp st) aa ==>
     wordSem_word_exp st (wordLang_Op op aa') = wordSem_word_exp
       st (wordLang_Op op aa)`)
  CHEAT_TAC;;

let word_exp_cong_Shift = cake_theorem "word_exp_cong_Shift"
  (fun () ->
    `wordSem_word_exp st e' = wordSem_word_exp st e ==>
     wordSem_word_exp st e2' = wordSem_word_exp st e2 ==>
     wordSem_word_exp st (Shift sh e' e2') = wordSem_word_exp st
       (Shift sh e e2)`)
  CHEAT_TAC;;

(* HOL4 word_copyProofScript.sml:872-895: a proof *)
(*
          let
            val (xty,_) = dom_rng exp_rator_ty
            val case_rand = ISPEC (mk_comb (r, el 1 d)) $ TypeBase.case_rand_of xty
          in
            rw[case_rand]
          end
*)
(* HOL4 word_copyProofScript.sml:904-906: ML code, not ported *)
        (* use appropriate case_cong *)
(* HOL4 word_copyProofScript.sml:908-916: a proof *)

(* "inst" is constant wordSem$inst *)
let copy_prop_inst_eval = cake_theorem "copy_prop_inst_eval"
  (fun () ->
    `!ins cs st prog' cs'.
     CPstate_inv cs ==>
     CPstate_models cs st ==>
     (prog',cs') = copy_prop_inst ins cs ==>
     wordSem_evaluate (prog',st) = wordSem_evaluate (Inst ins,st)`)
  CHEAT_TAC;;

let remove_eq_comm = cake_theorem "remove_eq_comm"
  (fun () ->
    `remove_eq (remove_eq cs x) y = remove_eq (remove_eq cs y) x`)
  CHEAT_TAC;;

let copy_prop_inst_correct = cake_theorem "copy_prop_inst_correct"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st /\
     copy_prop_inst ins cs = (prog',cs') /\
     wordSem_evaluate (Inst ins,st) = (err,st') ==>
     wordSem_evaluate (prog',st) = (err,st') /\
     (err = NONE ==> CPstate_models cs' st')`)
  CHEAT_TAC;;

let remove_eq_model_unset_var = cake_theorem "remove_eq_model_unset_var"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     CPstate_models (remove_eq cs t) (wordSem_unset_var t st)`)
  CHEAT_TAC;;

(* HOL4 word_copyProofScript.sml:966-981: code that the source has in
   a comment *)

let CPstate_modelsD_copy_prop_share =
  cake_theorem "CPstate_modelsD_copy_prop_share"
  (fun () ->
    `CPstate_inv cs ==>
     CPstate_models cs st ==>
     wordSem_word_exp st (copy_prop_share e cs) =
       wordSem_word_exp st e`)
  CHEAT_TAC;;

let lookup_store_eq_SOME = cake_theorem "lookup_store_eq_SOME"
  (fun () ->
    `CPstate_models cs st /\
     lookup_store_eq cs s = SOME v ==>
     FLOOKUP (wordSem_state_store st) s = sptree_lookup v
       (wordSem_state_locals st)`)
  CHEAT_TAC;;

let lookup_remove_eq = cake_theorem "lookup_remove_eq[simp]"
  (fun () ->
    `sptree_lookup n (copy_state_to_eq (remove_eq cs n)) = NONE`)
  CHEAT_TAC;;

let lookup_eq_set_store_eq = cake_theorem "lookup_eq_set_store_eq"
  (fun () ->
    `CPstate_inv cs /\
     is_alloc_var x ==>
     lookup_eq (set_store_eq cs s x) y =
     lookup_eq cs y`)
  CHEAT_TAC;;

let lookup_store_eq_set_store_eq_1 =
  cake_theorem "lookup_store_eq_set_store_eq_1"
  (fun () ->
    `CPstate_inv cs /\
     is_alloc_var x /\
     lookup_store_eq (set_store_eq cs s x) s = SOME y ==>
     lookup_eq cs x = lookup_eq cs y`)
  CHEAT_TAC;;

let lookup_store_eq_set_store_eq_2 =
  cake_theorem "lookup_store_eq_set_store_eq_2"
  (fun () ->
    `CPstate_inv cs /\
     is_alloc_var x /\ ~(s = t) /\
     lookup_store_eq (set_store_eq cs s x) t = SOME y ==>
     lookup_store_eq cs t = SOME y`)
  CHEAT_TAC;;

let set_store_eq_model_set_store =
  cake_theorem "set_store_eq_model_set_store"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st /\
     wordSem_get_var n st = SOME w ==>
     CPstate_models (set_store_eq cs s n) (wordSem_set_store s w
       st)`)
  CHEAT_TAC;;

let lookup_eq_remove_t_same = cake_theorem "lookup_eq_remove_t_same"
  (fun () ->
    `lookup_eq (remove_eq cs t) t = t`)
  CHEAT_TAC;;

let lookup_store_eq_set_store_eq_same =
  cake_theorem "lookup_store_eq_set_store_eq_same"
  (fun () ->
    `sptree_lookup x (copy_state_to_eq cs) = NONE /\
     is_alloc_var x ==>
     lookup_store_eq (set_store_eq cs s x) s = SOME x`)
  CHEAT_TAC;;

let set_store_eq_model_set_var =
  cake_theorem "set_store_eq_model_set_var"
  (fun () ->
    `CPstate_inv cs /\
     CPstate_models cs st /\
     lookup_store_eq cs s = NONE /\
     wordSem_get_store s st = SOME w ==>
     CPstate_models (set_store_eq (remove_eq cs n) s n)
       (wordSem_set_var n w st)`)
  CHEAT_TAC;;

(* Conditional body congruence for Loop: if the body transformation
   preserves semantics when the body doesn't error, then the Loop
   transformation preserves semantics when the Loop doesn't error. *)
let evaluate_Loop_body_cong_err =
  cake_theorem "evaluate_Loop_body_cong_err"
  (fun () ->
    `!(s:('a,'c,'ffi)wordSem_state) names c c' exit_names res s'.
       (!(v:('a,'c,'ffi)wordSem_state) res s'.
          wordSem_evaluate (c,v) = (res,s') /\ ~(res = SOME
            wordSem_Error) ==>
          wordSem_evaluate (c',v) = (res,s')) /\
       wordSem_evaluate (Loop names c exit_names,s) = (res,s') /\
         ~(res = SOME wordSem_Error) ==>
       wordSem_evaluate (Loop names c' exit_names,s) = (res,s')`)
  CHEAT_TAC;;

let copy_prop_correct = cake_theorem "copy_prop_correct"
  (fun () ->
    `!prog cs st prog' cs' err st'.
     CPstate_inv cs /\
     CPstate_models cs st /\
     copy_prop_prog prog cs = (prog',cs') /\ ~(err = SOME
       wordSem_Error) /\
     wordSem_evaluate (prog,st) = (err,st') ==>
     wordSem_evaluate (prog',st) = (err,st') /\
     (err = NONE ==> CPstate_models cs' st')`)
  CHEAT_TAC;;

(* HOL4 word_copyProofScript.sml:1386-1395: a proof *)

(* HOL4 word_copyProofScript.sml:1397: a proof *)

(* Main semantics result *)
let evaluate_copy_prop = cake_theorem "evaluate_copy_prop"
  (fun () ->
    `~(FST (wordSem_evaluate (e,s)) = SOME wordSem_Error) ==>
       wordSem_evaluate (copy_prop e,s) = wordSem_evaluate (e,s)`)
  CHEAT_TAC;;

cake_hide [];;

cake_hide_consts [];;
