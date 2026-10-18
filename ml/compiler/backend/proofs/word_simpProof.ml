(* ======================================================== *)
(*  word_simpProof: ported from HOL4's
    compiler/backend/proofs/word_simpProofScript.sml
    A proof theory about word_simp.ml, with 4 definitions and 72
    theorems.  Needed by data_to_word_gcProof.ml,
    word_gcFunctions.ml and word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_simp
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/comparison.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

cake_hide ["dummy"; "memory"];;
(* HOL4 ancestors outside the port: alist *)

(* HOL4 word_simpProofScript.sml:10: the ML values that the
   definitions below antiquote *)

(** verification of Seq_assoc **)

let evaluate_SmartSeq = cake_theorem "evaluate_SmartSeq"
  (fun () ->
    `wordSem_evaluate (SmartSeq p1 p2,s) = wordSem_evaluate (Seq p1
  p2,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let word_simpProof_evaluate_Seq_Skip = cake_theorem "evaluate_Seq_Skip"
  (fun () ->
    `!p1 s. wordSem_evaluate (wordLang_Seq p1 Skip,s) =
  wordSem_evaluate (p1,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let evaluate_Skip_Seq = cake_theorem "evaluate_Skip_Seq"
  (fun () ->
    `wordSem_evaluate (wordLang_Seq Skip p,s) = wordSem_evaluate
  (p,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let evaluate_Loop_body_cong = cake_theorem "evaluate_Loop_body_cong"
  (fun () ->
    `!(s:('a,'c,'ffi)wordSem_state) names c c' exit_names.
     (!(v:('a,'c,'ffi)wordSem_state). wordSem_evaluate (c',v) =
       wordSem_evaluate (c,v)) ==>
     wordSem_evaluate (Loop names c' exit_names,s) =
       wordSem_evaluate (Loop names c exit_names,s)`)
  CHEAT_TAC;;

let evaluate_Loop_body_cong_gc =
  cake_theorem "evaluate_Loop_body_cong_gc"
  (fun () ->
    `!(s:('a,'c,'ffi)wordSem_state) names c c' exit_names.
     (!(v:('a,'c,'ffi)wordSem_state). R (wordSem_state_gc_fun v)
       ==> wordSem_evaluate (c',v) = wordSem_evaluate (c,v)) ==>
     R (wordSem_state_gc_fun s) ==>
     wordSem_evaluate (Loop names c' exit_names,s) =
       wordSem_evaluate (Loop names c exit_names,s)`)
  CHEAT_TAC;;

let evaluate_Seq_assoc_lemma = cake_theorem "evaluate_Seq_assoc_lemma"
  (fun () ->
    `!p1 p2 s. wordSem_evaluate (Seq_assoc p1 p2,s) = wordSem_evaluate
  (Seq p1 p2,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let evaluate_Seq_assoc = cake_theorem "evaluate_Seq_assoc"
  (fun () ->
    `!p s. wordSem_evaluate (Seq_assoc Skip p,s) = wordSem_evaluate
  (p,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let dest_If_Eq_Imm_thm = cake_theorem "dest_If_Eq_Imm_thm"
  (fun () ->
    `dest_If_Eq_Imm x2 = SOME (n,w,p1,p2) <=>
      x2 = If Equal n (Imm w) p1 p2`)
  CHEAT_TAC;;

let dest_If_thm = cake_theorem "dest_If_thm"
  (fun () ->
    `dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5`)
  CHEAT_TAC;;

let dest_Seq_IMP = cake_theorem "dest_Seq_IMP"
  (fun () ->
    `word_simp_dest_Seq p1 = (x1,x2) ==> wordSem_evaluate (p1,s) =
  wordSem_evaluate (Seq x1 x2,(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

let dest_Seq_Assign_Const_IMP = cake_theorem "dest_Seq_Assign_Const_IMP"
  (fun () ->
    `dest_Seq_Assign_Const v p = SOME (q,w) ==>
      wordSem_evaluate (p,s) = wordSem_evaluate (Seq q
        (wordLang_Assign v (wordLang_Const
        w)),(s:('a,'c,'ffi)wordSem_state))`)
  CHEAT_TAC;;

(** verification of const_fp **)

(* gc *)

let is_gc_word_const_def = cake_define_list
  [`is_gc_word_const (wordLang_Loc _3 _4) = T`;
   `is_gc_word_const (wordLang_Word w) = is_gc_const w`];;

let gc_fun_const_ok_def = cake_define
  `gc_fun_const_ok (f:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) =
     (!x y. f x = SOME y ==> EVERY2 (\a b. is_gc_word_const a ==>
       b = a) (FST x) (FST y))`;;


let sf_gc_consts_def = cake_define
  `sf_gc_consts (StackFrame _5 l0 sv h) (StackFrame _6 l0' sw h') =
   (EVERY2 (\(ak,av) (bk,bv). (ak = bk) /\ (is_gc_word_const av
     ==> bv = av)) sv sw /\ l0 = l0' /\ h = h')`;;

(* HOL4 word_simpProofScript.sml:146-152: code that the source has in
   a comment *)

let sf_gc_consts_refl = cake_theorem "sf_gc_consts_refl"
  (fun () ->
    `!x. sf_gc_consts x x`)
  CHEAT_TAC;;

let sf_gc_consts_trans = cake_theorem "sf_gc_consts_trans"
  (fun () ->
    `!a b c. sf_gc_consts a b /\ sf_gc_consts b c ==>
             sf_gc_consts a c`)
  CHEAT_TAC;;

(* Assign *)

let strip_const_thm = cake_theorem "strip_const_thm"
  (fun () ->
    `!xs x s. strip_const xs = SOME x ==> MAP (\a. wordSem_word_exp s
  a) xs = MAP (SOME o wordLang_Word) x`)
  CHEAT_TAC;;

let the_words_thm = cake_theorem "the_words_thm"
  (fun () ->
    `!x. the_words (MAP (SOME o wordLang_Word) x) = SOME x`)
  CHEAT_TAC;;

let const_fp_exp_word_exp = cake_theorem "const_fp_exp_word_exp"
  (fun () ->
    `!e cs s. (!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v s
  = SOME (wordLang_Word w)) ==>
              wordSem_word_exp s (const_fp_exp e cs) =
                wordSem_word_exp s e`)
  CHEAT_TAC;;

let const_fp_exp_word_exp_const =
  cake_theorem "const_fp_exp_word_exp_const"
  (fun () ->
    `!e cs s c. (!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v
  s = SOME (wordLang_Word w)) /\
                const_fp_exp e cs = Const c ==>
                wordSem_word_exp s e = SOME (wordLang_Word c)`)
  CHEAT_TAC;;

(* Move *)

let set_vars_move_NONE = cake_theorem "set_vars_move_NONE"
  (fun () ->
    `!moves x s s' v.
     wordSem_set_vars (MAP FST moves) x s = s' /\
     ALOOKUP moves v = NONE ==>
     wordSem_get_var v s' = wordSem_get_var v s`)
  CHEAT_TAC;;

let set_vars_move_SOME = cake_theorem "set_vars_move_SOME"
  (fun () ->
    `!moves x v w s s'.
     wordSem_set_vars (MAP FST moves) x s = s' /\
     wordSem_get_vars (MAP SND moves) s = SOME x /\
     ALOOKUP moves v = SOME w ==>
     wordSem_get_var v s' = wordSem_get_var w s`)
  CHEAT_TAC;;

let get_var_move_thm = cake_theorem "get_var_move_thm"
  (fun () ->
    `!s s' moves x v.
     wordSem_get_vars (MAP SND moves) s = SOME x /\
     wordSem_set_vars (MAP FST moves) x s = s' ==>
     wordSem_get_var v s' = (match ALOOKUP moves v with SOME w ->
       wordSem_get_var w s | NONE -> wordSem_get_var v s)`)
  CHEAT_TAC;;

let lookup_const_fp_move_cs_NONE =
  cake_theorem "lookup_const_fp_move_cs_NONE"
  (fun () ->
    `!moves v cs cs'.
     ALOOKUP moves v = NONE /\
     sptree_lookup v cs = sptree_lookup v cs' ==>
     sptree_lookup v (const_fp_move_cs moves cs cs') =
       sptree_lookup v cs'`)
  CHEAT_TAC;;

let lookup_const_fp_move_cs_SOME_part =
  cake_theorem "lookup_const_fp_move_cs_SOME_part"
  (fun () ->
    `!moves q cs cs' x.
     ~(MEM q (MAP FST moves)) /\
     sptree_lookup q cs' = x ==>
     sptree_lookup q (const_fp_move_cs moves cs cs') = x`)
  CHEAT_TAC;;

(* TODO: In need of cleanup *)
let lookup_const_fp_move_cs_SOME =
  cake_theorem "lookup_const_fp_move_cs_SOME"
  (fun () ->
    `!moves v w cs cs'.
     ALOOKUP moves v = SOME w /\
     ALL_DISTINCT (MAP FST moves) /\
     sptree_lookup v cs = sptree_lookup v cs' ==>
     sptree_lookup v (const_fp_move_cs moves cs cs') =
       sptree_lookup w cs`)
  CHEAT_TAC;;

let lookup_const_fp_move_cs = cake_theorem "lookup_const_fp_move_cs"
  (fun () ->
    `!v moves cs.
     ALL_DISTINCT (MAP FST moves) ==>
     sptree_lookup v (const_fp_move_cs moves cs cs) = (match
       ALOOKUP moves v with SOME w -> sptree_lookup w cs | NONE ->
       sptree_lookup v cs)`)
  CHEAT_TAC;;

(* If *)

let get_var_imm_cs_imp_get_var_imm =
  cake_theorem "get_var_imm_cs_imp_get_var_imm"
  (fun () ->
    `!x y s cs. (!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v
  s = SOME (wordLang_Word w)) /\
                get_var_imm_cs x cs = SOME y ==>
                wordSem_get_var_imm x s = SOME (wordLang_Word y)`)
  CHEAT_TAC;;

(* Helpful lemmas about locals *)
(*TODO move*)
let get_var_set_var_thm = cake_theorem "get_var_set_var_thm"
  (fun () ->
    `!k1 k2 v s. wordSem_get_var k1 (wordSem_set_var k2 v s) =
                 (if k1 = k2 then SOME v else wordSem_get_var k1
                   s)`)
  CHEAT_TAC;;

let get_var_mem_store_thm = cake_theorem "get_var_mem_store_thm"
  (fun () ->
    `!v addr' x s. wordSem_mem_store addr' x s = SOME s' ==>
                  wordSem_get_var v s' = wordSem_get_var v s`)
  CHEAT_TAC;;

let cs_delete_if_set = cake_theorem "cs_delete_if_set"
  (fun () ->
    `!x v1 v2 s cs w.
     (!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v s =
       SOME (wordLang_Word w)) /\
     sptree_lookup v2 (sptree_delete v1 cs) = SOME w ==>
     wordSem_get_var v2 (wordSem_set_var v1 x s) = SOME
       (wordLang_Word w)`)
  CHEAT_TAC;;

let cs_delete_if_set_x2 = cake_theorem "cs_delete_if_set_x2"
  (fun () ->
    `!x1 x2 v1 v2 v3 s cs w.
     (!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v s =
       SOME (wordLang_Word w)) /\
     sptree_lookup v3 (sptree_delete v2 (sptree_delete v1 cs)) =
       SOME w ==>
     wordSem_get_var v3 (wordSem_set_var v2 x2 (wordSem_set_var
       v1 x1 s)) = SOME (wordLang_Word w)`)
  CHEAT_TAC;;

(* Lookup thms *)

let lookup_inter_eq_some = cake_theorem "lookup_inter_eq_some"
  (fun () ->
    `!m1 m2 k x. sptree_lookup k (inter_eq m1 m2) = SOME x ==>
                 sptree_lookup k m1 = SOME x /\ sptree_lookup k
                   m2 = SOME x`)
  CHEAT_TAC;;

let lookup_filter_v_SOME = cake_theorem "lookup_filter_v_SOME"
  (fun () ->
    `!t k v f. sptree_lookup k (filter_v f t) = SOME v ==> f v`)
  CHEAT_TAC;;

let lookup_filter_v_SOME_imp = cake_theorem "lookup_filter_v_SOME_imp"
  (fun () ->
    `!t k v f. sptree_lookup k (filter_v f t) = SOME v ==>
               sptree_lookup k t = SOME v`)
  CHEAT_TAC;;

(* LIST_REL/EVERY2 thms *)

let LIST_REL_prefix = cake_theorem "LIST_REL_prefix"
  (fun () ->
    `!R l1 l2 l1' l2'. LIST_REL R (l1 ++ l2) (l1' ++ l2') /\
                       LENGTH l1 = LENGTH l1' ==>
                       LIST_REL R l1 l1'`)
  CHEAT_TAC;;

let LIST_REL_append_left = cake_theorem "LIST_REL_append_left"
  (fun () ->
    `!l0 l1 l2 R.
     LIST_REL R (l0 ++ l1) l2 ==>
     LIST_REL R l0 (TAKE (LENGTH l0) l2) /\
     LIST_REL R l1 (DROP (LENGTH l0) l2)`)
  CHEAT_TAC;;

(* Stack thms *)

let push_env_set_store_stack = cake_theorem "push_env_set_store_stack"
  (fun () ->
    `!x1 x2 x3 x4 s. stack (wordSem_push_env x1 x2 (wordSem_set_store
  x3 x4 s)) = stack (wordSem_push_env x1 x2 s)`)
  CHEAT_TAC;;

(*TODO delete*)
let pop_env_stack_gc = cake_theorem "pop_env_stack_gc[local]"
  (fun () ->
    `!s. wordSem_pop_env s = SOME s' ==> wordSem_state_gc_fun s' =
  wordSem_state_gc_fun s`)
  CHEAT_TAC;;

let ALOOKUP_LIST_REL_sf_gc_consts =
  cake_theorem "ALOOKUP_LIST_REL_sf_gc_consts"
  (fun () ->
    `!l1 l2 k v.
     LIST_REL (\(ak,av) (bk,bv). ak = bk /\ (is_gc_word_const av
       ==> bv = av)) l1 l2 /\
     is_gc_word_const v /\
     ALOOKUP l1 k = SOME v ==>
     ALOOKUP l2 k = SOME v`)
  CHEAT_TAC;;

let ALOOKUP_LIST_REL_sf_gc_consts_NONE =
  cake_theorem "ALOOKUP_LIST_REL_sf_gc_consts_NONE"
  (fun () ->
    `!l1 l2 k v.
     LIST_REL (\(ak,av) (bk,bv). ak = bk /\ (is_gc_word_const av
       ==> bv = av)) l1 l2 /\
     ALOOKUP l1 k = NONE ==>
     ALOOKUP l2 k = NONE`)
  CHEAT_TAC;;

let ALL_DISTINCT_PERM_FST = cake_theorem "ALL_DISTINCT_PERM_FST"
  (fun () ->
    `!l. ALL_DISTINCT (MAP FST l) /\ PERM l (f l) ==> ALL_DISTINCT
  (MAP FST (f l))`)
  CHEAT_TAC;;

let ALOOKUP_LIST_REL_value_rel =
  cake_theorem "ALOOKUP_LIST_REL_value_rel"
  (fun () ->
    `!f l' l k v. LIST_REL (\(ak,av) (bk,bv). (ak = bk) /\ (f av ==> bv
  = av)) l' l /\
                  ALOOKUP l' k = SOME v /\
                  f v ==>
                  ALOOKUP l k = SOME v`)
  CHEAT_TAC;;

let ALOOKUP_ALL_DISTINCT_FST_PERM =
  cake_theorem "ALOOKUP_ALL_DISTINCT_FST_PERM"
  (fun () ->
    `!l1 l2. ALL_DISTINCT (MAP FST l1) /\ PERM l1 l2 ==> ALOOKUP l1 =
  ALOOKUP l2`)
  CHEAT_TAC;;

let ALOOKUP_ALL_DISTINCT_FST_PERM_SOME =
  cake_theorem "ALOOKUP_ALL_DISTINCT_FST_PERM_SOME"
  (fun () ->
    `!l1 f k v. ALL_DISTINCT (MAP FST l1) /\
                PERM l1 (f l1) /\
                ALOOKUP l1 k = SOME v ==>
                ALOOKUP (f l1) k = SOME v`)
  CHEAT_TAC;;

let pop_env_gc_fun = cake_theorem "pop_env_gc_fun"
  (fun () ->
    `!s s'. wordSem_pop_env s = SOME s' ==> wordSem_state_gc_fun s' =
  wordSem_state_gc_fun s`)
  CHEAT_TAC;;

let pop_env_gc_fun_const_ok = cake_theorem "pop_env_gc_fun_const_ok"
  (fun () ->
    `!s s'. wordSem_pop_env s = SOME s' /\ gc_fun_const_ok
  (wordSem_state_gc_fun s) ==>
            gc_fun_const_ok (wordSem_state_gc_fun s')`)
  CHEAT_TAC;;

(* HOL4 word_simpProofScript.sml:510-514: code that the source has in
   a comment *)

let evaluate_gc_fun_const_ok = cake_theorem "evaluate_gc_fun_const_ok"
  (fun () ->
    `!p s res s'. wordSem_evaluate (p,s) = (res,s') /\ gc_fun_const_ok
  (wordSem_state_gc_fun s) ==>
                  gc_fun_const_ok (wordSem_state_gc_fun s')`)
  CHEAT_TAC;;

let get_above_handler_def = cake_define
  `get_above_handler s = (match EL (LENGTH (stack s) -
  (wordSem_state_handler s + 1)) (stack s) with StackFrame _7 _8 _9
  (SOME (h,_10,_11)) -> h)`;;

let enc_stack_dec_stack_is_gc_word_const =
  cake_theorem "enc_stack_dec_stack_is_gc_word_const"
  (fun () ->
    `!s s' s'l.
     LIST_REL (\a b. is_gc_word_const a ==> b = a)
       (wordSem_enc_stack s) s'l /\
     wordSem_dec_stack s'l s = SOME s' ==>
     LIST_REL sf_gc_consts s s'`)
  CHEAT_TAC;;

let gc_fun_sf_gc_consts = cake_theorem "gc_fun_sf_gc_consts"
  (fun () ->
    `!s s'l s' gc_fun memory' memory' mdomain store store'.
     gc_fun_const_ok gc_fun /\
     gc_fun (wordSem_enc_stack s,memory',mdomain,store) = SOME
       (s'l,memory',store') /\
     wordSem_dec_stack s'l s = SOME s' ==>
     LIST_REL sf_gc_consts s s'`)
  CHEAT_TAC;;

let gc_sf_gc_consts = cake_theorem "gc_sf_gc_consts"
  (fun () ->
    `!s s'. gc_fun_const_ok (wordSem_state_gc_fun s) /\ wordSem_gc s =
  SOME s' ==> LIST_REL sf_gc_consts (stack s) (stack s')`)
  CHEAT_TAC;;

let gc_handler = cake_theorem "gc_handler"
  (fun () ->
    `!s s'. wordSem_gc s = SOME s' ==> wordSem_state_handler s' =
  wordSem_state_handler s`)
  CHEAT_TAC;;

let sf_gc_consts_get_above_handler =
  cake_theorem "sf_gc_consts_get_above_handler"
  (fun () ->
    `!s s'. LIST_REL sf_gc_consts (stack s) (stack s') /\
  wordSem_state_handler
            s' = wordSem_state_handler s /\ wordSem_state_handler
            s < LENGTH (stack s) ==>
            get_above_handler s' = get_above_handler s`)
  CHEAT_TAC;;

let LIST_REL_call_Result = cake_theorem "LIST_REL_call_Result"
  (fun () ->
    `!s s' s'' s''' env handler.
     LIST_REL sf_gc_consts (stack (wordSem_push_env env handler s))
       (stack s'') /\
     wordSem_pop_env s'' = SOME s''' /\ wordSem_state_handler
     s'' = wordSem_state_handler (wordSem_push_env env handler s)
       ==>
     LIST_REL sf_gc_consts (stack s) (stack s''') /\
       wordSem_state_handler s''' = wordSem_state_handler s`)
  CHEAT_TAC;;

let get_above_handler_call_env_push_env_dec_clock =
  cake_theorem "get_above_handler_call_env_push_env_dec_clock"
  (fun () ->
    `!s s' s'' args lsz env x0 x1 x2 x3.
     s' = wordSem_call_env args lsz (wordSem_push_env env (SOME
       (x0,x1,x2,x3)) (wordSem_dec_clock s)) /\ wordSem_state_handler
     s'' = get_above_handler s' ==> wordSem_state_handler
     s'' = wordSem_state_handler s`)
  CHEAT_TAC;;

let call_env_push_env_dec_clock_handler_length =
  cake_theorem "call_env_push_env_dec_clock_handler_length"
  (fun () ->
    `!s s' args lsz env x0 x1 x2 x3. s' = wordSem_call_env args lsz
  (wordSem_push_env env (SOME (x0,x1,x2,x3)) (wordSem_dec_clock s)) ==>
  wordSem_state_handler
     s' < LENGTH (stack s')`)
  CHEAT_TAC;;

let EVERY2_trans_LASTN_sf_gc_consts =
  cake_theorem "EVERY2_trans_LASTN_sf_gc_consts"
  (fun () ->
    `!l l' l'' n R. n <= LENGTH l /\ LIST_REL sf_gc_consts l l' /\
  LIST_REL sf_gc_consts (LASTN n l') l'' ==>
               LIST_REL sf_gc_consts (LASTN n l) l''`)
  CHEAT_TAC;;

let LIST_REL_push_env = cake_theorem "LIST_REL_push_env"
  (fun () ->
    `!R s s' env h. LIST_REL R (stack (wordSem_push_env env h s))
  (stack s') ==> LIST_REL R (stack s) (TL (stack s'))`)
  CHEAT_TAC;;

(*TODO move*)
let LASTN_LENGTH_CONS = cake_theorem "LASTN_LENGTH_CONS"
  (fun () ->
    `!l h. LASTN (LENGTH l) (h :: l) = l`)
  CHEAT_TAC;;

let LASTN_TL_res = cake_theorem "LASTN_TL_res"
  (fun () ->
    `!l n h t. n < LENGTH l /\ LASTN (n + 1) l = (h :: t) ==> t =
  LASTN n l`)
  CHEAT_TAC;;

let HD_LASTN = cake_theorem "HD_LASTN"
  (fun () ->
    `!l n. 0 < n /\ n <= LENGTH l ==> HD (LASTN n l) = EL (LENGTH l -
  n) l`)
  CHEAT_TAC;;

let push_env_pop_env_locals_thm =
  cake_theorem "push_env_pop_env_locals_thm"
  (fun () ->
    `!(s:('a,'c,'ffi)wordSem_state) s' (s'':('a,'c,'ffi)wordSem_state)
  s''' env names (handler:(num#'a wordLang_prog#num#num) option).
     cut_envs names (wordSem_state_locals s) = SOME env /\
     wordSem_push_env env handler s = s' /\
     LIST_REL sf_gc_consts (stack s') (stack s'') /\
     wordSem_pop_env s'' = SOME s''' ==>
     (!v w. wordSem_get_var v s = SOME w /\ is_gc_word_const w /\
       ~(sptree_lookup v (all_names names) = NONE) ==> wordSem_get_var
       v s''' = SOME w)`)
  CHEAT_TAC;;

let evaluate_sf_gc_consts = cake_theorem "evaluate_sf_gc_consts"
  (fun () ->
    `!p s s' res.
     wordSem_evaluate (p,s) = (res,s') /\ gc_fun_const_ok
       (wordSem_state_gc_fun s) ==>
     (match res with NONE ->
         LIST_REL sf_gc_consts (stack s) (stack s') /\
           wordSem_state_handler
         s' = wordSem_state_handler s | SOME (wordSem_Result _12
           _13) ->
         LIST_REL sf_gc_consts (stack s) (stack s') /\
           wordSem_state_handler
         s' = wordSem_state_handler s | SOME (wordSem_Exception _14
           _15) -> wordSem_state_handler
         s < LENGTH (stack s) ==>
         LIST_REL sf_gc_consts (LASTN (wordSem_state_handler s)
           (stack s)) (stack s') /\ wordSem_state_handler
         s' = get_above_handler s | SOME (Break _16) ->
         LIST_REL sf_gc_consts (stack s) (stack s') /\
           wordSem_state_handler
         s' = wordSem_state_handler s | SOME (Continue _17) ->
         LIST_REL sf_gc_consts (stack s) (stack s') /\
           wordSem_state_handler
         s' = wordSem_state_handler s | _18 -> T)`)
  CHEAT_TAC;;

(* HOL4 word_simpProofScript.sml:761-851: a proof *)

(* HOL4 word_simpProofScript.sml:853-891: a proof *)

(* HOL4 word_simpProofScript.sml:893: a proof *)

let evaluate_drop_consts_1 = cake_theorem "evaluate_drop_consts_1"
  (fun () ->
    `!vs rest s.
     (!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v s =
       SOME (wordLang_Word w)) ==>
     wordSem_evaluate (drop_consts cs vs,s) = (NONE,s)`)
  CHEAT_TAC;;

let evaluate_drop_consts = cake_theorem "evaluate_drop_consts[simp]"
  (fun () ->
    `(!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v s = SOME
  (wordLang_Word w)) ==>
     wordSem_evaluate (SmartSeq (drop_consts cs vs) p,s) =
       wordSem_evaluate (p,s)`)
  CHEAT_TAC;;

let lookup_FOLDR_delete = cake_theorem "lookup_FOLDR_delete[local]"
  (fun () ->
    `!l m v w.
       sptree_lookup v (ITLIST sptree_delete l m) = SOME w ==>
       sptree_lookup v m = SOME w /\ ~(MEM v l)`)
  CHEAT_TAC;;

let get_var_set_vars_ignore = cake_theorem "get_var_set_vars_ignore"
  (fun () ->
    `!xs l m. ~(MEM v xs) ==> wordSem_get_var v (wordSem_set_vars xs l
  m) = wordSem_get_var v m`)
  CHEAT_TAC;;

let evaluate_const_fp_loop = cake_theorem "evaluate_const_fp_loop"
  (fun () ->
    `!p cs p' cs' s res s'.
     wordSem_evaluate (p,s) = (res,s') /\
     const_fp_loop p cs = (p',cs') /\
     gc_fun_const_ok (wordSem_state_gc_fun s) /\
     (!v w. sptree_lookup v cs = SOME w ==> wordSem_get_var v s =
       SOME (wordLang_Word w)) ==>
     wordSem_evaluate (p',s) = (res,s') /\
     (res = NONE ==> (!v w. sptree_lookup v cs' = SOME w ==>
       wordSem_get_var v s' = SOME (wordLang_Word w)))`)
  CHEAT_TAC;;

(* HOL4 word_simpProofScript.sml:1149-1156: a proof *)

(* HOL4 word_simpProofScript.sml:1158: a proof *)

let evaluate_const_fp = cake_theorem "evaluate_const_fp"
  (fun () ->
    `!p s. gc_fun_const_ok (wordSem_state_gc_fun s) ==>
  wordSem_evaluate (const_fp p,s) = wordSem_evaluate (p,s)`)
  CHEAT_TAC;;

(* the duplicate-if pass *)

let evaluate_try_if_hoist2 =
  cake_theorem "evaluate_try_if_hoist2[local]"
  (fun () ->
    `!N p1 interm dummy' p2 s.
     try_if_hoist2 N p1 interm dummy' p2 = SOME p3 ==>
     gc_fun_const_ok (wordSem_state_gc_fun s) ==>
     wordSem_evaluate (p3,s) = wordSem_evaluate (Seq (Seq p1
       interm) p2,s)`)
  CHEAT_TAC;;

let evaluate_try_if_hoist1 =
  cake_theorem "evaluate_try_if_hoist1[local]"
  (fun () ->
    `try_if_hoist1 p1 p2 = SOME p3 ==>
     gc_fun_const_ok (wordSem_state_gc_fun s) ==>
     wordSem_evaluate (p3,s) = wordSem_evaluate (Seq p1 p2,s)`)
  CHEAT_TAC;;

let evaluate_simp_duplicate_if =
  cake_theorem "evaluate_simp_duplicate_if"
  (fun () ->
    `!p s. gc_fun_const_ok (wordSem_state_gc_fun s) ==>
     wordSem_evaluate (simp_duplicate_if p,s) = wordSem_evaluate
       (p,s)`)
  CHEAT_TAC;;

let push_out_if_aux_T = cake_theorem "push_out_if_aux_T[local]"
  (fun () ->
    `!c2 c2' res s s'.
     push_out_if_aux c2 = (c2',T) ==>
     wordSem_evaluate (c2,s) = (res,s') ==> ~(res = NONE)`)
  CHEAT_TAC;;

(* HOL4 word_simpProofScript.sml:1282-1285: ML code, not ported *)

let evaluate_simp_push_out_if = cake_theorem "evaluate_simp_push_out_if"
  (fun () ->
    `!p s.
     wordSem_evaluate (push_out_if p,s) = wordSem_evaluate (p,s)`)
  CHEAT_TAC;;

(* putting it all together *)

let compile_exp_thm = cake_theorem "compile_exp_thm"
  (fun () ->
    `wordSem_evaluate (prog,(s:('a,'c,'ffi)wordSem_state)) = (res,s2) /\
  ~(res = SOME wordSem_Error) /\
     gc_fun_const_ok (wordSem_state_gc_fun s) ==>
     wordSem_evaluate (word_simp_compile_exp prog,s) = (res,s2)`)
  CHEAT_TAC;;

cake_hide [];;
