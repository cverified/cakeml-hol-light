(* ======================================================== *)
(*  word_elimProof: ported from HOL4's
    compiler/backend/proofs/word_elimProofScript.sml
    A proof theory about word_elim.ml, with 12 definitions and 54
    theorems.  Needed by word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_elim
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_elim.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/spt_closure.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

cake_hide ["addr"];;

cake_hide_consts
  ["memory","memory"];;


cake_hide_more ["mem"];;

(**************************** ANALYSIS LEMMAS *****************************)

let lookup_analyse_word_code = cake_theorem "lookup_analyse_word_code"
  (fun () ->
    `!code n arity prog.
     ALOOKUP code n = SOME (arity,prog) ==> sptree_lookup n
       (analyse_word_code code) = SOME (find_word_ref prog)`)
  CHEAT_TAC;;

let remove_word_code_thm = cake_theorem "remove_word_code_thm"
  (fun () ->
    `!n (reachable:1 spt) l.
     ALL_DISTINCT (MAP FST l) ==> (!v. (n IN domain reachable /\
       MEM (n,v) l <=>
        MEM (n,v) (remove_word_code reachable l)))`)
  CHEAT_TAC;;


(**************************** DEFINITIONS *****************************)

let dest_word_loc_def = cake_define
  `dest_word_loc x1 =
        match x1 with
          wordLang_Loc n _2 -> SOME n
        | (_3:'a word_loc) -> NONE`;;

let dest_result_loc_def = cake_define
  `dest_result_loc x1 =
        match x1 with
          SOME (wordSem_Result w ns) ->
       BIGUNION (set_of_list (MAP (\x. match (dest_word_loc x) with
         NONE -> {} | SOME x -> {x}) ns))
        | (SOME (wordSem_Exception w (wordLang_Loc n n0))) -> {n}
        | _4 -> {}`;;

(* TODO could do alt def using toAList -
    not necessary though, may not be cleaner *)
let get_locals_def = cake_define_list
  [`get_locals (LN:('a word_loc) spt) = LN`;
   `get_locals (LS a) = (match (dest_word_loc a) with SOME n ->
  sptree_insert n one LN | NONE -> LN)`;
   `get_locals (BN t1 t2) = sptree_union (get_locals t1) (get_locals
  t2)`;
   `get_locals (BS t1 a t2) =
            (let t = (sptree_union (get_locals t1) (get_locals t2))
              in
                match (dest_word_loc a) with SOME n ->
                  sptree_insert n one t | NONE -> t)`];;

let domain_get_locals_lookup = cake_theorem "domain_get_locals_lookup"
  (fun () ->
    `!n t. n IN domain (get_locals t) <=> (?k n1. sptree_lookup k t =
  SOME (Loc n n1))`)
  CHEAT_TAC;;

let get_locals_insert_Loc = cake_theorem "get_locals_insert_Loc"
  (fun () ->
    `!k n1 n0 (locals:('a word_loc) spt).
        domain (get_locals (sptree_insert k (Loc n1 n0) locals))
          SUBSET
            domain (get_locals locals) UNION {n1}`)
  CHEAT_TAC;;

let get_locals_insert = cake_theorem "get_locals_insert"
  (fun () ->
    `!k v (locals:('a word_loc) spt).
        domain (get_locals (sptree_insert k v locals)) SUBSET
        domain (get_locals locals) UNION (match dest_word_loc v
          with NONE -> {} | SOME n -> {n})`)
  CHEAT_TAC;;

(*TODO fix conflict with get_store in WordSem*)
let get_store_def = cake_define
  `word_elimProof_get_store (st:(store_name,'a word_loc)fmap) =
       (let locSet = SET_TO_LIST (FRANGE st) in
       let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc
         locSet)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locList)`;;
hol4_overload "get_store" "word_elimProof_get_store";;

let domain_get_store = cake_theorem "domain_get_store"
  (fun () ->
    `!n store. n IN domain (get_store store) <=>
        (?k n1. FLOOKUP store k = SOME (Loc n n1))`)
  CHEAT_TAC;;

let get_store_update = cake_theorem "get_store_update"
  (fun () ->
    `!store k v.
        domain (get_store (store |+ (k,v))) SUBSET
            domain (get_store store) UNION (match dest_word_loc v
              with NONE -> {} | SOME n -> {n})`)
  CHEAT_TAC;;

let get_num_wordloc_alist_def = cake_define
  `get_num_wordloc_alist (l:(num#'a word_loc) list) =
       (let locs = MAP THE (FILTER IS_SOME (MAP (dest_word_loc o SND)
         l)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locs)`;;

let get_num_wordloc_alist_thm = cake_theorem "get_num_wordloc_alist_thm"
  (fun () ->
    `!n e l. (?n0. MEM (Loc n n0) (MAP SND l)) <=>
        n IN domain (get_num_wordloc_alist l)`)
  CHEAT_TAC;;

let get_num_wordloc_alist_get_locals =
  cake_theorem "get_num_wordloc_alist_get_locals"
  (fun () ->
    `!e.
        domain (get_locals (fromAList e)) SUBSET domain
          (get_num_wordloc_alist e)`)
  CHEAT_TAC;;

let get_locals_union_subset = cake_theorem "get_locals_union_subset"
  (fun () ->
    `!A B.
     domain (get_locals (sptree_union A B)) SUBSET (domain
       (sptree_union (get_locals A) (get_locals B)))`)
  CHEAT_TAC;;

let get_stack_def = cake_define_list
  [`word_elimProof_get_stack [] = (LN:1 spt)`;
   `word_elimProof_get_stack (StackFrame lsz e0 e _5 :: xs) =
            ((sptree_union (sptree_union (get_num_wordloc_alist
              e0) (get_num_wordloc_alist e))
              (word_elimProof_get_stack xs)):1 spt)`];;
hol4_overload "get_stack" "word_elimProof_get_stack";;

(* HOL4 word_elimProofScript.sml:210: ML code, not ported *)

let get_stack_hd_thm = cake_theorem "get_stack_hd_thm"
  (fun () ->
    `!stack' dr l0 l opt t.
        domain (get_stack stack') SUBSET dr /\
        stack' = StackFrame lsz l l0 opt :: t ==> domain
          (get_locals (sptree_union (fromAList l0) (fromAList l)))
          SUBSET dr /\
          domain (get_stack t) SUBSET dr`)
  CHEAT_TAC;;

let get_stack_LASTN = cake_theorem "get_stack_LASTN"
  (fun () ->
    `!stack' n. domain (get_stack (LASTN n stack')) SUBSET domain
  (get_stack stack')`)
  CHEAT_TAC;;

let get_stack_CONS = cake_theorem "get_stack_CONS"
  (fun () ->
    `!h t. domain (get_stack [h]) SUBSET domain (get_stack (h :: t)) /\
        domain (get_stack t) SUBSET domain (get_stack (h :: t))`)
  CHEAT_TAC;;

let get_stack_enc_stack = cake_theorem "get_stack_enc_stack"
  (fun () ->
    `!stack' reachable.
     domain (get_stack stack') SUBSET domain reachable ==> (!e.
     MEM e (wordSem_enc_stack stack') ==> (match dest_word_loc e
       with NONE -> {} | SOME n -> {n}) SUBSET
        domain reachable)`)
  CHEAT_TAC;;

let get_stack_dec_stack = cake_theorem "get_stack_dec_stack"
  (fun () ->
    `!locs stack' reachable new_stack.
     (!n n0. MEM (Loc n n0) locs ==> n IN domain reachable) /\
     domain (get_stack stack') SUBSET domain reachable /\
     wordSem_dec_stack locs stack' = SOME new_stack ==> domain
       (get_stack new_stack) SUBSET domain reachable`)
  CHEAT_TAC;;

let get_memory_def = cake_define
  `get_memory (mem':'a word->'a word_loc) (mdom:'a word->bool) =
       (let locSet = SET_TO_LIST (IMAGE mem' mdom) in
       let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc
         locSet)) in
       FOLDL (\acc loc. sptree_insert loc one acc) LN locList)`;;

let FINITE_mdom_mem = cake_theorem "FINITE_mdom_mem"
  (fun () ->
    `!mdom. FINITE mdom ==> FINITE {mem x | x IN mdom}`)
  CHEAT_TAC;;

let domain_get_memory = cake_theorem "domain_get_memory"
  (fun () ->
    `!mem' (mdom:'a word->bool) n.
       n IN domain (get_memory mem' mdom) <=>
         (?k n1. k IN mdom /\ mem' k = Loc n n1)`)
  CHEAT_TAC;;

let get_memory_update = cake_theorem "get_memory_update"
  (fun () ->
    `!k v (memory':'a word->'a word_loc) (mdomain:'a word->bool).
        (domain (get_memory ((k =+ v) memory') mdomain)) SUBSET
            (domain (get_memory memory' mdomain)) UNION (match
              (dest_word_loc v) with NONE -> {} | SOME n -> {n})`)
  CHEAT_TAC;;

let find_loc_state_def = cake_define
  `find_loc_state s =
       (let loc = (get_locals (wordSem_state_locals s)) in
       let sto = (get_store (wordSem_state_store s)) in
       let sta = (get_stack (stack s)) in
       let mem' = (get_memory (wordSem_state_memory s)
         (wordSem_state_mdomain s)) in
       sptree_union (sptree_union loc sto) (sptree_union sta
         mem'))`;;

let domain_find_loc_state = cake_theorem "domain_find_loc_state"
  (fun () ->
    `!s. domain (find_loc_state s) =
        domain (get_locals (wordSem_state_locals s)) UNION domain
          (get_store (wordSem_state_store s)) UNION
        domain (get_stack (stack s)) UNION domain (get_memory
          (wordSem_state_memory s) (wordSem_state_mdomain s))`)
  CHEAT_TAC;;

let code_rel_def = cake_define
  `word_elimProof_code_rel (reachable:1 spt) s_code (t_code:(num#'a
  wordLang_prog) spt) =
       (!n. n IN domain reachable ==>
           sptree_lookup n s_code = sptree_lookup n t_code)`;;
hol4_overload "code_rel" "word_elimProof_code_rel";;

let code_closed_def = cake_define
  `code_closed reachable c1 <=> (?code1. c1 = fromAList code1 /\
       (!n m. n IN domain reachable /\
       is_reachable (analyse_word_code code1) n m ==>
       m IN domain reachable))`;;

let gc_no_new_locs_def = cake_define
  `gc_no_new_locs (g:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) <=> (!sta
  mem' mdom sto wl mem1 sto1 sta1.
       (g (wordSem_enc_stack sta,mem',mdom,sto) = SOME
         (wl,mem1,sto1)) /\
        wordSem_dec_stack wl sta = SOME sta1 ==>
       domain (get_stack sta1) SUBSET domain (get_stack sta) /\
       domain (get_memory mem1 mdom) SUBSET domain (get_memory mem'
         mdom) /\
       domain (get_store sto1) SUBSET domain (get_store sto))`;;

let word_state_rel_def = cake_define
  `word_state_rel (reachable:1 spt) t s <=> wordSem_state_locals
       s = wordSem_state_locals t /\ wordSem_state_fp_regs
       s = wordSem_state_fp_regs t /\ wordSem_state_store
       s = wordSem_state_store t /\ stack
       s = stack t /\ wordSem_state_memory
       s = wordSem_state_memory t /\ wordSem_state_mdomain
       s = wordSem_state_mdomain t /\ wordSem_state_sh_mdomain
       s = wordSem_state_sh_mdomain t /\ wordSem_state_permute
       s = wordSem_state_permute t /\ wordSem_state_compile
       s = wordSem_state_compile t /\ wordSem_state_compile_oracle
       s = wordSem_state_compile_oracle t /\
         wordSem_state_code_buffer
       s = wordSem_state_code_buffer t /\ wordSem_state_data_buffer
       s = wordSem_state_data_buffer t /\ wordSem_state_gc_fun
       s = wordSem_state_gc_fun t /\ wordSem_state_handler
       s = wordSem_state_handler t /\ state_clock
       s = state_clock t /\ wordSem_state_termdep
       s = wordSem_state_termdep t /\ wordSem_state_be
       s = wordSem_state_be t /\ state_ffi
       s = state_ffi t /\ wordSem_state_locals_size
       s = wordSem_state_locals_size t /\ wordSem_state_stack_max
       s = wordSem_state_stack_max t /\ wordSem_state_stack_limit
       s = wordSem_state_stack_limit t /\ wordSem_state_stack_size
       s = wordSem_state_stack_size t /\
       word_elimProof_code_rel reachable (wordSem_state_code s)
         (wordSem_state_code t) /\
       domain (find_loc_state t) SUBSET domain (reachable)`;;


(**************************** OTHER LEMMAS *****************************)

let ALOOKUP_ZIP_SUCCESS = cake_theorem "ALOOKUP_ZIP_SUCCESS"
  (fun () ->
    `!x y k v.
     LENGTH x = LENGTH y ==> ALOOKUP (ZIP x y) k = SOME v ==> MEM
       v y`)
  CHEAT_TAC;;

let get_vars_locals = cake_theorem "get_vars_locals"
  (fun () ->
    `!args s x y.
     wordSem_get_vars args s = SOME x /\ MEM y x ==> (?n.
       sptree_lookup n (wordSem_state_locals s) = SOME y)`)
  CHEAT_TAC;;

let get_vars_get_locals = cake_theorem "get_vars_get_locals"
  (fun () ->
    `!args s x n n1.
     wordSem_get_vars args s = SOME x /\ MEM (Loc n n1) x ==> n
       IN domain (get_locals (wordSem_state_locals s))`)
  CHEAT_TAC;;

let get_locals_fromList2 = cake_theorem "get_locals_fromList2"
  (fun () ->
    `!args s x t.
     wordSem_get_vars args s = SOME x /\ ~(x = []) /\ t =
       fromList2 x ==> domain (get_locals t) SUBSET domain (get_locals
       (wordSem_state_locals s))`)
  CHEAT_TAC;;

let get_locals_fromList2_extension =
  cake_theorem "get_locals_fromList2_extension"
  (fun () ->
    `!x y ys.
     x IN domain (get_locals (fromList2 ys)) ==> x IN domain
       (get_locals (fromList2 (ys ++ [y])))`)
  CHEAT_TAC;;

let get_locals_fromList2_FRONT =
  cake_theorem "get_locals_fromList2_FRONT"
  (fun () ->
    `!args s x xf t.
     wordSem_get_vars args s = SOME x /\ ~(x = []) /\ xf = FRONT
       x /\ t = fromList2 xf ==> domain (get_locals t) SUBSET domain
       (get_locals (wordSem_state_locals s))`)
  CHEAT_TAC;;

let get_memory_write_bytearray_lemma =
  cake_theorem "get_memory_write_bytearray_lemma"
  (fun () ->
    `!mem' mdom reachable c r be'.
        domain (get_memory mem' mdom) SUBSET domain reachable ==>
          domain (get_memory (write_bytearray c r mem' mdom be') mdom)
          SUBSET
        domain reachable`)
  CHEAT_TAC;;

let stack_list_rearrange_lemma =
  cake_theorem "stack_list_rearrange_lemma"
  (fun () ->
    `!s dr locs opt lsz.
        domain (get_locals (wordSem_state_locals s)) SUBSET dr /\
        domain (get_stack (stack s)) SUBSET dr ==>
        domain (get_stack (StackFrame lsz (toAList (inter
          (wordSem_state_locals s) n)) (list_rearrange
          (wordSem_state_permute s 0)
     (sort key_val_compare (toAList (inter (wordSem_state_locals
       s) locs)))) opt :: stack s)) SUBSET dr`)
  CHEAT_TAC;;

let remove_word_code_thm_FST = cake_theorem "remove_word_code_thm_FST"
  (fun () ->
    `!n (reachable:1 spt) l.
     ALL_DISTINCT (MAP FST l) ==> (n IN domain reachable /\ MEM n
       (MAP FST l) <=>
     MEM n (MAP FST (remove_word_code reachable l)))`)
  CHEAT_TAC;;

let remove_word_code_MAP_FST_lemma =
  cake_theorem "remove_word_code_MAP_FST_lemma"
  (fun () ->
    `!(reachable:1 spt).
        MAP FST (FILTER (\x. IS_SOME (sptree_lookup (FST x)
          reachable)) l) =
            FILTER (\x. IS_SOME (sptree_lookup x reachable)) (MAP
              FST l)`)
  CHEAT_TAC;;

(**************************** WORD STATE REL ***************************)

let word_state_rel_get_var = cake_theorem "word_state_rel_get_var"
  (fun () ->
    `word_state_rel reachable s t ==> wordSem_get_var v t =
  wordSem_get_var v s`)
  CHEAT_TAC;;

let word_state_rel_get_store = cake_theorem "word_state_rel_get_store"
  (fun () ->
    `word_state_rel reachable s t ==> wordSem_get_store v t =
  wordSem_get_store v s`)
  CHEAT_TAC;;

let word_state_rel_get_vars = cake_theorem "word_state_rel_get_vars"
  (fun () ->
    `word_state_rel reachable s t ==> wordSem_get_vars vs t =
  wordSem_get_vars vs s`)
  CHEAT_TAC;;

let word_state_rel_set_var = cake_theorem "word_state_rel_set_var"
  (fun () ->
    `word_state_rel reachable s t /\
     (match dest_word_loc v with NONE -> {} | SOME n -> {n}) SUBSET
          domain reachable ==>
     word_state_rel reachable (wordSem_set_var n v s)
            (wordSem_set_var n v t)`)
  CHEAT_TAC;;

(*TODO maybe depreciate?*)
let word_state_rel_set_var_word =
  cake_theorem "word_state_rel_set_var_word"
  (fun () ->
    `word_state_rel reachable s t ==>
     word_state_rel reachable (wordSem_set_var n (wordLang_Word w)
       s)
            (wordSem_set_var n (wordLang_Word w) t)`)
  CHEAT_TAC;;

(*TODO add assum to prove it*)
let word_state_rel_set_vars = cake_theorem "word_state_rel_set_vars"
  (fun () ->
    `word_state_rel reachable s t /\
     BIGUNION
             (set_of_list
                (MAP (\x'. match dest_word_loc x' with NONE -> {} |
                  SOME x -> {x})
                   l)) SUBSET domain reachable /\
     LENGTH l0 = LENGTH l ==>
     word_state_rel reachable (wordSem_set_vars l0 l s)
            (wordSem_set_vars l0 l t)`)
  CHEAT_TAC;;

(*This can be strengthened to an equality*)
let word_state_rel_set_fp_var = cake_theorem "word_state_rel_set_fp_var"
  (fun () ->
    `word_state_rel reachable s t ==>
     word_state_rel reachable (wordSem_set_fp_var n v s)
            (wordSem_set_fp_var n v t)`)
  CHEAT_TAC;;

let word_state_rel_word_exp = cake_theorem "word_state_rel_word_exp"
  (fun () ->
    `!s1 exp s2 reachable.
        word_state_rel reachable s1 s2 ==> wordSem_word_exp s2
          exp = wordSem_word_exp s1 exp`)
  CHEAT_TAC;;

let word_state_rel_mem_load = cake_theorem "word_state_rel_mem_load"
  (fun () ->
    `word_state_rel reachable s t ==> wordSem_mem_load addr t =
  wordSem_mem_load addr s`)
  CHEAT_TAC;;

let word_state_rel_mem_load_32 =
  cake_theorem "word_state_rel_mem_load_32"
  (fun () ->
    `word_state_rel reachable s t ==>
     mem_load_32 (wordSem_state_memory s) (wordSem_state_mdomain s)
       (wordSem_state_be s) c =
     mem_load_32 (wordSem_state_memory t) (wordSem_state_mdomain
       t) (wordSem_state_be t) c`)
  CHEAT_TAC;;

let word_state_rel_get_fp_var = cake_theorem "word_state_rel_get_fp_var"
  (fun () ->
    `word_state_rel reachable s t ==> wordSem_get_fp_var v s =
  wordSem_get_fp_var v t`)
  CHEAT_TAC;;

let word_state_rel_assign_NONE =
  cake_theorem "word_state_rel_assign_NONE"
  (fun () ->
    `!reg exp s reachable t.
     word_state_rel reachable s t ==> (wordSem_assign reg exp s =
       NONE <=> wordSem_assign reg exp t = NONE)`)
  CHEAT_TAC;;

let word_state_rel_inst_NONE = cake_theorem "word_state_rel_inst_NONE"
  (fun () ->
    `!reachable s t i.
     word_state_rel reachable s t ==> (wordSem_inst i s = NONE
       <=> wordSem_inst i t = NONE)`)
  CHEAT_TAC;;

let word_state_rel_assign_SOME =
  cake_theorem "word_state_rel_assign_SOME"
  (fun () ->
    `word_state_rel reachable s t ==>
     (
       wordSem_assign reg exp s = (SOME s1) /\ wordSem_assign reg
         exp t = SOME t1 ==> word_state_rel reachable s1 t1)`)
  CHEAT_TAC;;

let word_state_rel_inst_SOME = cake_theorem "word_state_rel_inst_SOME"
  (fun () ->
    `!reachable s t i s1 t1. word_state_rel reachable s t ==>
     (wordSem_inst i s = SOME s1 /\ wordSem_inst i t = SOME t1
       ==> word_state_rel reachable s1 t1)`)
  CHEAT_TAC;;

let word_state_rel_pop_env_NONE =
  cake_theorem "word_state_rel_pop_env_NONE"
  (fun () ->
    `!reachable s t.
     word_state_rel reachable s t ==> (wordSem_pop_env s = NONE
       <=> wordSem_pop_env t = NONE)`)
  CHEAT_TAC;;

let word_state_rel_pop_env = cake_theorem "word_state_rel_pop_env"
  (fun () ->
    `!reachable s t s1 l1 l2.
     word_state_rel reachable s t ==>
     wordSem_pop_env s = SOME (s1) ==> (?t1. wordSem_pop_env t =
       SOME (t1) /\ word_state_rel reachable s1 t1)`)
  CHEAT_TAC;;

let word_state_rel_jump_exc = cake_theorem "word_state_rel_jump_exc"
  (fun () ->
    `!reachable s t s1 l1 l2.
     word_state_rel reachable s t ==>
     wordSem_jump_exc s = SOME (s1,l1,l2) ==> (?t1.
       wordSem_jump_exc t = SOME (t1,l1,l2) /\ word_state_rel
       reachable s1 t1)`)
  CHEAT_TAC;;

let word_state_rel_gc = cake_theorem "word_state_rel_gc"
  (fun () ->
    `!reachable s t s1.
     word_state_rel reachable s t /\ gc_no_new_locs
       (wordSem_state_gc_fun s) ==>
     wordSem_gc s = SOME s1 ==> (?t1. wordSem_gc t = SOME t1 /\
       word_state_rel reachable s1 t1)`)
  CHEAT_TAC;;

let word_state_rel_alloc = cake_theorem "word_state_rel_alloc"
  (fun () ->
    `!reachable s t res c n s1.
     word_state_rel reachable s t /\ ~(res = SOME wordSem_Error) /\
       gc_no_new_locs (wordSem_state_gc_fun s) ==> wordSem_alloc c n s =
       (res,s1) ==>
        (?t1. wordSem_alloc c n t = (res,t1) /\ word_state_rel
          reachable s1 t1 /\
      dest_result_loc res SUBSET domain reachable)`)
  CHEAT_TAC;;

let const_writes_eq_Loc = cake_theorem "const_writes_eq_Loc"
  (fun () ->
    `!words a c m k l1 l2.
       const_writes a c words m k = Loc l1 l2 ==> m k = Loc l1 l2`)
  CHEAT_TAC;;
(*TODO move*)
let push_env_def2 = cake_theorem "push_env_def2"
  (fun () ->
    `wordSem_push_env env handler s =
         (let l0 = toAList (FST env) in
          let (l,permute) = env_to_list (SND env)
            (wordSem_state_permute s) in
          let handler = (match handler with NONE -> NONE | SOME
            (w,h,l1,l2) -> SOME (wordSem_state_handler s,l1,l2)) in
         let stack' = StackFrame (wordSem_state_locals_size s) l0 l
           handler :: stack s in wordSem_state_handler_fupd (K (match
           handler with NONE -> wordSem_state_handler s | SOME x ->
           LENGTH (stack s))) (wordSem_state_permute_fupd (K permute)
           (wordSem_state_stack_max_fupd (K (OPTION_MAP2 MAX
           (wordSem_state_stack_max s) (stack_size stack'))) (stack_fupd
           (K stack')
          s))))`)
  CHEAT_TAC;;

(**************************** MAIN LEMMAS *****************************)
let get_locals_inter_subset =
  cake_theorem "get_locals_inter_subset[local]"
  (fun () ->
    `domain (get_locals (inter a b)) SUBSET domain (get_locals a)`)
  CHEAT_TAC;;

let word_removal_lemma = cake_theorem "word_removal_lemma"
  (fun () ->
    `!program state result new_state reachable removed_state.
        wordSem_evaluate (program,state) = (result,new_state) /\
          ~(result = SOME wordSem_Error) /\ word_state_rel reachable
          state removed_state /\
        gc_no_new_locs (wordSem_state_gc_fun state) /\
        wordConvs_no_install program /\ no_install_code
          (wordSem_state_code state) /\
        no_install_code (wordSem_state_code removed_state) /\
        domain (find_word_ref program) SUBSET domain (reachable) /\
        code_closed reachable (wordSem_state_code state) ==> (?s.
            wordSem_evaluate (program,removed_state) = (result,s)
              /\
            word_state_rel reachable new_state s /\
            (dest_result_loc result) SUBSET domain (reachable))`)
  CHEAT_TAC;;

(* HOL4 word_elimProofScript.sml:989-992: a proof *)

(* HOL4 word_elimProofScript.sml:994-996: a proof *)

(* HOL4 word_elimProofScript.sml:998-1006: a proof *)

(* HOL4 word_elimProofScript.sml:1008-1014: a proof *)

(* HOL4 word_elimProofScript.sml:1016-1023: a proof *)

(* HOL4 word_elimProofScript.sml:1025-1035: a proof *)

(* HOL4 word_elimProofScript.sml:1037-1044: a proof *)

(* HOL4 word_elimProofScript.sml:1046-1052: a proof *)

(* HOL4 word_elimProofScript.sml:1054-1065: a proof *)

(* HOL4 word_elimProofScript.sml:1067-1079: a proof *)

(* HOL4 word_elimProofScript.sml:1081-1093: a proof *)

(* HOL4 word_elimProofScript.sml:1095-1108: a proof *)

(* HOL4 word_elimProofScript.sml:1110-1132: a proof *)

(* HOL4 word_elimProofScript.sml:1134-1159: a proof *)

(* HOL4 word_elimProofScript.sml:1161-1176: a proof *)

(* HOL4 word_elimProofScript.sml:1178-1186: a proof *)

(* HOL4 word_elimProofScript.sml:1188-1203: a proof *)

(* HOL4 word_elimProofScript.sml:1205-1217: a proof *)

(* HOL4 word_elimProofScript.sml:1219-1232: a proof *)

(* HOL4 word_elimProofScript.sml:1234-1254: a proof *)

(* HOL4 word_elimProofScript.sml:1256-1274: a proof *)

(* HOL4 word_elimProofScript.sml:1276-1295: a proof *)

(* HOL4 word_elimProofScript.sml:1297-1542: a proof *)

(* HOL4 word_elimProofScript.sml:1544-1599: a proof *)

(* HOL4 word_elimProofScript.sml:1601: a proof *)

(**************************** WORD_REMOVAL_THM *****************************)

let word_removal_thm = cake_theorem "word_removal_thm"
  (fun () ->
    `!start' state result new_state r reachable code1.
        wordSem_evaluate (Call NONE (SOME start') [0] NONE,state) =
            (result,new_state) /\ ~(result = SOME wordSem_Error) /\
              wordSem_state_code state = fromAList code1 /\
        domain (find_loc_state state) SUBSET domain reachable /\
        gc_no_new_locs (wordSem_state_gc_fun state) /\
        reachable = closure_spt (sptree_insert start' one LN)
          (analyse_word_code code1) /\
        ALL_DISTINCT (MAP FST code1) /\ no_install_code
          (wordSem_state_code state) ==> (?s.
            wordSem_evaluate (Call NONE (SOME start') [0]
              NONE,wordSem_state_code_fupd (K
                    (fromAList (remove_word_code reachable code1)))
                state) = (result,s))`)
  CHEAT_TAC;;

cake_hide [];;

cake_hide_consts [];;
