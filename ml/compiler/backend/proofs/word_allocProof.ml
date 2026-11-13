(* ======================================================== *)
(*  word_allocProof: ported from HOL4's
    compiler/backend/proofs/word_allocProofScript.sml
    A proof theory about word_alloc.ml, with 10 definitions and 220
    theorems.  Needed by word_to_wordProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for word_alloc
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/proofs/linear_scanProof.ml";;
needs "compiler/backend/reg_alloc/proofs/reg_allocProof.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "word_allocProof"
  ["backend_common"; "linear_scan"; "linear_scanProof"; "mllist";
   "reg_alloc"; "reg_allocProof"; "wordConvs"; "wordLang";
   "wordProps"; "wordSem"; "word_alloc"];;

let _ = do_list hide_constant ["C"; "not"; "sloc"; "val"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
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
   "data_buffer","data_buffer"];;

(* Ensures we have the correct ML bindings *)
(* HOL4 word_allocProofScript.sml:13-15: ML code, not ported *)

let _ = do_list hide_constant ["mem"];;
hol4_overload "numset_list_insert" "word_alloc_numset_list_insert";;

(*TODO: Move?*)
let SUBSET_OF_INSERT = prove
 (`!s x. s SUBSET x INSERT s`,
  CHEAT_TAC);;

(* [local] *)
let INJ_UNION = prove
 (`!f A B.
   INJ f (A UNION B) UNIV ==>
   INJ f A UNIV /\
   INJ f B UNIV`,
  CHEAT_TAC);;

(* INJ_less[local] *)
let word_allocProof_INJ_less = prove
 (`INJ f s' UNIV /\ s SUBSET s' ==>
   INJ f s UNIV`,
  CHEAT_TAC);;

(* [local] *)
let LET_FORALL_ELIM' = prove
 (`LET f v <=> (!) (hol4_S ((==>) o (=) v) f)`,
  CHEAT_TAC);;
(* TODO: can we have a global for this *)
let word_allocProof_hide_def = cake_define
  `word_allocProof_hide x = x`;;
hol4_overload "hide" "word_allocProof_hide";;

(* [local] *)
let INJ_IMP_IMAGE_DIFF = prove
 (`INJ f (s UNION t) UNIV ==>
   IMAGE f (s DIFF t) = (IMAGE f s) DIFF (IMAGE f t)`,
  CHEAT_TAC);;

(* [local] *)
let INJ_IMP_IMAGE_DIFF_single = prove
 (`INJ f (s UNION {n}) UNIV ==>
   (IMAGE f s) DIFF {f n} = IMAGE f (s DIFF {n})`,
  CHEAT_TAC);;

(* [local] *)
let INJ_ALL_DISTINCT_MAP = prove
 (`!ls.
   ALL_DISTINCT (MAP f ls) ==>
   INJ f (set_of_list ls) UNIV`,
  CHEAT_TAC);;

(* word_alloc proofs
  1. correctness theorem about colouring_ok
  2. get_clash_sets (TODO: redundant)
  3. connect check_clash_tree to colouring_ok
  4. word_alloc_correct (connect 1 and 3)
  5. ssa_cc_trans correctness proof (including an invariant property), followed by full_ssa_cc_trans correctness
  6. ssa syntactic things (pre_alloc_conventions, wf_cutsets)
  7. word_alloc syntactic things
  8. misc
 *)

(* colouring_ok correctness proof *)
let colouring_ok_def = cake_define
  `colouring_ok f prog live lt =
        match prog with
          wordLang_Seq s1 s2 ->
       // Normal live sets
       (let s2_live = get_live s2 live lt in
       let s1_live = get_live s1 s2_live lt in
         INJ f (domain s1_live) UNIV /\
         // Internal clash sets
         colouring_ok f s2 live lt /\ colouring_ok f s1 s2_live lt)
        | (If cmp r1 ri e2 e3) ->
       (let e2_live = get_live e2 live lt in
       let e3_live = get_live e3 live lt in
       let union_live = sptree_union e2_live e3_live in
       let merged = (match ri with Reg r2 -> sptree_insert r2 one
         (sptree_insert r1 one union_live) | _1 -> sptree_insert r1 one
         union_live) in
         // All of them must be live at once
         INJ f (domain merged) UNIV /\
         // Internal clash sets
         colouring_ok f e2 live lt /\ colouring_ok f e3 live lt)
        | (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) ->
       (let args_set = numset_list_insert args LN in
       let all_names' = sptree_union (SND cutset) (FST cutset) in
       INJ f (domain (sptree_union all_names' args_set)) UNIV /\
       INJ f (domain (numset_list_insert v all_names')) UNIV /\
       // returning handler
       colouring_ok f ret_handler live lt /\
       (
        // exception handler
        match h with NONE -> T | SOME (v,prog,l1,l2) ->
           INJ f (domain (sptree_insert v one all_names')) UNIV /\
           colouring_ok f prog live lt))
        | (wordLang_MustTerminate p) ->
       colouring_ok f p live lt
        | (Loop names body exit_names) ->
       (INJ f (domain names) UNIV /\
       INJ f (domain exit_names) UNIV /\
       colouring_ok f body names ((names,exit_names) :: lt))
        | prog ->
       // live before must be fine, and clash set must be fine
       (let lset = get_live prog live lt in
       let iset = sptree_union (get_writes prog) live in
         INJ f (domain lset) UNIV /\ INJ f (domain iset) UNIV)`;;

(*Equivalence on everything except permutation and locals*)
(* should we add local_size here? may be no, as locals are not included *)
(*TODO this definition is bad for automation remove it with
t = s with (...)*)
let word_state_eq_rel_def = cake_define
  `word_state_eq_rel (s:('a,'c,'ffi)wordSem_state)
  (t:('a,'c,'ffi)wordSem_state) <=> wordSem_state_fp_regs
   t = wordSem_state_fp_regs s /\ wordSem_state_store
   t = wordSem_state_store s /\ wordSem_state_locals_size
   t = wordSem_state_locals_size s /\ wordSem_state_stack
   t = wordSem_state_stack s /\ wordSem_state_stack_limit
   t = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   t = wordSem_state_stack_max s /\ wordSem_state_stack_size
   t = wordSem_state_stack_size s /\ wordSem_state_memory
   t = wordSem_state_memory s /\ wordSem_state_mdomain
   t = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   t = wordSem_state_sh_mdomain s /\ wordSem_state_gc_fun
   t = wordSem_state_gc_fun s /\ wordSem_state_handler
   t = wordSem_state_handler s /\ wordSem_state_clock
   t = wordSem_state_clock s /\ wordSem_state_code
   t = wordSem_state_code s /\ wordSem_state_ffi
   t = wordSem_state_ffi s /\ wordSem_state_be
   t = wordSem_state_be s /\ wordSem_state_termdep
   t = wordSem_state_termdep s /\ wordSem_state_compile
   t = wordSem_state_compile s /\ wordSem_state_compile_oracle
   t = wordSem_state_compile_oracle s /\ wordSem_state_code_buffer
   t = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   t = wordSem_state_data_buffer s`;;


(*tlocs is a supermap of slocs under f for everything in a given
  live set*)

let strong_locals_rel_def = cake_define
  `strong_locals_rel f ls slocs tlocs <=>
   (!n v.
     n IN ls /\ sptree_lookup n slocs = SOME v ==>
     sptree_lookup (f n) tlocs = SOME v)`;;

(* [local] *)
let strong_locals_rel_subset_domain = prove
 (`strong_locals_rel f s l1 l2 /\ s SUBSET domain l1 ==>
   (!v. v IN s ==> f v IN domain l2)`,
  CHEAT_TAC);;

(* domain_numset_list_insert *)
let word_allocProof_domain_numset_list_insert = prove
 (`!ls locs.
   domain (numset_list_insert ls locs) = domain locs UNION
     set_of_list ls`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_get_var = prove
 (`strong_locals_rel f live (wordSem_state_locals st)
  (wordSem_state_locals cst) /\
   n IN live /\
   wordSem_get_var n st = SOME x ==>
   wordSem_get_var (f n) cst = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_get_var_imm = prove
 (`strong_locals_rel f live (wordSem_state_locals st)
  (wordSem_state_locals cst) /\
   (match n with Reg n -> n IN live | _2 -> T) /\
   wordSem_get_var_imm n st = SOME x ==>
   wordSem_get_var_imm (apply_colour_imm f n) cst = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_get_vars = prove
 (`!ls y f live st cst.
   strong_locals_rel f live (wordSem_state_locals st)
     (wordSem_state_locals cst) /\
   (!x. MEM x ls ==> x IN live) /\
   wordSem_get_vars ls st = SOME y ==>
   wordSem_get_vars (MAP f ls) cst = SOME y`,
  CHEAT_TAC);;

let strong_locals_rel_UNION = prove
 (`strong_locals_rel f (A UNION B) t l <=> strong_locals_rel f A t l
  /\ strong_locals_rel f B t l`,
  CHEAT_TAC);;

(* [local] *)
let domain_big_union_subset = prove
 (`!ls a.
   MEM a ls ==>
   domain (get_live_exp a) SUBSET
   domain (big_union (MAP get_live_exp ls))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:265: ML code, not ported *)

(* [local] *)
let apply_nummap_key_domain = prove
 (`!f names.
   domain (apply_nummap_key f names) =
   IMAGE f (domain names)`,
  CHEAT_TAC);;

let cut_names_lemma = prove
 (`!names sloc' tloc x f.
   INJ f (domain names) UNIV /\
   cut_names names sloc' = SOME x /\
   strong_locals_rel f (domain names) sloc' tloc ==>
   (?y. cut_names (apply_nummap_key f names) tloc = SOME y /\
       domain y = IMAGE f (domain x) /\
       strong_locals_rel f (domain names) x y /\
       INJ f (domain x) UNIV /\
       domain x = domain names)`,
  CHEAT_TAC);;

let cut_envs_lemma = prove
 (`INJ f (domain n1) UNIV /\
   INJ f (domain n2) UNIV /\
   cut_envs (n1,n2) sloc = SOME (x1,x2) /\
   strong_locals_rel f (domain n1) sloc tloc /\
   strong_locals_rel f (domain n2) sloc tloc ==>
   (?y1 y2.
     cut_envs (apply_nummaps_key f (n1,n2)) tloc = SOME (y1,y2) /\
     domain y1 = IMAGE f (domain n1) /\
     domain y2 = IMAGE f (domain n2) /\
     strong_locals_rel f (domain n1) x1 y1 /\
     strong_locals_rel f (domain n2) x2 y2 /\
     INJ f (domain x1) UNIV /\
     INJ f (domain x2) UNIV /\
     domain x1 = domain n1 /\
     domain x2 = domain n2)`,
  CHEAT_TAC);;

let cut_env_lemma = prove
 (`INJ f (domain (FST names) UNION domain (SND names)) UNIV /\
   wordSem_cut_env names sloc = SOME x /\
   strong_locals_rel f (domain (FST names) UNION domain (SND names))
     sloc tloc ==>
   (?y.
     wordSem_cut_env (apply_nummaps_key f names) tloc = SOME y /\
     domain y = IMAGE f (domain x) /\
     strong_locals_rel f (domain (FST names) UNION domain (SND
       names)) x y /\
     INJ f (domain x) UNIV /\
     domain x = domain (FST names) UNION domain (SND names))`,
  CHEAT_TAC);;

(* [local] *)
let nummaps_to_nummap = prove
 (`FST (apply_nummaps_key f a) = apply_nummap_key f (FST a) /\
   SND (apply_nummaps_key f a) = apply_nummap_key f (SND a)`,
  CHEAT_TAC);;

let INJ_union = prove
 (`INJ f (A UNION B) C ==> INJ f A C /\ INJ f B C`,
  CHEAT_TAC);;

(* [local] *)
let LENGTH_list_rerrange = prove
 (`LENGTH (list_rearrange mover xs) = LENGTH xs`,
  CHEAT_TAC);;

(*For any 2 lists that are permutations of each other,
  We can give a list_rearranger that permutes one to the other*)
(* [local] *)
let list_rearrange_perm = prove
 (`PERM xs ys ==>
   (?perm. list_rearrange perm xs = ys)`,
  CHEAT_TAC);;

(* [local] *)
let GENLIST_MAP = prove
 (`!k. (!i. i < LENGTH l ==> m i < LENGTH l) /\ k <= LENGTH l ==>
         GENLIST (\i. EL (m i) (MAP f l)) k =
         MAP f (GENLIST (\i. EL (m i) l) k)`,
  CHEAT_TAC);;

let list_rearrange_MAP = prove
 (`!l f m. list_rearrange m (MAP f l) = MAP f (list_rearrange m l)`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:432: ML code, not ported *)

(*Main theorem for permute oracle usage!
  This shows that we can push locals that are exactly matching using
  any desired permutation
  and we can choose the final permutation to be anything we want
  (In Alloc we choose it to be cst.permute, in Call something
   given by the IH)
*)

(* [local] *)
let env_to_list_perm = prove
 (`!y x f perm tperm.
   domain y = IMAGE f (domain x) /\
   INJ f (domain x) UNIV /\
   strong_locals_rel f (domain x) x y ==>
   (let (l,permute) = env_to_list y perm in
   ?perm'.
     let (l',permute') = env_to_list x perm' in
       permute' = tperm /\
       // Just change the first permute
       MAP (\(x,y). f x,y) l' = l)`,
  CHEAT_TAC);;

(*Proves s_val_eq and some extra conditions on the resulting lists*)
let push_env_s_val_eq = prove
 (`!tperm.
   wordSem_state_handler
   st = wordSem_state_handler cst /\ stack
   st = stack cst /\ wordSem_state_locals_size
   st = wordSem_state_locals_size cst /\
   domain y = IMAGE f (domain x) /\
   INJ f (domain x) UNIV /\
   domain y' = IMAGE f (domain x') /\
   INJ f (domain x') UNIV /\
   strong_locals_rel f (domain x) x y /\
   (match b with NONE -> b' = NONE | SOME (w,h,l1,l2) ->
           (match b' with NONE -> F | SOME (a,b,c,d) -> c = l1 /\ d =
             l2)) ==>
   (?perm.
   (let (l,permute) = env_to_list y (wordSem_state_permute cst) in
   let (l',permute') = env_to_list x perm in
     permute' = tperm /\
     MAP (\(x,y). f x,y) l' = l /\
     (!x y. MEM x (MAP FST l') /\
       MEM y (MAP FST l') /\ f x = f y ==> x = y)) /\
   s_val_eq (stack (wordSem_push_env (x',x) b
     (wordSem_state_permute_fupd (K perm) st))) (stack
          (wordSem_push_env (y',y) b' cst)))`,
  CHEAT_TAC);;

(*TODO: Maybe move to props?
gc doesn't touch other components*)
let gc_frame = prove
 (`wordSem_gc st = SOME st' ==> wordSem_state_fp_regs
   st' = wordSem_state_fp_regs st /\ wordSem_state_mdomain
   st' = wordSem_state_mdomain st /\ wordSem_state_sh_mdomain
   st' = wordSem_state_sh_mdomain st /\ wordSem_state_gc_fun
   st' = wordSem_state_gc_fun st /\ wordSem_state_handler
   st' = wordSem_state_handler st /\ state_clock
   st' = state_clock st /\ wordSem_state_code
   st' = wordSem_state_code st /\ wordSem_state_locals
   st' = wordSem_state_locals st /\ wordSem_state_locals_size
   st' = wordSem_state_locals_size st /\ wordSem_state_stack_size
   st' = wordSem_state_stack_size st /\ wordSem_state_stack_max
   st' = wordSem_state_stack_max st /\ wordSem_state_stack_limit
   st' = wordSem_state_stack_limit st /\ wordSem_state_be
   st' = wordSem_state_be st /\ state_ffi
   st' = state_ffi st /\ wordSem_state_compile
   st' = wordSem_state_compile st /\ wordSem_state_compile_oracle
   st' = wordSem_state_compile_oracle st /\ wordSem_state_code_buffer
   st' = wordSem_state_code_buffer st /\ wordSem_state_data_buffer
   st' = wordSem_state_data_buffer st /\ wordSem_state_permute
   st' = wordSem_state_permute st /\ wordSem_state_termdep
   st' = wordSem_state_termdep st`,
  CHEAT_TAC);;

(* Convenient rewrite for pop_env
  TODO: do we need more on lsz'?
*)
let s_key_eq_val_eq_pop_env = prove
 (`wordSem_pop_env s = SOME s' /\
   s_key_eq (stack s) ((StackFrame n lsz ls opt) :: keys) /\
   s_val_eq (stack s) vals ==>
   (?lsz' ls' rest.
   vals = StackFrame n lsz' ls' opt :: rest /\ wordSem_state_locals
   s' =
     sptree_union (fromAList (ZIP (MAP FST ls) (MAP SND ls')))
       (fromAList lsz) /\
   s_key_eq (stack s') keys /\
   s_val_eq (stack s') rest /\
   (match opt with NONE -> wordSem_state_handler s' =
     wordSem_state_handler s | SOME (h,l1,l2) -> wordSem_state_handler
     s' = h))`,
  CHEAT_TAC);;

(*Less powerful form*)
let ALOOKUP_key_remap_2 = prove
 (`!ls vals f.
   (!x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y) /\
   LENGTH ls = LENGTH vals /\
   ALOOKUP (ZIP ls vals) n = SOME v ==>
   ALOOKUP (ZIP (MAP f ls) vals) (f n) = SOME v`,
  CHEAT_TAC);;

let ALOOKUP_key_remap_INJ = prove
 (`INJ f (n INSERT set_of_list ls) UNIV /\
   LENGTH ls = LENGTH vals ==>
   ALOOKUP (ZIP ls vals) n =
   ALOOKUP (ZIP (MAP f ls) vals) (f n)`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:657: ML code, not ported *)

(* [local] *)
let strong_locals_rel_subset = prove
 (`s SUBSET s' /\
   strong_locals_rel f s' stl cstl ==>
   strong_locals_rel f s stl cstl`,
  CHEAT_TAC);;

(* [local] *)
let env_to_list_keys = prove
 (`let (l,permute) = env_to_list x perm in
   set_of_list (MAP FST l) = domain x`,
  CHEAT_TAC);;

let list_rearrange_keys = prove
 (`list_rearrange perm (ls:('a#'b) list) = e ==>
   set_of_list (MAP FST e) = set_of_list (MAP FST ls)`,
  CHEAT_TAC);;

let list_rearrange_keys_2 = prove
 (`set_of_list (MAP FST (list_rearrange perm (ls:('a#'b) list))) =
  set_of_list (MAP FST ls)`,
  CHEAT_TAC);;

let MAP_FST_list_rearrange_keys_SORT = prove
 (`set_of_list (MAP FST (list_rearrange perm
     (sort key_val_compare (toAList x)))) = domain x`,
  CHEAT_TAC);;

(* [local] *)
let MAP_FST_keys_SORT = prove
 (`set_of_list (MAP FST (sort f (toAList x))) = domain x`,
  CHEAT_TAC);;

let pop_env_frame = prove
 (`s_val_eq (stack r') st' /\
   s_key_eq (stack y') (stack y'') /\
   wordSem_pop_env (stack_fupd (K st') r') = SOME y'' /\
   wordSem_pop_env r' = SOME y' ==>
   word_state_eq_rel y' y''`,
  CHEAT_TAC);;

let key_map_implies = prove
 (`MAP (\(x,y). f x,y) l' = l ==> MAP f (MAP FST l') = MAP FST l`,
  CHEAT_TAC);;

(*Main proof of liveness theorem starts here*)
(* HOL4 word_allocProofScript.sml:734-742: code that the source has
   in a comment *)

(* [local] *)
let apply_colour_exp_lemma = prove
 (`!st w cst f res.
     wordSem_word_exp st w = SOME res /\
     word_state_eq_rel st cst /\
     strong_locals_rel f (domain (get_live_exp w))
       (wordSem_state_locals st) (wordSem_state_locals cst) ==>
     wordSem_word_exp cst (apply_colour_exp f w) = SOME res`,
  CHEAT_TAC);;

let strong_locals_rel_insert = prove
 (`INJ f (n INSERT l) UNIV /\
   strong_locals_rel f (l DELETE n) st cst ==>
   strong_locals_rel f l (sptree_insert n v st) (sptree_insert (f
     n) v cst)`,
  CHEAT_TAC);;

(*Frequently used tactics*)
(* HOL4 word_allocProofScript.sml:798-800: a proof *)

(* HOL4 word_allocProofScript.sml:802-809: a proof *)

(* HOL4 word_allocProofScript.sml:811-813: a proof *)

(* [local] *)
let LASTN_LENGTH2 = prove
 (`LASTN (LENGTH xs + 1) (x :: xs) = x :: xs`,
  CHEAT_TAC);;

(* [local] *)
let toAList_not_empty = prove
 (`~(domain t = {}) ==> ~(toAList t = [])`,
  CHEAT_TAC);;

let PAIR_CASE_PAIR_MAP = prove
 (`pair_CASE ((f ## g) e) h = (match e with (x,y) -> h (f x) (g y))`,
  CHEAT_TAC);;

let permute_swap_lemma4 = prove
 (`(!st'. wordSem_evaluate (prog,st) = (SOME wordSem_Error,st') ==>
   P (SOME wordSem_Error,st')) /\ (?perm. P ((I ## (\s.
     wordSem_state_permute_fupd (K perm) s)) (wordSem_evaluate
     (prog,st)))) ==>
   (?perm. P (wordSem_evaluate (prog,wordSem_state_permute_fupd (K
     perm) st)))`,
  CHEAT_TAC);;

let MEM_ZIP_weak = prove
 (`LENGTH l1 = LENGTH l2 /\
   MEM (x1,x2) (ZIP l1 l2) ==>
   MEM x1 l1 /\ MEM x2 l2`,
  CHEAT_TAC);;

let strong_locals_rel_set_vars_dom = prove
 (`LENGTH ns = LENGTH ls /\
   INJ f X UNIV /\
   domain (wordSem_state_locals s) SUBSET X /\
   set_of_list ns SUBSET X /\
   strong_locals_rel f d (wordSem_state_locals s)
     (wordSem_state_locals t) ==>
   strong_locals_rel f d (wordSem_state_locals (wordSem_set_vars ns
     ls s)) (wordSem_state_locals (wordSem_set_vars (MAP f ns) ls t))`,
  CHEAT_TAC);;

let s_key_eq_push_env_imp_MAP_FST = prove
 (`s_key_eq (stack
     (wordSem_push_env (x',x'') o0 s))
     (StackFrame n' bb l opt :: ls) /\
   env_to_list x'' (wordSem_state_permute s) = (ll,res) ==>
   MAP FST ll = MAP FST l /\
   set_of_list (MAP FST bb) = domain x'`,
  CHEAT_TAC);;

let strong_locals_rel_set_var_dom = prove
 (`INJ f X UNIV /\
   domain (wordSem_state_locals s) SUBSET X /\
   n IN X /\
   strong_locals_rel f d (wordSem_state_locals s)
     (wordSem_state_locals t) ==>
   strong_locals_rel f d (wordSem_state_locals (wordSem_set_var n l
     s)) (wordSem_state_locals (wordSem_set_var (f n) l t))`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_extend_aux = prove
 (`domain src SUBSET s /\
   strong_locals_rel f s src tgt ==>
   strong_locals_rel f t src tgt`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_apply_colour_Loop_helper = prove
 (`!(st:('a,'c,'ffi)wordSem_state) cst f names body exit_names live lt.
     colouring_ok f (Loop names body exit_names) live lt /\
     word_state_eq_rel st cst /\
     strong_locals_rel f
       (domain (get_live (Loop names body exit_names) live lt))
         (wordSem_state_locals
       st) (wordSem_state_locals cst) /\
     (!(st:('a,'c,'ffi)wordSem_state) cst f live lt.
        colouring_ok f body live lt /\
        word_state_eq_rel st cst /\
        strong_locals_rel f (domain (get_live body live lt))
          (wordSem_state_locals
          st) (wordSem_state_locals cst) ==>
        (?perm'.
          (let (res,rst) = wordSem_evaluate
            (body,wordSem_state_permute_fupd (K perm') st) in
             res = SOME wordSem_Error \/
             (let (res',rcst) = wordSem_evaluate (apply_colour f
               body,cst) in
               res = res' /\ word_state_eq_rel rst rcst /\
               (match res with
                 NONE ->
                   strong_locals_rel f (domain live)
                     (wordSem_state_locals rst) (wordSem_state_locals
                     rcst) | SOME (Break n) ->
                   (match oEL n lt with SOME (_3,exit_names) ->
                        strong_locals_rel f (domain exit_names)
                          (wordSem_state_locals
                          rst) (wordSem_state_locals rcst) | NONE ->
                            T) | SOME (Continue n) ->
                   (match oEL n lt with SOME (names,_4) ->
                        strong_locals_rel f (domain names)
                          (wordSem_state_locals
                          rst) (wordSem_state_locals rcst) | NONE ->
                            T) | SOME _5 -> wordSem_state_locals rst =
                            wordSem_state_locals rcst))))) ==>
     (?perm'.
       (let (res,rst) = wordSem_evaluate
                          (Loop names body
                            exit_names,wordSem_state_permute_fupd (K
                            perm')
                           st) in
          res = SOME wordSem_Error \/
          (let (res',rcst) = wordSem_evaluate
                              (apply_colour f
                              (Loop names body exit_names),cst) in
            res = res' /\ word_state_eq_rel rst rcst /\
            (match res with
              NONE ->
                strong_locals_rel f (domain live)
                  (wordSem_state_locals rst) (wordSem_state_locals rcst)
                  | SOME (Break n) ->
                (match oEL n lt with SOME (_6,exit_names) ->
                     strong_locals_rel f (domain exit_names)
                       (wordSem_state_locals
                       rst) (wordSem_state_locals rcst) | NONE -> T)
                         | SOME (Continue n) ->
                (match oEL n lt with SOME (names,_7) ->
                     strong_locals_rel f (domain names)
                       (wordSem_state_locals
                       rst) (wordSem_state_locals rcst) | NONE ->
                         T) | SOME _8 -> wordSem_state_locals rst =
                         wordSem_state_locals rcst))))`,
  CHEAT_TAC);;

(*liveness theorem*)
let evaluate_apply_colour = prove
 (`!prog st cst f live lt.
   colouring_ok f prog live lt /\
   word_state_eq_rel (st:('a,'c,'ffi)wordSem_state) cst /\
   strong_locals_rel f (domain (get_live prog live lt))
     (wordSem_state_locals st) (wordSem_state_locals cst) ==>
   (?perm'.
   let (res,rst) = wordSem_evaluate (prog,wordSem_state_permute_fupd
     (K perm') st) in
   if (res = SOME wordSem_Error) then T else
   let (res',rcst) = wordSem_evaluate (apply_colour f prog,cst) in
     res = res' /\
     word_state_eq_rel rst rcst /\
     (match res with
       NONE -> strong_locals_rel f (domain live)
         (wordSem_state_locals
               rst) (wordSem_state_locals rcst) | SOME (Break n) ->
         (match oEL n lt with SOME (_9,exit_names) ->
              strong_locals_rel f (domain exit_names)
                (wordSem_state_locals rst) (wordSem_state_locals rcst) |
                NONE -> T) | SOME (Continue n) ->
         (match oEL n lt with SOME (names,_10) ->
              strong_locals_rel f (domain names)
                (wordSem_state_locals rst) (wordSem_state_locals rcst)
                | NONE -> T) | SOME _11 -> wordSem_state_locals rst =
                wordSem_state_locals rcst))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:1165-1167: a proof *)

(* HOL4 word_allocProofScript.sml:1169-1193: a proof *)
  (*NONE:
  Therefore n is not in l but it is in live and so it is not deleted
  *)
(* HOL4 word_allocProofScript.sml:1197-1223: a proof *)

(* HOL4 word_allocProofScript.sml:1225-1374: a proof *)
  (* All the FP cases *)
(* HOL4 word_allocProofScript.sml:1376-1394: a proof *)

(* HOL4 word_allocProofScript.sml:1396-1403: a proof *)

(* HOL4 word_allocProofScript.sml:1405-1411: a proof *)

(* HOL4 word_allocProofScript.sml:1413-1419: a proof *)

(* HOL4 word_allocProofScript.sml:1421-1431: a proof *)

(* HOL4 word_allocProofScript.sml:1433-1447: a proof *)

(* HOL4 word_allocProofScript.sml:1449-1480: a proof *)
  (*Returning calls*)
(* HOL4 word_allocProofScript.sml:1482-1592: a proof *)
  (*Result*)
(* HOL4 word_allocProofScript.sml:1594-1608: a proof *)
  (*finally using IH*)
(* HOL4 word_allocProofScript.sml:1610-1629: a proof *)
  (* Strong locals rel *)
(* HOL4 word_allocProofScript.sml:1631-1663: a proof *)
  (*Exception*)
(* HOL4 word_allocProofScript.sml:1665-1673: a proof *)
  (*No handler*)
(* HOL4 word_allocProofScript.sml:1675-1702: a proof *)
  (*Handler*)
(* HOL4 word_allocProofScript.sml:1704-1758: a proof *)
  (*Use IH*)
(* HOL4 word_allocProofScript.sml:1760-1769: a proof *)
  (* Strong locals rel *)
(* HOL4 word_allocProofScript.sml:1771-1799: a proof *)
  (*Remaining Cases*)
(* HOL4 word_allocProofScript.sml:1801-1809: a proof *)

(* HOL4 word_allocProofScript.sml:1811-1831: a proof *)

(* HOL4 word_allocProofScript.sml:1833-1881: a proof *)

(* HOL4 word_allocProofScript.sml:1883-1892: a proof *)

(* HOL4 word_allocProofScript.sml:1894-1976: a proof *)
      (* Strong locals rel *)
(* HOL4 word_allocProofScript.sml:1978-2022: a proof *)

(* HOL4 word_allocProofScript.sml:2024-2060: a proof *)

(* HOL4 word_allocProofScript.sml:2062-2067: a proof *)

(* HOL4 word_allocProofScript.sml:2069-2084: a proof *)

(* HOL4 word_allocProofScript.sml:2086-2090: a proof *)

(* HOL4 word_allocProofScript.sml:2092-2096: a proof *)

(* HOL4 word_allocProofScript.sml:2098-2100: a proof *)

(* HOL4 word_allocProofScript.sml:2102-2117: a proof *)

(* HOL4 word_allocProofScript.sml:2119-2131: a proof *)

(* HOL4 word_allocProofScript.sml:2133-2162: a proof *)

(* HOL4 word_allocProofScript.sml:2164-2171: a proof *)

(* HOL4 word_allocProofScript.sml:2173-2180: a proof *)

(* HOL4 word_allocProofScript.sml:2182-2205: a proof *)

(* HOL4 word_allocProofScript.sml:2207-2266: a proof *)

(* HOL4 word_allocProofScript.sml:2268: a proof *)

(* TODO: get_clash_sets, made redundant by clash tree *)

(* HOL4 word_allocProofScript.sml:2272-2383: code that the source has
   in a comment *)

(* [local] *)
let every_var_exp_get_live_exp = prove
 (`!exp.
   every_var_exp (\x. x IN domain (get_live_exp exp)) exp`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:2398-2589: code that the source has
   in a comment *)

(* Proofs for check_clash_tree *)
(* check_col_INJ *)
let word_allocProof_check_col_INJ = prove
 (`check_col f numset = SOME (q,r) ==>
   q = numset /\
   INJ f (domain q) UNIV /\
   domain r = IMAGE f (domain q)`,
  CHEAT_TAC);;

(* [local] *)
let wf_insert_swap = prove
 (`sptree_wf (t:1 spt) ==>
   sptree_insert (a:num) one (sptree_insert c one t) =
   sptree_insert (c:num) one (sptree_insert a one t)`,
  CHEAT_TAC);;

(*TODO: This is true without wf*)
(* [local] *)
let numset_list_insert_swap = prove
 (`!ls h live.
   sptree_wf live ==>
   sptree_wf (numset_list_insert ls live) /\
   numset_list_insert ls (sptree_insert h one live) =
   sptree_insert h one (numset_list_insert ls live)`,
  CHEAT_TAC);;

(* check_partial_col_INJ *)
let word_allocProof_check_partial_col_INJ = prove
 (`!ls f live flive live' flive'.
   sptree_wf live /\
   domain flive = IMAGE f (domain live) /\
   INJ f (domain live) UNIV /\
   check_partial_col f ls live flive = SOME (live',flive') ==>
   sptree_wf live' /\
   live' = numset_list_insert ls live /\
   INJ f (domain live') UNIV /\
   domain flive' = IMAGE f (domain live')`,
  CHEAT_TAC);;

(* [local] *)
let domain_insert_eq_union = prove
 (`domain (sptree_insert num one live) = domain (sptree_union
  (sptree_insert num one LN) live)`,
  CHEAT_TAC);;

(* [local] *)
let domain_numset_list_insert_eq_union = prove
 (`domain (numset_list_insert ls live) = domain (sptree_union
  (numset_list_insert ls LN) live)`,
  CHEAT_TAC);;

(* [local] *)
let get_reads_exp_get_live_exp = prove
 (`!exp.
   set_of_list (get_reads_exp exp) = domain (get_live_exp exp)`,
  CHEAT_TAC);;

(* [local] *)
let lookup_numset_list_insert = prove
 (`!ls n t.
   sptree_lookup n (numset_list_insert ls t) =
   (if MEM n ls then SOME one else sptree_lookup n t)`,
  CHEAT_TAC);;

(* [local] *)
let numset_list_insert_eq_UNION = prove
 (`!t t' ls.
   sptree_wf t /\ sptree_wf t' /\
   domain t' = set_of_list ls ==>
   numset_list_insert ls t =
   sptree_union t' t`,
  CHEAT_TAC);;

(* [local] *)
let wf_delete_swap = prove
 (`sptree_wf t ==>
   sptree_delete a (sptree_delete c t) =
   sptree_delete c (sptree_delete a t)`,
  CHEAT_TAC);;

(* [local] *)
let numset_list_delete_swap = prove
 (`!ls h live.
   sptree_wf live ==>
   sptree_wf (numset_list_delete ls live) /\
   numset_list_delete ls (sptree_delete h live) =
   sptree_delete h (numset_list_delete ls live)`,
  CHEAT_TAC);;

(* [local] *)
let wf_numset_list_delete_eq = prove
 (`!ls t live.
   sptree_wf t ==>
   ITLIST sptree_delete ls t = numset_list_delete ls t`,
  CHEAT_TAC);;

(* [local] *)
let wf_get_live_exp = prove
 (`!exp. sptree_wf (get_live_exp exp)`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:2791-2799: a proof *)

(* HOL4 word_allocProofScript.sml:2801-2804: a proof *)

(* IMAGE_DIFF *)
let word_allocProof_IMAGE_DIFF = prove
 (`INJ f (s UNION t) UNIV ==>
   IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t`,
  CHEAT_TAC);;

let clash_tree_colouring_ok = prove
 (`!prog lt f live flive livein flivein.
   wf_cutsets prog /\
   sptree_wf live /\
   EVERY (\(n,e). sptree_wf n /\ sptree_wf e) lt /\
   domain flive = IMAGE f (domain live) /\
   INJ f (domain live) UNIV /\
   check_clash_tree f (get_clash_tree prog lt) live flive = SOME
     (livein,flivein) ==>
   // very slow when this is not hidden...
   hide (sptree_wf livein /\
   INJ f (domain livein) UNIV /\
   colouring_ok f prog live lt /\
   livein = get_live prog live lt /\
   domain flivein = IMAGE f (domain livein))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:3270-3279: a proof *)

(* HOL4 word_allocProofScript.sml:3281-3289: a proof *)

(* HOL4 word_allocProofScript.sml:3291-3299: a proof *)

(* HOL4 word_allocProofScript.sml:3301: a proof *)

(*Actually, it should probably be exactly 0,2,4,6...*)
let even_starting_locals_def = cake_define
  `even_starting_locals (locs:('a word_loc) spt) <=>
     (!x. x IN domain locs ==> is_phy_var x)`;;

(* HOL4 word_allocProofScript.sml:3309: ML code, not ported *)

(* [local] *)
let get_forced_tail_split = prove
 (`!c p ls ls'.
   get_forced c p (ls ++ ls') =
   get_forced c p ls ++ ls'`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_get_forced = prove
 (`EVERY P (get_forced c p ls) <=>
   EVERY P (get_forced c p []) /\ EVERY P ls`,
  CHEAT_TAC);;

(* [local] *)
let get_forced_pairwise_distinct = prove
 (`!c prog ls.
   EVERY (\(x,y). ~(x = y)) ls ==>
   EVERY (\(x,y). ~(x = y)) (get_forced c prog ls)`,
  CHEAT_TAC);;

(* [local] *)
let get_forced_in_get_clash_tree = prove
 (`!prog lt c.
   EVERY (\(x,y). in_clash_tree (get_clash_tree prog lt) x /\
     in_clash_tree (get_clash_tree prog lt) y) (get_forced c prog [])`,
  CHEAT_TAC);;

let select_reg_alloc_correct = prove
 (`!alg spillcosts k heu_moves tree forced fs.
   EVERY (\(r1,r2). in_clash_tree tree r1 /\ in_clash_tree tree r2)
     forced ==>
   (?spcol livein flivein.
   select_reg_alloc alg spillcosts k heu_moves tree forced fs =
     M_success spcol /\
   check_clash_tree (sp_default spcol) tree LN LN = SOME
     (livein,flivein) /\
   (!r. in_clash_tree tree r ==>
     r IN domain spcol /\
     (if is_phy_var r then
       sp_default spcol r = r DIV 2 else if is_stack_var r then
       k <= (sp_default spcol r) else
       T)) /\
   (!r. r IN domain spcol ==> in_clash_tree tree r) /\
   EVERY (\(r1,r2). (sp_default spcol) r1 = (sp_default spcol) r2
     ==> r1 = r2) forced)`,
  CHEAT_TAC);;

(*Prove the full correctness theorem for word_alloc*)
let word_alloc_correct = prove
 (`!fc c alg prog k col_opt st.
   even_starting_locals (wordSem_state_locals st) /\
   wf_cutsets prog ==>
   (?perm'.
   let (res,rst) = wordSem_evaluate (prog,wordSem_state_permute_fupd
     (K perm') st) in
   if (res = SOME wordSem_Error) then T else
   let (res',rcst) = wordSem_evaluate (word_alloc fc c alg k prog
     col_opt,st) in
     res = res' /\
     word_state_eq_rel rst rcst /\
     (match res with
       NONE -> T | SOME (Break _12) -> T | SOME (Continue _13) -> T
         | SOME _14 -> wordSem_state_locals rst = wordSem_state_locals
         rcst))`,
  CHEAT_TAC);;

(* [local] *)
let apply_colour_exp_I = prove
 (`apply_colour_exp I exp = exp`,
  CHEAT_TAC);;

(* Dead code removal *)
let live_store_rel_def = cake_define
  `live_store_rel nlive sstore tstore <=>
   (!n. ~(n IN set_of_list nlive) ==>
     FLOOKUP sstore n = FLOOKUP tstore n)`;;

let live_store_rel_less = prove
 (`live_store_rel ls st tt /\
   set_of_list ls SUBSET set_of_list ls' ==>
   live_store_rel ls' st tt`,
  CHEAT_TAC);;

let live_store_rel_FLOOKUP_store = prove
 (`live_store_rel ls sstore tstore /\ ~(s IN set_of_list ls) ==>
   FLOOKUP tstore s = FLOOKUP sstore s`,
  CHEAT_TAC);;

let nlive_store_def = cake_define
  `nlive_store nlive x2 =
        match x2 with
          wordLang_Op _16 ls ->
         EVERY (nlive_store nlive) ls
        | (wordLang_Lookup s) -> ~(s IN set_of_list nlive)
        | (Load e) ->
       nlive_store nlive e
        | (Shift _17 e1 e2) ->
       nlive_store nlive e1 /\ nlive_store nlive e2
        | _18 -> T`;;

(* [local] *)
let strong_locals_rel_I_get_var = prove
 (`wordSem_get_var x st = SOME v /\
   strong_locals_rel I (x INSERT live) (wordSem_state_locals st) t
     ==>
   wordSem_get_var x (wordSem_state_store_fupd (K tstore)
     (wordSem_state_locals_fupd (K t) st)) = SOME v`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_I_get_var' = prove
 (`wordSem_get_var x st = SOME v /\
   strong_locals_rel I (x INSERT live) (wordSem_state_locals st) t
     ==>
   wordSem_get_var x (wordSem_state_locals_fupd (K t) st) = SOME v`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_I_word_exp = prove
 (`!st exp res.
   wordSem_word_exp st exp = SOME res /\
   strong_locals_rel I
     (domain (sptree_union (get_live_exp exp) live))
       (wordSem_state_locals st) t /\
   live_store_rel nlive (wordSem_state_store st) tstore /\
   nlive_store nlive exp ==>
   wordSem_word_exp (wordSem_state_store_fupd (K tstore)
     (wordSem_state_locals_fupd (K t) st)) exp = SOME res`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_insert_notin = prove
 (`strong_locals_rel f live s t /\ ~(n IN live) ==>
   strong_locals_rel f live (sptree_insert n v s) t`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_I_get_vars' = prove
 (`!ls live st t vs.
   (!x. MEM x ls ==> x IN live) /\
   strong_locals_rel I live (wordSem_state_locals st) t /\
   wordSem_get_vars ls st = SOME vs ==>
   wordSem_get_vars ls (wordSem_state_locals_fupd (K t) st) = SOME
     vs`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_I_cut_envs = prove
 (`strong_locals_rel I (domain (FST cutset) UNION domain (SND cutset))
  (wordSem_state_locals st) t /\
   cut_envs cutset (wordSem_state_locals st) = SOME x ==>
   cut_envs cutset t = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_I_cut_env = prove
 (`strong_locals_rel I (domain (FST cutset) UNION domain (SND cutset))
  (wordSem_state_locals st) t /\
   wordSem_cut_env cutset (wordSem_state_locals st) = SOME x ==>
   wordSem_cut_env cutset t = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let get_vars_eq = prove
 (`(set_of_list ls) SUBSET domain (wordSem_state_locals st) ==> (?z.
  wordSem_get_vars ls st = SOME z /\
                              z = MAP (\x. THE (sptree_lookup x
                                (wordSem_state_locals st))) ls)`,
  CHEAT_TAC);;

(* [local] *)
let get_vars_exists = prove
 (`!ls.
   (?z. wordSem_get_vars ls st = SOME z) <=>
   set_of_list ls SUBSET domain (wordSem_state_locals st)`,
  CHEAT_TAC);;

(* [local] *)
let strong_locals_rel_I_insert_insert = prove
 (`strong_locals_rel I (live DELETE p) A B /\
   v = v' ==>
   strong_locals_rel I live (sptree_insert p v A) (sptree_insert p
     v' B)`,
  CHEAT_TAC);;

(* [simp,local] *)
let st_eq = prove
 (`wordSem_state_store_fupd (K tstore) (wordSem_state_locals_fupd (K t)
     rst) = wordSem_state_store_fupd (K tstore')
       (wordSem_state_locals_fupd (K t')
     rst) <=>
     t = t' /\ tstore = tstore'`,
  CHEAT_TAC);;

(* [simp,local] *)
let live_store_rel_NIL = prove
 (`live_store_rel [] sstore tstore <=>
   sstore = tstore`,
  CHEAT_TAC);;

(* [simp,local] *)
let live_store_rel_refl = prove
 (`live_store_rel ls sstore sstore`,
  CHEAT_TAC);;

(* [simp,local] *)
let with_same_store = prove
 (`wordSem_state_store_fupd (K (wordSem_state_store st))
     st = st`,
  CHEAT_TAC);;

(* with_same_locals[simp,local] *)
let word_allocProof_with_same_locals = prove
 (`wordSem_state_locals_fupd (K (wordSem_state_locals st))
     st = st`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_remove_dead_Loop_helper = prove
 (`!(st:('a,'c,'ffi)wordSem_state) t tstore names body exit_names
     live nlive lt prog' livein nlivein res rst.
     strong_locals_rel I (domain livein) (wordSem_state_locals st) t
       /\
     live_store_rel nlivein (wordSem_state_store st) tstore /\
     wordSem_evaluate (Loop names body exit_names,st) = (res,rst) /\
     flat_exp_conventions body /\
     remove_dead (Loop names body exit_names) live nlive lt =
       (prog',livein,nlivein) /\
     nlivein = [] /\ ~(res = SOME wordSem_Error) /\
     (!(st':('a,'c,'ffi)wordSem_state) t' tstore' prog'' livein'
       nlivein' res' rst'.
        strong_locals_rel I (domain livein') (wordSem_state_locals
          st') t' /\
        live_store_rel nlivein' (wordSem_state_store st') tstore' /\
        wordSem_evaluate (body,st') = (res',rst') /\
        remove_dead body names [] ((names,exit_names) :: lt) =
          (prog'',livein',nlivein') /\ ~(res' = SOME wordSem_Error)
            ==>
        (?t'' tstore''.
          wordSem_evaluate (prog'',wordSem_state_store_fupd (K
            tstore') (wordSem_state_locals_fupd (K t') st')) =
            (res',wordSem_state_store_fupd (K tstore'')
              (wordSem_state_locals_fupd (K t'') rst')) /\
          (match res' with
             NONE ->
               strong_locals_rel I (domain names)
                 (wordSem_state_locals rst') t'' /\
               live_store_rel [] (wordSem_state_store rst') tstore''
                 | SOME (Break n) -> wordSem_state_store
               rst' = tstore'' /\
               (match oEL n ((names,exit_names) :: lt) with
                  SOME (_19,exit_names) ->
                    strong_locals_rel I (domain exit_names)
                      (wordSem_state_locals rst') t'' | NONE -> T) |
                      SOME (Continue n) -> wordSem_state_store
               rst' = tstore'' /\
               (match oEL n ((names,exit_names) :: lt) with
                  SOME (names,_20) ->
                    strong_locals_rel I (domain names)
                      (wordSem_state_locals rst') t'' | NONE -> T) |
                      SOME _21 -> wordSem_state_locals rst' = t'' /\
                      wordSem_state_store rst' = tstore''))) ==>
     (?t' tstore'.
       wordSem_evaluate (prog',wordSem_state_store_fupd (K tstore)
         (wordSem_state_locals_fupd (K t) st)) =
         (res,wordSem_state_store_fupd (K tstore')
           (wordSem_state_locals_fupd (K t') rst)) /\
       (match res with
          NONE ->
            strong_locals_rel I (domain live) (wordSem_state_locals
              rst) t' /\
            live_store_rel nlive (wordSem_state_store rst) tstore' |
              SOME (Break n) -> wordSem_state_store
            rst = tstore' /\
            (match oEL n lt with
               SOME (_22,exit_names) ->
                 strong_locals_rel I (domain exit_names)
                   (wordSem_state_locals rst) t' | NONE -> T) | SOME
                   (Continue n) -> wordSem_state_store
            rst = tstore' /\
            (match oEL n lt with
               SOME (names,_23) ->
                 strong_locals_rel I (domain names)
                   (wordSem_state_locals rst) t' | NONE -> T) | SOME
                   _24 -> wordSem_state_locals rst = t' /\
                   wordSem_state_store rst = tstore'))`,
  CHEAT_TAC);;

let evaluate_remove_dead = prove
 (`!prog live nlive lt prog' livein nlivein st t tstore res rst.
   strong_locals_rel I (domain livein) (wordSem_state_locals st) t /\
   live_store_rel nlivein (wordSem_state_store st) tstore /\
   wordSem_evaluate (prog,st) = (res,rst) /\
   flat_exp_conventions prog /\
   remove_dead prog live nlive lt = (prog',livein,nlivein) /\ ~(res =
     SOME wordSem_Error) ==>
   (?t' tstore'.
     wordSem_evaluate (prog',wordSem_state_store_fupd (K tstore)
       (wordSem_state_locals_fupd (K t) st)) =
       (res,wordSem_state_store_fupd (K tstore')
         (wordSem_state_locals_fupd (K t') rst)) /\
     (match res with
       NONE ->
         strong_locals_rel I (domain live) (wordSem_state_locals rst)
           t' /\
         live_store_rel nlive (wordSem_state_store rst) tstore' |
           SOME (Break n) -> wordSem_state_store
         rst = tstore' /\
         (match oEL n lt with
            SOME (_25,exit_names) ->
              strong_locals_rel I (domain exit_names)
                (wordSem_state_locals rst) t' | NONE -> T) | SOME
                (Continue n) -> wordSem_state_store
         rst = tstore' /\
         (match oEL n lt with
            SOME (names,_26) ->
              strong_locals_rel I (domain names)
                (wordSem_state_locals rst) t' | NONE -> T) | SOME _27
                -> wordSem_state_locals rst = t' /\
                wordSem_state_store rst = tstore'))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:3958-4029: a proof *)

(* HOL4 word_allocProofScript.sml:4031-4071: a proof *)

(* HOL4 word_allocProofScript.sml:4073-4088: a proof *)

(* HOL4 word_allocProofScript.sml:4090-4114: a proof *)

(* HOL4 word_allocProofScript.sml:4116-4121: a proof *)

(* HOL4 word_allocProofScript.sml:4123-4135: a proof *)

(* HOL4 word_allocProofScript.sml:4137-4155: a proof *)

(* HOL4 word_allocProofScript.sml:4157-4168: a proof *)

(* HOL4 word_allocProofScript.sml:4170-4173: a proof *)
  (* Reg: resolve get_var for register operand, then apply IH *)
(* HOL4 word_allocProofScript.sml:4175-4193: a proof *)
  (* Imm: apply IH directly *)
(* HOL4 word_allocProofScript.sml:4195-4210: a proof *)

(* HOL4 word_allocProofScript.sml:4212-4266: a proof *)

(* HOL4 word_allocProofScript.sml:4268-4279: a proof *)

(* HOL4 word_allocProofScript.sml:4281-4289: a proof *)

(* HOL4 word_allocProofScript.sml:4291-4294: a proof *)

(* HOL4 word_allocProofScript.sml:4296-4299: a proof *)

(* HOL4 word_allocProofScript.sml:4301-4318: a proof *)

(* HOL4 word_allocProofScript.sml:4320-4324: a proof *)

(* HOL4 word_allocProofScript.sml:4326-4332: a proof *)

(* HOL4 word_allocProofScript.sml:4334-4336: a proof *)

(* HOL4 word_allocProofScript.sml:4338-4345: a proof *)

(* HOL4 word_allocProofScript.sml:4347-4350: a proof *)

(* HOL4 word_allocProofScript.sml:4352-4374: a proof *)

(* HOL4 word_allocProofScript.sml:4376-4391: a proof *)

(* HOL4 word_allocProofScript.sml:4393-4408: a proof *)

(* HOL4 word_allocProofScript.sml:4410-4436: a proof *)

(* HOL4 word_allocProofScript.sml:4438-4469: a proof *)

(* HOL4 word_allocProofScript.sml:4471: a proof *)

let evaluate_remove_dead_prog = prove
 (`!prog st rst res.
   flat_exp_conventions prog /\
   wordSem_evaluate (prog,st) = (res,rst) /\ ~(res = SOME
     wordSem_Error) ==>
   (?t'.
     wordSem_evaluate (remove_dead_prog prog,st) =
       (res,wordSem_state_locals_fupd (K t') rst) /\
     (match res with
        NONE -> T | SOME (Break _28) -> T | SOME (Continue _29) ->
          T | SOME _30 -> wordSem_state_locals rst = t'))`,
  CHEAT_TAC);;

(*SSA Proof*)

(* HOL4 word_allocProofScript.sml:4506: ML code, not ported *)

(*This might not be the optimal invariant.. because it is very
  restrictive on the ssa_mapping*)
let ssa_locals_rel_def = cake_define
  `ssa_locals_rel na ssa st_locs cst_locs =
   ((!x y. sptree_lookup x ssa = SOME y ==> y IN domain cst_locs) /\
   (!x y. sptree_lookup x st_locs = SOME y ==>
     x IN domain ssa /\
     sptree_lookup (THE (sptree_lookup x ssa)) cst_locs = SOME y /\
     (is_alloc_var x ==> x < na)))`;;

(*ssa_map_ok specifies the form of ssa_maps we care about
  1) The remapped keys are ALL_DISTINCT
  2) The remap keyset is bounded, and no phy vars
*)
let ssa_map_ok_def = cake_define
  `ssa_map_ok na ssa =
   (!x y. sptree_lookup x ssa = SOME y ==>
     ~(is_phy_var y) /\ y < na)`;;

(* [local] *)
let list_next_var_rename_lemma_1 = prove
 (`!ls ssa na ls' ssa' na'.
   list_next_var_rename ls ssa na = (ls',ssa',na') ==>
   (let len = LENGTH ls in
   ALL_DISTINCT ls' /\
   ls' = (MAP (\x. 4 * x + na) (COUNT_LIST len)) /\
   na' = na + 4 * len)`,
  CHEAT_TAC);;

(* [local] *)
let list_next_var_rename_lemma_2 = prove
 (`!ls ssa na.
   ALL_DISTINCT ls ==>
   (let (ls',ssa',na') = list_next_var_rename ls ssa na in
   ls' = MAP (\x. THE (sptree_lookup x ssa')) ls /\
   domain ssa' = domain ssa UNION set_of_list ls /\
   (!x. ~(MEM x ls) ==> sptree_lookup x ssa' = sptree_lookup x ssa)
     /\
   (!x. MEM x ls ==> (?y. sptree_lookup x ssa' = SOME y)))`,
  CHEAT_TAC);;

(* [local] *)
let list_next_var_rename_lemma_2' = prove
 (`!ls ssa na ls' ssa' na'.
   list_next_var_rename ls ssa na = (ls',ssa',na') ==>
   ALL_DISTINCT ls ==>
   ls' = MAP (\x. THE (sptree_lookup x ssa')) ls /\
   domain ssa' = domain ssa UNION set_of_list ls /\
   (!x. ~(MEM x ls) ==> sptree_lookup x ssa' = sptree_lookup x ssa)
     /\
   (!x. MEM x ls ==> (?y. sptree_lookup x ssa' = SOME y))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:4594-4596: a proof *)

(* [local] *)
let ssa_locals_rel_get_var = prove
 (`ssa_locals_rel na ssa (wordSem_state_locals st) (wordSem_state_locals
  cst) /\
   wordSem_get_var n st = SOME x ==>
   wordSem_get_var (option_lookup ssa n) cst = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let ssa_locals_rel_get_vars = prove
 (`!ls y na ssa st cst.
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals cst) /\
   wordSem_get_vars ls st = SOME y ==>
   wordSem_get_vars (MAP (option_lookup ssa) ls) cst = SOME y`,
  CHEAT_TAC);;

(* [local] *)
let ssa_map_ok_extend = prove
 (`ssa_map_ok na ssa /\
   ~(is_phy_var na) ==>
   ssa_map_ok (na + 4) (sptree_insert h na ssa)`,
  CHEAT_TAC);;

(* [local] *)
let merge_moves_frame = prove
 (`!ls na ssaL ssaR.
   is_alloc_var na ==>
   (let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls
     ssaL ssaR na in
   is_alloc_var na' /\
   na <= na' /\
   (ssa_map_ok na ssaL ==> ssa_map_ok na' ssaL') /\
   (ssa_map_ok na ssaR ==> ssa_map_ok na' ssaR'))`,
  CHEAT_TAC);;

(* [local] *)
let merge_moves_fst = prove
 (`!ls na ssaL ssaR.
   let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL
     ssaR na in
   na <= na' /\
   EVERY (\x. x < na' /\ x >= na) (MAP FST moveL) /\
   EVERY (\x. x < na' /\ x >= na) (MAP FST moveR)`,
  CHEAT_TAC);;

(*Characterize result of merge_moves*)
(* [local] *)
let merge_moves_frame2 = prove
 (`!ls na ssaL ssaR.
   let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL
     ssaR na in
   domain ssaL' = domain ssaL /\
   domain ssaR' = domain ssaR /\
   (!x. MEM x ls /\ x IN domain (inter ssaL ssaR) ==>
     sptree_lookup x ssaL' = sptree_lookup x ssaR')`,
  CHEAT_TAC);;

(*Another frame proof about unchanged lookups*)
(* [local] *)
let merge_moves_frame3 = prove
 (`!ls na ssaL ssaR.
   let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls ssaL
     ssaR na in
   !x. ~(MEM x ls) \/ ~(x IN domain (inter ssaL ssaR)) ==>
     sptree_lookup x ssaL' = sptree_lookup x ssaL /\
     sptree_lookup x ssaR' = sptree_lookup x ssaR`,
  CHEAT_TAC);;

(*Don't know a neat way to prove this for both sides at once neatly,
Also, the cases are basically copy pasted... *)

(* [local] *)
let mov_eval_head = prove
 (`wordSem_evaluate (wordLang_Move p moves,st) = (NONE,rst) /\
   y IN domain (wordSem_state_locals st) /\
   ~(MEM y (MAP FST moves)) /\
   ~(MEM x (MAP FST moves)) ==>
   wordSem_evaluate (wordLang_Move p ((x,y) :: moves),st) =
     (NONE,wordSem_state_locals_fupd (K (sptree_insert x (THE
     (sptree_lookup y (wordSem_state_locals st)))
     (wordSem_state_locals rst))) rst)`,
  CHEAT_TAC);;

(* [local] *)
let merge_moves_correctL = prove
 (`!ls na ssaL ssaR stL cstL pri.
   is_alloc_var na /\
   ALL_DISTINCT ls /\
   ssa_map_ok na ssaL ==>
   (let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls
     ssaL ssaR na in
   (ssa_locals_rel na ssaL (wordSem_state_locals stL)
     (wordSem_state_locals cstL) ==>
   (let (resL,rcstL) = wordSem_evaluate (wordLang_Move pri
     moveL,cstL) in
     resL = NONE /\
     (!x. ~(MEM x ls) ==> sptree_lookup x ssaL' = sptree_lookup x
       ssaL) /\
     (!x y.
     (x < na /\ sptree_lookup x (wordSem_state_locals cstL) = SOME y)
       ==> sptree_lookup x (wordSem_state_locals rcstL) = SOME y) /\
     ssa_locals_rel na' ssaL' (wordSem_state_locals stL)
       (wordSem_state_locals rcstL) /\
     word_state_eq_rel cstL rcstL)))`,
  CHEAT_TAC);;

(* [local] *)
let merge_moves_correctR = prove
 (`!ls na ssaL ssaR stR cstR pri.
   is_alloc_var na /\
   ALL_DISTINCT ls /\
   ssa_map_ok na ssaR ==>
   (let (moveL,moveR,na',ssaL',ssaR') = word_alloc_merge_moves ls
     ssaL ssaR na in
   (ssa_locals_rel na ssaR (wordSem_state_locals stR)
     (wordSem_state_locals cstR) ==>
   (let (resR,rcstR) = wordSem_evaluate (wordLang_Move pri
     moveR,cstR) in
     resR = NONE /\
     (!x. ~(MEM x ls) ==> sptree_lookup x ssaR' = sptree_lookup x
       ssaR) /\
     (!x y.
     (x < na /\ sptree_lookup x (wordSem_state_locals cstR) = SOME y)
       ==> sptree_lookup x (wordSem_state_locals rcstR) = SOME y) /\
     ssa_locals_rel na' ssaR' (wordSem_state_locals stR)
       (wordSem_state_locals rcstR) /\
     word_state_eq_rel cstR rcstR)))`,
  CHEAT_TAC);;

(* [local] *)
let fake_moves_frame = prove
 (`!ls na ssaL ssaR.
   is_alloc_var na ==>
   (let (moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR
     na in
   is_alloc_var na' /\
   na <= na' /\
   (ssa_map_ok na ssaL ==> ssa_map_ok na' ssaL') /\
   (ssa_map_ok na ssaR ==> ssa_map_ok na' ssaR'))`,
  CHEAT_TAC);;

(* [local] *)
let fake_moves_frame2 = prove
 (`!ls na ssaL ssaR.
   let (moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR
     na in
   domain ssaL' = domain ssaL UNION (set_of_list ls INTER (domain
     ssaR UNION domain ssaL)) /\
   domain ssaR' = domain ssaR UNION (set_of_list ls INTER (domain
     ssaR UNION domain ssaL)) /\
   (!x. MEM x ls /\ ~(x IN domain (inter ssaL ssaR)) ==>
     sptree_lookup x ssaL' = sptree_lookup x ssaR')`,
  CHEAT_TAC);;

(* [local] *)
let fake_moves_frame3 = prove
 (`!ls na ssaL ssaR.
   let (moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR
     na in
   !x. ~(MEM x ls) \/ x IN domain (inter ssaL ssaR) ==>
     sptree_lookup x ssaL' = sptree_lookup x ssaL /\
     sptree_lookup x ssaR' = sptree_lookup x ssaR`,
  CHEAT_TAC);;

(* [local] *)
let fake_moves_correctL = prove
 (`!ls na ssaL ssaR stL cstL.
   is_alloc_var na /\
   ALL_DISTINCT ls /\
   ssa_map_ok na ssaL ==>
   (let (moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR
     na in
   (ssa_locals_rel na ssaL (wordSem_state_locals stL)
     (wordSem_state_locals cstL) ==>
   (let (resL,rcstL) = wordSem_evaluate (moveL,cstL) in
     resL = NONE /\
     (!x. ~(MEM x ls) ==> sptree_lookup x ssaL' = sptree_lookup x
       ssaL) /\
     (!x y.
     (x < na /\ sptree_lookup x (wordSem_state_locals cstL) = SOME y)
       ==> sptree_lookup x (wordSem_state_locals rcstL) = SOME y) /\
     ssa_locals_rel na' ssaL' (wordSem_state_locals stL)
       (wordSem_state_locals rcstL) /\
     word_state_eq_rel cstL rcstL)))`,
  CHEAT_TAC);;

(* [local] *)
let fake_moves_correctR = prove
 (`!ls na ssaL ssaR stR cstR.
   is_alloc_var na /\
   ALL_DISTINCT ls /\
   ssa_map_ok na ssaR ==>
   (let (moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR
     na in
   (ssa_locals_rel na ssaR (wordSem_state_locals stR)
     (wordSem_state_locals cstR) ==>
   (let (resR,rcstR) = wordSem_evaluate (moveR,cstR) in
     resR = NONE /\
     (!x. ~(MEM x ls) ==> sptree_lookup x ssaR' = sptree_lookup x
       ssaR) /\
     (!x y.
     (x < na /\ sptree_lookup x (wordSem_state_locals cstR) = SOME y)
       ==> sptree_lookup x (wordSem_state_locals rcstR) = SOME y) /\
     ssa_locals_rel na' ssaR' (wordSem_state_locals stR)
       (wordSem_state_locals rcstR) /\
     word_state_eq_rel cstR rcstR)))`,
  CHEAT_TAC);;

(*Swapping lemma that allows us to swap in ssaL for ssaR
  after we are done fixing them*)
(* [local] *)
let ssa_eq_rel_swap = prove
 (`ssa_locals_rel na ssaR (wordSem_state_locals st)
  (wordSem_state_locals cst) /\
   domain ssaL = domain ssaR /\
   (!x. sptree_lookup x ssaL = sptree_lookup x ssaR) ==>
   ssa_locals_rel na ssaL (wordSem_state_locals st)
     (wordSem_state_locals cst)`,
  CHEAT_TAC);;

(* [local] *)
let ssa_locals_rel_more = prove
 (`ssa_locals_rel na ssa stlocs cstlocs /\ na <= na' ==>
   ssa_locals_rel na' ssa stlocs cstlocs`,
  CHEAT_TAC);;

(* [local] *)
let ssa_map_ok_more = prove
 (`ssa_map_ok na ssa /\ na <= na' ==>
   ssa_map_ok na' ssa`,
  CHEAT_TAC);;

(* [local] *)
let get_var_ignore = prove
 (`!ls a.
   wordSem_get_var x cst = SOME y /\
   ~(MEM x ls) /\
   LENGTH ls = LENGTH a ==>
   wordSem_get_var x (wordSem_set_vars ls a cst) = SOME y`,
  CHEAT_TAC);;

(* [local] *)
let fix_inconsistencies_correctL = prove
 (`!na ssaL ssaR.
   is_alloc_var na /\
   ssa_map_ok na ssaL ==>
   (let (moveL,moveR,na',ssaU) = fix_inconsistencies prio ssaL ssaR
     na in
   (!(stL:('a,'b,'c)wordSem_state) (cstL:('a,'b,'c)wordSem_state).
   ssa_locals_rel na ssaL (wordSem_state_locals stL)
     (wordSem_state_locals cstL) ==>
   (let (resL,rcstL) = wordSem_evaluate (moveL,cstL) in
     resL = NONE /\
     ssa_locals_rel na' ssaU (wordSem_state_locals stL)
       (wordSem_state_locals rcstL) /\
     word_state_eq_rel cstL rcstL)))`,
  CHEAT_TAC);;

(* [local] *)
let fix_inconsistencies_correctR = prove
 (`!na ssaL ssaR prio.
   is_alloc_var na /\
   ssa_map_ok na ssaR ==>
   (let (moveL,moveR,na',ssaU) = fix_inconsistencies prio ssaL ssaR
     na in
   (!(stR:('a,'b,'c)wordSem_state) (cstR:('a,'b,'c)wordSem_state).
   ssa_locals_rel na ssaR (wordSem_state_locals stR)
     (wordSem_state_locals cstR) ==>
   (let (resR,rcstR) = wordSem_evaluate (moveR,cstR) in
     resR = NONE /\
     ssa_locals_rel na' ssaU (wordSem_state_locals stR)
       (wordSem_state_locals rcstR) /\
     word_state_eq_rel cstR rcstR)))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:5318-5325: ML code, not ported *)

(* [local] *)
let list_next_var_rename_move_preserve = prove
 (`!st ssa na ls cst.
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals cst) /\
   set_of_list ls SUBSET domain (wordSem_state_locals st) /\
   ALL_DISTINCT ls /\
   ssa_map_ok na ssa /\
   word_state_eq_rel st cst ==>
   (let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
   let (res,rcst) = wordSem_evaluate (mov,cst) in
     res = NONE /\
     ssa_locals_rel na' ssa' (wordSem_state_locals st)
       (wordSem_state_locals rcst) /\
     word_state_eq_rel st rcst /\
     (~(is_phy_var na) ==> (!w. is_phy_var w ==> sptree_lookup w
       (wordSem_state_locals rcst) = sptree_lookup w
       (wordSem_state_locals cst))) /\
     (!x y. sptree_lookup x (wordSem_state_locals st) = SOME y ==>
       sptree_lookup (THE (sptree_lookup x ssa)) (wordSem_state_locals
       rcst) = SOME y))`,
  CHEAT_TAC);;

(* [local] *)
let option_lookup_subset_helper = prove
 (`!ssa cst_locs ls.
     (!x y. sptree_lookup x ssa = SOME y ==> y IN domain cst_locs) /\
     set_of_list ls SUBSET domain ssa ==>
     set_of_list (MAP (option_lookup ssa) ls) SUBSET domain
       cst_locs`,
  CHEAT_TAC);;

(* [local] *)
let list_next_var_rename_move_preserve_weak = prove
 (`!st ssa na ls cst.
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals cst) /\
   set_of_list ls SUBSET domain ssa /\
   ALL_DISTINCT ls /\
   ssa_map_ok na ssa /\
   word_state_eq_rel st cst ==>
   (let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
   let (res,rcst) = wordSem_evaluate (mov,cst) in
     res = NONE /\
     ssa_locals_rel na' ssa' (wordSem_state_locals st)
       (wordSem_state_locals rcst) /\
     word_state_eq_rel st rcst)`,
  CHEAT_TAC);;

(* [local] *)
let get_vars_list_insert_eq_gen = prove
 (`!ls x locs a b.
   (LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\
                   LENGTH a = LENGTH b /\ (!e. MEM e ls ==> ~(MEM e
                     a))) ==> wordSem_get_vars ls
                     (wordSem_state_locals_fupd (K (alist_insert (a ++
                     ls) (b ++ x) locs)) st) = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let get_vars_set_vars_eq = prove
 (`!ls x.
   ALL_DISTINCT ls /\ LENGTH x = LENGTH ls ==>
   wordSem_get_vars ls (wordSem_set_vars ls x cst) = SOME x`,
  CHEAT_TAC);;

(* [local] *)
let ssa_locals_rel_ignore_set_var = prove
 (`ssa_map_ok na ssa /\
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals cst) /\
   is_phy_var v ==>
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals (wordSem_set_var v a cst))`,
  CHEAT_TAC);;

(* [local] *)
let ssa_locals_rel_ignore_insert = prove
 (`ssa_map_ok na ssa /\
   ssa_locals_rel na ssa stloc cstloc /\
   is_phy_var v ==>
   ssa_locals_rel na ssa stloc (sptree_insert v a cstloc)`,
  CHEAT_TAC);;


(* [local] *)
let ssa_locals_rel_ignore_list_insert = prove
 (`ssa_map_ok na ssa /\
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals cst) /\
   EVERY is_phy_var ls /\
   LENGTH ls = LENGTH x ==>
   ssa_locals_rel na ssa (wordSem_state_locals st) (alist_insert ls
     x (wordSem_state_locals cst))`,
  CHEAT_TAC);;

(* [local] *)
let ssa_locals_rel_set_var = prove
 (`ssa_locals_rel na ssa stl cstl /\
   ssa_map_ok na ssa /\
   n < na ==>
   ssa_locals_rel (na + 4) (sptree_insert n na ssa) (sptree_insert
     n w stl) (sptree_insert na w cstl)`,
  CHEAT_TAC);;

(* [local] *)
let ssa_locals_rel_insert = prove
 (`ssa_locals_rel na ssa stloc cstloc /\
   ssa_map_ok na ssa /\
   n < na ==>
   ssa_locals_rel (na + 4) (sptree_insert n na ssa) (sptree_insert
     n w stloc) (sptree_insert na w cstloc)`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:5667-5671: a proof *)

(* [local] *)
let ssa_locals_rel_list_next_var_rename = prove
 (`!xs ssa na stloc cstloc ys ssa' na' ls.
   list_next_var_rename xs ssa na = (ys,ssa',na') /\
   ssa_locals_rel na ssa stloc cstloc /\
   ssa_map_ok na ssa /\
   LENGTH xs = LENGTH ls /\
   EVERY (\x. x < na) xs /\
   ALL_DISTINCT xs /\
   ~(is_phy_var na) ==>
   ssa_locals_rel na' ssa' (alist_insert xs ls stloc) (alist_insert
     ys ls cstloc)`,
  CHEAT_TAC);;

(* [local] *)
let is_alloc_var_add = prove
 (`is_alloc_var na ==> is_alloc_var (na + 4)`,
  CHEAT_TAC);;

(* [local] *)
let is_stack_var_add = prove
 (`is_stack_var na ==> is_stack_var (na + 4)`,
  CHEAT_TAC);;

(* [local] *)
let is_alloc_var_flip = prove
 (`is_alloc_var na ==> is_stack_var (na + 2)`,
  CHEAT_TAC);;

(* [local] *)
let is_stack_var_flip = prove
 (`is_stack_var na ==> is_alloc_var (na + 2)`,
  CHEAT_TAC);;

(*ordered such that its easy to drule*)
(* [local] *)
let list_next_var_rename_props = prove
 (`!ls ssa na ls' ssa' na'.
   list_next_var_rename ls ssa na = (ls',ssa',na') ==>
   (is_alloc_var na \/ is_stack_var na) /\
   ssa_map_ok na ssa ==>
   na <= na' /\
   (is_alloc_var na ==> is_alloc_var na') /\
   (is_stack_var na ==> is_stack_var na') /\
   ssa_map_ok na' ssa'`,
  CHEAT_TAC);;

(*ordered such that its easy to drule*)
(* [local] *)
let list_next_var_rename_move_props = prove
 (`!ls ssa na ls' ssa' na'.
   list_next_var_rename_move ssa na ls = (ls',ssa',na') ==>
   (is_alloc_var na \/ is_stack_var na) /\
   ssa_map_ok na ssa ==>
   na <= na' /\
   (is_alloc_var na ==> is_alloc_var na') /\
   (is_stack_var na ==> is_stack_var na') /\
   ssa_map_ok na' ssa'`,
  CHEAT_TAC);;

(* [local] *)
let next_var_rename_props = prove
 (`next_var_rename ls ssa na = (ls',ssa',na') ==>
   (is_alloc_var na \/ is_stack_var na) /\
   ssa_map_ok na ssa ==>
   na <= na' /\
   (is_alloc_var na ==> is_alloc_var na') /\
   (is_stack_var na ==> is_stack_var na') /\
   ssa_map_ok na' ssa'`,
  CHEAT_TAC);;

(*ordered such that its easy to drule*)
(* [local] *)
let ssa_cc_trans_inst_props = prove
 (`!i ssa na i' ssa' na'.
   ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
   ssa_map_ok na ssa /\
   is_alloc_var na ==>
   na <= na' /\
   is_alloc_var na' /\
   ssa_map_ok na' ssa'`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:5834-5836: a proof *)

(* [local] *)
let fix_inconsistencies_props = prove
 (`!ssaL ssaR na a b na' ssaU.
   fix_inconsistencies prio ssaL ssaR na = (a,b,na',ssaU) ==>
   is_alloc_var na /\
   ssa_map_ok na ssaL /\
   ssa_map_ok na ssaR ==>
   na <= na' /\
   is_alloc_var na' /\
   ssa_map_ok na' ssaU`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:5857-5860: ML code, not ported *)

(* [local] *)
let flip_rw = prove
 (`is_stack_var (na + 2) = is_alloc_var na /\
     is_alloc_var (na + 2) = is_stack_var na`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:5876: the ML values that the
   definitions below antiquote *)

(* HOL4 word_allocProofScript.sml:5878-5892: ML code, not ported *)

(* [local] *)
let ssa_map_ok_lem = prove
 (`ssa_map_ok na ssa ==> ssa_map_ok (na + 2) ssa`,
  CHEAT_TAC);;

(*ordered such that its easy to drule*)
(* [local] *)
let list_next_var_rename_move_props_2 = prove
 (`!ls ssa na ls' ssa' na'.
   list_next_var_rename_move ssa (na + 2) ls = (ls',ssa',na') ==>
   (is_alloc_var na \/ is_stack_var na) /\ ssa_map_ok na ssa ==>
   (na + 2) <= na' /\
   (is_alloc_var na ==> is_stack_var na') /\
   (is_stack_var na ==> is_alloc_var na') /\
   ssa_map_ok na' ssa'`,
  CHEAT_TAC);;

(* [local] *)
let ssa_map_ok_inter = prove
 (`ssa_map_ok na ssa ==>
   ssa_map_ok na (inter ssa ssa')`,
  CHEAT_TAC);;

let ssa_map_ok_insert = prove
 (`ssa_map_ok na ssa /\
   y < na /\ ~(is_phy_var y) ==>
   ssa_map_ok na (sptree_insert x y ssa)`,
  CHEAT_TAC);;

let ssa_map_ok_force_rename = prove
 (`!ls ssa.
   ssa_map_ok na ssa /\
   EVERY (\x. SND x < na /\ ~(is_phy_var (SND x))) ls ==>
   ssa_map_ok na (force_rename ls ssa)`,
  CHEAT_TAC);;


(*Prove the properties that hold of ssa_cc_trans independent of semantics*)
(* [local] *)
let ssa_cc_trans_props = prove
 (`!prog ssa na lt prog' ssa' na'.
   ssa_cc_trans prog ssa na lt = (prog',ssa',na') ==>
   ssa_map_ok na ssa /\
   is_alloc_var na ==>
   na <= na' /\
   is_alloc_var na' /\
   ssa_map_ok na' ssa'`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:6177-6200: a proof *)

(* HOL4 word_allocProofScript.sml:6202-6204: a proof *)

(* HOL4 word_allocProofScript.sml:6206-6208: a proof *)

(* HOL4 word_allocProofScript.sml:6210: a proof *)

(* [local] *)
let PAIR_ZIP_MEM = prove
 (`LENGTH c = LENGTH d /\
   MEM (a,b) (ZIP c d) ==>
   MEM a c /\ MEM b d`,
  CHEAT_TAC);;

(* [local] *)
let ALOOKUP_ZIP_MEM = prove
 (`LENGTH a = LENGTH b /\
   ALOOKUP (ZIP a b) x = SOME y ==>
   MEM x a /\ MEM y b`,
  CHEAT_TAC);;

(* [local] *)
let ALOOKUP_ALL_DISTINCT_REMAP = prove
 (`!ls x f y n.
   LENGTH ls = LENGTH x /\
   ALL_DISTINCT (MAP f ls) /\
   n < LENGTH ls /\
   ALOOKUP (ZIP ls x) (EL n ls) = SOME y ==>
   ALOOKUP (ZIP (MAP f ls) x) (f (EL n ls)) = SOME y`,
  CHEAT_TAC);;

(* [local] *)
let ssa_cc_trans_exp_correct = prove
 (`!st w cst ssa na res.
   wordSem_word_exp st w = SOME res /\
   word_state_eq_rel st cst /\
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals cst) ==>
   wordSem_word_exp cst (ssa_cc_trans_exp ssa w) = SOME res`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:6294-6303: a proof *)

(* HOL4 word_allocProofScript.sml:6305-6308: a proof *)

(* [local] *)
let get_var_set_vars_notin = prove
 (`~(MEM v ls) /\
   LENGTH ls = LENGTH vs ==>
   wordSem_get_var v (wordSem_set_vars ls vs st) = wordSem_get_var
     v st`,
  CHEAT_TAC);;

let ssa_locals_rel_delete_left = prove
 (`ssa_locals_rel na ssa stl cstl ==>
   ssa_locals_rel na ssa (sptree_delete n stl) cstl`,
  CHEAT_TAC);;

let ssa_locals_rel_delete_right = prove
 (`ssa_map_ok na ssa /\ ssa_locals_rel na ssa stl cstl /\ is_phy_var n
  ==>
   ssa_locals_rel na ssa stl (sptree_delete n cstl)`,
  CHEAT_TAC);;

let lookup_force_rename_aux = prove
 (`!ls ssa.
   sptree_lookup x (force_rename (REVERSE ls) ssa) =
   (match ALOOKUP ls x with
     NONE -> sptree_lookup x ssa | SOME y -> SOME y)`,
  CHEAT_TAC);;

let lookup_force_rename = prove
 (`sptree_lookup x (force_rename ls ssa) =
   (match ALOOKUP (REVERSE ls) x with
     NONE -> sptree_lookup x ssa | SOME y -> SOME y)`,
  CHEAT_TAC);;

let domain_force_rename = prove
 (`domain (force_rename ls ssa) =
     domain ssa UNION set_of_list (MAP FST ls)`,
  CHEAT_TAC);;

let ssa_locals_rel_force_rename = prove
 (`ssa_locals_rel na ssa st1 st2 /\
   EVERY (\x. sptree_lookup (FST x) st1 = sptree_lookup (SND x) st2)
     ls /\
   set_of_list (MAP SND ls) SUBSET domain st2 ==>
   ssa_locals_rel na (force_rename ls ssa) st1 st2`,
  CHEAT_TAC);;

let list_next_var_rename_move_distinct = prove
 (`list_next_var_rename_move ssa na ls = (mov,ssa',na') /\
   ALL_DISTINCT ls /\
   MEM x ls /\ MEM y ls /\
   option_lookup ssa' x = option_lookup ssa' y ==>
   x = y`,
  CHEAT_TAC);;
(*TODO move*)

let get_vars_NOT_MEM = prove
 (`~(MEM h xs) ==>
   wordSem_get_vars xs (wordSem_state_locals_fupd (K (sptree_insert
     h h' ys)) cs) = wordSem_get_vars xs (wordSem_state_locals_fupd (K
     ys) cs)`,
  CHEAT_TAC);;

let get_vars_eq_alist_insert = prove
 (`!regs' l.
   ALL_DISTINCT regs' /\
   LENGTH regs' = LENGTH l /\
   (!x. MEM x regs' ==>
   sptree_lookup x (wordSem_state_locals st) =
   sptree_lookup x (alist_insert regs' l rest)) ==>
   wordSem_get_vars regs' st = SOME l`,
  CHEAT_TAC);;

let cut_envs_domain_SUBSET = prove
 (`cut_envs (x1,x2) locs = SOME x ==>
   domain x1 SUBSET domain locs /\
   domain x2 SUBSET domain locs`,
  CHEAT_TAC);;

(* [local] *)
let ssa_reconcile_distinct_lemma = prove
 (`!f g ns.
     INJ f (domain ns) UNIV ==>
     ALL_DISTINCT (MAP FST
       (FILTER (\(a,b). ~(a = b))
         (MAP (\v. (f v,g v)) (MAP FST (toAList ns)))))`,
  CHEAT_TAC);;

(* [local] *)
let ssa_reconcile_moves_eq = prove
 (`!L.
     FILTER (\(a,b). ~(a = b)) (FLAT (MAP (\v. match sptree_lookup v
       m with NONE -> [] | SOME cv -> [(f v,cv)]) L)) =
     MAP (\v. (f v,THE (sptree_lookup v m)))
       (FILTER (\v. match sptree_lookup v m with NONE -> F | SOME
         cv -> ~(f v = cv)) L)`,
  CHEAT_TAC);;

(* [local] *)
let ssa_reconcile_filtered_all_distinct = prove
 (`ALL_DISTINCT (FILTER (\v. match sptree_lookup v cur_ssa with NONE ->
  F | SOME cv -> ~(option_lookup tgt_ssa v = cv))
                   (MAP FST (toAList ns)))`,
  CHEAT_TAC);;

(* [local] *)
let ssa_reconcile_filtered_in_dom = prove
 (`!v. MEM v (FILTER (\v. match sptree_lookup v cur_ssa with NONE -> F |
  SOME cv -> ~(option_lookup tgt_ssa v = cv))
               (MAP FST (toAList ns))) ==>
     v IN domain ns /\
     (?cv. sptree_lookup v cur_ssa = SOME cv /\ ~(option_lookup
       tgt_ssa v = cv) /\
          THE (sptree_lookup v cur_ssa) = cv)`,
  CHEAT_TAC);;

(* [local] *)
let ssa_reconcile_get_vars_lemma = prove
 (`!ls cur_ssa (cst:('a,'b,'c)wordSem_state).
     ALL_DISTINCT ls /\
     (!v. MEM v ls ==>
          (?val'. sptree_lookup (THE (sptree_lookup v cur_ssa))
            (wordSem_state_locals cst) = SOME val')) ==>
     (?vs. wordSem_get_vars (MAP (\v. THE (sptree_lookup v cur_ssa))
       ls) cst = SOME vs /\
          LENGTH vs = LENGTH ls /\
          (!i. i < LENGTH ls ==>
              sptree_lookup (THE (sptree_lookup (EL i ls) cur_ssa))
                (wordSem_state_locals cst) = SOME (EL i vs)))`,
  CHEAT_TAC);;

(* [local] *)
let alookup_zip_map_some = prove
 (`!ls vs i f.
     ALL_DISTINCT (MAP f ls) /\
     i < LENGTH ls /\
     LENGTH vs = LENGTH ls ==>
     ALOOKUP (ZIP (MAP f ls) vs) (f (EL i ls)) = SOME (EL i vs)`,
  CHEAT_TAC);;

(* [local] *)
let alookup_zip_map_option_lookup_none = prove
 (`!ls vs n ns f.
     INJ f (domain ns) UNIV /\
     n IN domain ns /\
     ~(MEM n ls) /\
     (!v. MEM v ls ==> v IN domain ns) /\
     LENGTH vs = LENGTH ls ==>
     ALOOKUP (ZIP (MAP f ls) vs) (f n) = NONE`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_ssa_reconcile = prove
 (`ssa_locals_rel na cur_ssa st_locs (wordSem_state_locals cst) /\
   INJ (option_lookup tgt_ssa) (domain ns) UNIV ==>
   (?cst'.
     wordSem_evaluate (ssa_reconcile cur_ssa tgt_ssa ns,cst) =
       (NONE,cst') /\
     word_state_eq_rel cst cst' /\
     strong_locals_rel (option_lookup tgt_ssa) (domain ns) st_locs
       (wordSem_state_locals cst'))`,
  CHEAT_TAC);;

let lt_ok_def = cake_define
  `lt_ok lt <=>
     EVERY (\(tgt_ssa,names,exit_names).
       INJ (option_lookup tgt_ssa) (domain names) UNIV /\
       INJ (option_lookup tgt_ssa) (domain exit_names) UNIV) lt`;;

(* [local] *)
let foldr_insert_const_swap = prove
 (`!rs h (v:'a word_loc) m.
     ITLIST (\r loc. sptree_insert r v loc) rs (sptree_insert h v m)
       =
     sptree_insert h v (ITLIST (\r loc. sptree_insert r v loc) rs
       m)`,
  CHEAT_TAC);;

(* Evaluating a chain of fake_move r writes 0 to each register in rs,
   leaves the rest of state untouched. *)
(* [local] *)
let evaluate_fake_const_chain = prove
 (`!rs (cst:('a,'b,'c)wordSem_state).
     wordSem_evaluate (ITLIST Seq (MAP (\r. (fake_move r):'a
       wordLang_prog) rs) Skip,cst) =
       (NONE,wordSem_state_locals_fupd (K (ITLIST (\r loc.
         sptree_insert r (wordLang_Word (n2w 0)) loc) rs
         (wordSem_state_locals cst))) cst)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_fake_const_chain_locals = prove
 (`!rs (cst:('a,'b,'c)wordSem_state).
     let rcst = SND (wordSem_evaluate (ITLIST Seq
       (MAP (\r. (fake_move r):'a wordLang_prog) rs) Skip,cst)) in
     word_state_eq_rel cst rcst /\
     domain (wordSem_state_locals rcst) = domain
       (wordSem_state_locals cst) UNION set_of_list rs /\
     (!r. ~(MEM r rs) ==> sptree_lookup r (wordSem_state_locals rcst)
       = sptree_lookup r (wordSem_state_locals cst)) /\
     (!r. MEM r rs ==> sptree_lookup r (wordSem_state_locals rcst)
       = SOME (wordLang_Word (n2w 0)))`,
  CHEAT_TAC);;

(* Bundles the (extend, fake_init, refresh) Loop-entry setup. Establishes
   ssa_locals_rel under ssa_refreshed and INJ on names/exit_names domains
   by construction. *)
(* [local] *)
let loop_setup_correct = prove
 (`!(st:('a,'b,'c)wordSem_state) cst ssa na names exit_names
     setup_prog ssa_refreshed na_refreshed.
     word_state_eq_rel st cst /\
     ssa_locals_rel na ssa (wordSem_state_locals st)
       (wordSem_state_locals cst) /\
     ssa_map_ok na ssa /\
     is_alloc_var na /\
     loop_setup names exit_names ssa na =
       (setup_prog,ssa_refreshed,na_refreshed) ==>
     (?rcst.
       wordSem_evaluate (setup_prog,cst) = (NONE,rcst) /\
       word_state_eq_rel st rcst /\
       ssa_locals_rel na_refreshed ssa_refreshed
         (wordSem_state_locals st) (wordSem_state_locals rcst) /\
       na <= na_refreshed /\
       is_alloc_var na_refreshed /\
       ssa_map_ok na_refreshed ssa_refreshed /\
       domain ssa_refreshed = domain ssa UNION domain (sptree_union
         names exit_names) /\
       INJ (option_lookup ssa_refreshed) (domain names) UNIV /\
       INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV /\
       (!v. v IN domain ssa_refreshed ==>
         option_lookup ssa_refreshed v IN domain
           (wordSem_state_locals rcst)))`,
  CHEAT_TAC);;

(* If P evaluates to (NONE, t), Seq P Q evaluates as Q from t. *)
(* [local] *)
let evaluate_seq_collapse = prove
 (`wordSem_evaluate (P,s) = (NONE,t) ==>
   wordSem_evaluate (Seq P Q,s) = wordSem_evaluate (Q,t)`,
  CHEAT_TAC);;

(* fromAList (MAP f (toAList LN)) behaves like LN in cut_env. *)
(* [local] *)
let cut_env_fromAList_LN = prove
 (`wordSem_cut_env (a,fromAList (MAP (g:num#1->num#1) (toAList LN))) v =
   wordSem_cut_env (a,LN) v`,
  CHEAT_TAC);;

(* Helper for Loop iter; target is the INNER Loop (not the full translation),
   so the clock-IH recursive call lines up with the inner Loop's STOP-recursion
   without re-running the outer fake_prog + refresh_mov setup each iter. *)
(* [local] *)
let ssa_cc_trans_Loop_helper = prove
 (`!(st:('a,'b,'c)wordSem_state) cst ssa_refreshed na_refreshed
     names body exit_names lt body' ssa' na'.
     word_state_eq_rel st cst /\
     strong_locals_rel (option_lookup ssa_refreshed) (domain names)
       (wordSem_state_locals
       st) (wordSem_state_locals cst) /\
     (!v. v IN domain names ==>
        option_lookup ssa_refreshed v IN domain (wordSem_state_locals
          cst)) /\
     ssa_map_ok na_refreshed ssa_refreshed /\
     is_alloc_var na_refreshed /\
     wordLang_every_var (\x. x < na_refreshed) body /\
     INJ (option_lookup ssa_refreshed) (domain names) UNIV /\
     INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV /\
     domain names SUBSET domain ssa_refreshed /\
     domain exit_names SUBSET domain ssa_refreshed /\
     EVERY (\x. x < na_refreshed) (MAP FST (toAList names)) /\
     EVERY (\x. x < na_refreshed) (MAP FST (toAList exit_names)) /\
     lt_ok lt /\
     ssa_cc_trans body (inter ssa_refreshed names) na_refreshed
       ((ssa_refreshed,names,exit_names) :: lt) = (body',ssa',na') /\
     (!(st':('a,'b,'c)wordSem_state) cst' ssa'' na'' lt'.
        word_state_eq_rel st' cst' /\
        ssa_locals_rel na'' ssa'' (wordSem_state_locals st')
          (wordSem_state_locals cst') /\
        is_alloc_var na'' /\
        wordLang_every_var (\x. x < na'') body /\
        ssa_map_ok na'' ssa'' /\
        lt_ok lt' ==>
        (?perm'.
          (let (res,rst) = wordSem_evaluate
            (body,wordSem_state_permute_fupd (K perm') st') in
             res = SOME wordSem_Error \/
             (let (prog',ssaB,naB) = ssa_cc_trans body ssa'' na'' lt'
               in let
                  (res',rcst) = wordSem_evaluate (prog',cst') in
                res = res' /\ word_state_eq_rel rst rcst /\
                (match res with
                  NONE -> ssa_locals_rel naB ssaB
                    (wordSem_state_locals rst) (wordSem_state_locals
                    rcst) | SOME (Break n) ->
                    (match oEL n lt' with
                       NONE -> T | SOME (tgt_ssa,_31,exit_names) ->
                         strong_locals_rel (option_lookup tgt_ssa)
                           (domain exit_names) (wordSem_state_locals
                             rst) (wordSem_state_locals rcst)) | SOME
                             (Continue n') ->
                    (match oEL n' lt' with
                       NONE -> T | SOME (tgt_ssa,names,_32) ->
                         strong_locals_rel (option_lookup tgt_ssa)
                           (domain names) (wordSem_state_locals rst)
                             (wordSem_state_locals rcst)) | SOME _33 ->
                             wordSem_state_locals rst =
                             wordSem_state_locals rcst))))) ==>
     (let back_moves = ssa_reconcile ssa' ssa_refreshed names in
     let body_final = (if back_moves = Skip then body' else Seq body'
       back_moves) in
     let ssa_names = apply_nummap_key (option_lookup ssa_refreshed)
       names in
     let ssa_exit = apply_nummap_key (option_lookup ssa_refreshed)
       exit_names in
     !res' rcst.
       wordSem_evaluate (Loop ssa_names body_final ssa_exit,cst) =
         (res',rcst) ==>
       (?perm'.
         (\(res,rst).
             res = SOME wordSem_Error \/
             res = res' /\ word_state_eq_rel rst rcst /\
             (match res with
               NONE -> ssa_locals_rel na' (inter ssa_refreshed
                 exit_names) (wordSem_state_locals
                         rst) (wordSem_state_locals rcst) | SOME
                           (Break n) ->
                 (match oEL n lt with
                    NONE -> T | SOME (tgt_ssa,_34,exit_names) ->
                      strong_locals_rel (option_lookup tgt_ssa)
                        (domain exit_names) (wordSem_state_locals
                          rst) (wordSem_state_locals rcst)) | SOME
                          (Continue n') ->
                 (match oEL n' lt with
                    NONE -> T | SOME (tgt_ssa,names,_35) ->
                      strong_locals_rel (option_lookup tgt_ssa)
                        (domain names) (wordSem_state_locals rst)
                          (wordSem_state_locals rcst)) | SOME _36 ->
                          wordSem_state_locals rst =
                          wordSem_state_locals rcst))
           (wordSem_evaluate (Loop names body
             exit_names,wordSem_state_permute_fupd (K perm') st))))`,
  CHEAT_TAC);;

(* [local] *)
let ssa_cut_inter_lemma = prove
 (`domain ssa' INTER domain (sptree_union x1 x2) = domain x1 UNION
  domain x2 ==>
   xx IN domain (sptree_union x1 x2) ==>
   xx IN domain ssa'`,
  CHEAT_TAC);;

let ssa_cc_trans_correct = prove
 (`!prog st cst ssa na lt.
   word_state_eq_rel st cst /\
   ssa_locals_rel na ssa (wordSem_state_locals st)
     (wordSem_state_locals cst) /\
   // The following 3 assumptions are from the transform properties and
   // are independent of semantics
   is_alloc_var na /\
   wordLang_every_var (\x. x < na) prog /\
   ssa_map_ok na ssa /\
   lt_ok lt ==>
   (?perm'.
   let (res,rst) = wordSem_evaluate (prog,wordSem_state_permute_fupd
     (K perm') st) in
   if (res = SOME wordSem_Error) then T else
   let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
   let (res',rcst) = wordSem_evaluate (prog',cst) in
     res = res' /\
     word_state_eq_rel rst rcst /\
     (match res with
       NONE ->
         ssa_locals_rel na' ssa' (wordSem_state_locals rst)
           (wordSem_state_locals rcst) | SOME (Break n) ->
         (match oEL n lt with
            SOME (tgt_ssa,_37,exit_names) ->
              strong_locals_rel (option_lookup tgt_ssa) (domain
                exit_names) (wordSem_state_locals
                rst) (wordSem_state_locals rcst) | NONE -> T) | SOME
                  (Continue n) ->
         (match oEL n lt with
            SOME (tgt_ssa,names,_38) ->
              strong_locals_rel (option_lookup tgt_ssa) (domain
                names) (wordSem_state_locals
                rst) (wordSem_state_locals rcst) | NONE -> T) |
                  SOME _39 -> wordSem_state_locals rst =
                  wordSem_state_locals rcst))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:7736-7738: a proof *)

(* HOL4 word_allocProofScript.sml:7740-7751: a proof *)
    (* The ssa'' map would have been fine to return without
      forcing the renames too *)
(* HOL4 word_allocProofScript.sml:7754-7823: a proof *)
    (* but we force some new mappings *)
(* HOL4 word_allocProofScript.sml:7825-7858: a proof *)

(* HOL4 word_allocProofScript.sml:7860-7955: a proof *)
        (* is_x64 *)
(* HOL4 word_allocProofScript.sml:7957-7982: a proof *)
(* HOL4 word_allocProofScript.sml:7983-7996: code that the source has
   in a comment *)
(* HOL4 word_allocProofScript.sml:7997-8182: a proof *)
          (* Nasty special case for 32-bit FPMovFromReg *)
(* HOL4 word_allocProofScript.sml:8184-8207: a proof *)
      (* Special case for two writes *)
(* HOL4 word_allocProofScript.sml:8209-8222: a proof *)

(* HOL4 word_allocProofScript.sml:8224-8226: a proof *)

(* HOL4 word_allocProofScript.sml:8228-8230: a proof *)

(* HOL4 word_allocProofScript.sml:8232-8234: a proof *)

(* HOL4 word_allocProofScript.sml:8236-8249: a proof *)

(* HOL4 word_allocProofScript.sml:8251-8266: a proof *)

(* HOL4 word_allocProofScript.sml:8268-8296: a proof *)

(* HOL4 word_allocProofScript.sml:8298-8338: a proof *)
    (*Establish invariants about ssa_cut to use later*)
(* HOL4 word_allocProofScript.sml:8340-8351: a proof *)
    (*Probably need to case split here to deal with the 2 cases*)
(* HOL4 word_allocProofScript.sml:8353-8383: a proof *)
      (*Important preservation step*)
(* HOL4 word_allocProofScript.sml:8385-8392: a proof *)
      (*Try to use cut_envs_lemma from word_live*)
(* HOL4 word_allocProofScript.sml:8394-8458: a proof *)
        (*Backwards chaining*)
(* HOL4 word_allocProofScript.sml:8460-8468: a proof *)
        (*This went missing somewhere..*)
(* HOL4 word_allocProofScript.sml:8470-8474: ML code, not ported *)
        (*Now is a good place to establish the invariant ssa_locals_rel*)
(* HOL4 word_allocProofScript.sml:8476-8546: a proof *)
        (*We set the return variables but it is never in the
          locals so the ssa_locals_rel property is preserved*)
(* HOL4 word_allocProofScript.sml:8549-8631: a proof *)
        (*"Hot-swap" the suffix of perm, maybe move into lemma*)
(* HOL4 word_allocProofScript.sml:8633-8645: a proof *)
        (*Excepting without handler*)
(* HOL4 word_allocProofScript.sml:8647-8677: a proof *)
        (* 4 subgoals *)
(* HOL4 word_allocProofScript.sml:8679-8685: a proof *)
    (*Handler reasoning*)
(* HOL4 word_allocProofScript.sml:8687-8719: a proof *)
    (*Important preservation lemma*)
(* HOL4 word_allocProofScript.sml:8721-8733: a proof *)
    (*Try to use cut_env_lemma from word_live*)
(* HOL4 word_allocProofScript.sml:8735-8786: a proof *)
    (*More props theorems that will be useful*)
(* HOL4 word_allocProofScript.sml:8788-9191: a proof *)
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
(* HOL4 word_allocProofScript.sml:9193-9226: a proof *)

(* HOL4 word_allocProofScript.sml:9228-9261: a proof *)

(* HOL4 word_allocProofScript.sml:9263-9331: a proof *)

(* HOL4 word_allocProofScript.sml:9333-9459: a proof *)
    (*Establish invariants about ssa_cut to use later*)
(* HOL4 word_allocProofScript.sml:9461-9606: a proof *)

(* HOL4 word_allocProofScript.sml:9608-9647: a proof *)

(* HOL4 word_allocProofScript.sml:9649-9654: a proof *)

(* HOL4 word_allocProofScript.sml:9656-9687: a proof *)

(* HOL4 word_allocProofScript.sml:9689-9692: a proof *)

(* HOL4 word_allocProofScript.sml:9694-9704: a proof *)

(* HOL4 word_allocProofScript.sml:9706-9708: a proof *)

(* HOL4 word_allocProofScript.sml:9710-9858: a proof *)

(* HOL4 word_allocProofScript.sml:9860-9862: a proof *)

(* HOL4 word_allocProofScript.sml:9864-9866: a proof *)

(* HOL4 word_allocProofScript.sml:9868: a proof *)
    (*FFI*)
(* HOL4 word_allocProofScript.sml:9870-10010: a proof *)

(* HOL4 word_allocProofScript.sml:10012-10045: a proof *)

(* HOL4 word_allocProofScript.sml:10047-10096: a proof *)

(* HOL4 word_allocProofScript.sml:10098-10115: a proof *)

(* HOL4 word_allocProofScript.sml:10117-10134: a proof *)

(* HOL4 word_allocProofScript.sml:10136: a proof *)

(*For starting up*)
(* [local] *)
let setup_ssa_props = prove
 (`is_alloc_var lim /\
   domain (wordSem_state_locals st) = set_of_list (even_list n) ==>
   (let ((mov:'a wordLang_prog),ssa,na) = setup_ssa n lim (prog:'a
     wordLang_prog) in
   let (res,cst) = wordSem_evaluate (mov,st) in
     res = NONE /\
     word_state_eq_rel st cst /\
     ssa_map_ok na ssa /\
     ssa_locals_rel na ssa (wordSem_state_locals st)
       (wordSem_state_locals cst) /\
     is_alloc_var na /\
     lim <= na)`,
  CHEAT_TAC);;

(* [local] *)
let max_var_exp_max = prove
 (`!exp.
     every_var_exp (\x. x <= max_var_exp exp) exp`,
  CHEAT_TAC);;

(* [local] *)
let max_var_inst_max = prove
 (`!inst'.
     every_var_inst (\x. x <= max_var_inst inst') inst'`,
  CHEAT_TAC);;

(* [local] *)
let max3_eq = prove
 (`!x y z. max3 x y z = MAX x (MAX y z)`,
  CHEAT_TAC);;

let max_var_max = prove
 (`!prog.
   wordLang_every_var (\x. x <= max_var prog) prog`,
  CHEAT_TAC);;

(* [local] *)
let limit_var_props = prove
 (`limit_var prog = lim ==>
   is_alloc_var lim /\
   wordLang_every_var (\x. x < lim) prog`,
  CHEAT_TAC);;

(*Full correctness theorem*)
let full_ssa_cc_trans_correct = prove
 (`!prog st n.
    domain (wordSem_state_locals st) = set_of_list (even_list n) ==>
    (?perm'.
    let (res,rst) = wordSem_evaluate (prog,wordSem_state_permute_fupd
      (K perm') st) in
    if (res = SOME wordSem_Error) then T else
    let (res',rcst) = wordSem_evaluate (full_ssa_cc_trans n prog,st)
      in
      res = res' /\
      word_state_eq_rel rst rcst /\
      (match res with
        NONE -> T | SOME (Break _40) -> T | SOME (Continue _41) ->
          T | SOME _42 -> wordSem_state_locals rst =
          wordSem_state_locals rcst))`,
  CHEAT_TAC);;

(* Prove that the ssa form sets up pre_alloc_conventions
   and preserves some syntactic conventions
*)
(* [local] *)
let fake_moves_conventions = prove
 (`!ls ssaL ssaR na.
   let (a,b,c,d,e) = fake_moves prio ls ssaL ssaR na in
   every_stack_var is_stack_var a /\
   every_stack_var is_stack_var b /\
   call_arg_convention a /\
   call_arg_convention b`,
  CHEAT_TAC);;

(* [local] *)
let fix_inconsistencies_conventions = prove
 (`!ssaL ssaR na prio.
   let ((a:'a wordLang_prog),(b:'a wordLang_prog),c,d) =
     fix_inconsistencies prio ssaL ssaR na in
   every_stack_var is_stack_var a /\
   every_stack_var is_stack_var b /\
   call_arg_convention a /\
   call_arg_convention b`,
  CHEAT_TAC);;

let every_name_def2 = prove
 (`every_name P t = EVERY P (MAP FST (toAList (sptree_union (FST t)
  (SND t))))`,
  CHEAT_TAC);;

(* [local] *)
let union_apply_nummaps_key = prove
 (`domain (sptree_union (FST (apply_nummaps_key (f) p))
                       (SND (apply_nummaps_key (f) p))) =
   domain (apply_nummap_key (f) (sptree_union (FST p) (SND p)))`,
  CHEAT_TAC);;

(* [local] *)
let fake_seq_pre_alloc_conventions = prove
 (`!ls. pre_alloc_conventions (ITLIST Seq (MAP (\r. fake_move r) ls)
  Skip)`,
  CHEAT_TAC);;

(* [local] *)
let fake_seq_every_inst_distinct_tar_reg = prove
 (`!ls. every_inst distinct_tar_reg (ITLIST Seq (MAP (\r. fake_move r)
  ls) Skip)`,
  CHEAT_TAC);;

(* [local] *)
let fake_seq_full_inst_ok_less = prove
 (`!c ls. full_inst_ok_less c (ITLIST Seq (MAP (\r. fake_move r) ls)
  Skip)`,
  CHEAT_TAC);;

(* [local] *)
let loop_setup_pre_alloc_conventions = prove
 (`loop_setup names exit_names ssa na =
  (setup_prog,ssa_refreshed,na_refreshed) ==>
   pre_alloc_conventions setup_prog`,
  CHEAT_TAC);;

(* [local] *)
let loop_setup_props_local = prove
 (`loop_setup names exit_names ssa na =
  (setup_prog,ssa_refreshed,na_refreshed) /\
   ssa_map_ok na ssa /\ is_alloc_var na ==>
   is_alloc_var na_refreshed /\ ssa_map_ok na_refreshed ssa_refreshed
     /\
   na <= na_refreshed`,
  CHEAT_TAC);;

(* [local] *)
let loop_setup_every_inst_distinct_tar_reg = prove
 (`loop_setup names exit_names ssa na =
  (setup_prog,ssa_refreshed,na_refreshed) ==>
   every_inst distinct_tar_reg setup_prog`,
  CHEAT_TAC);;

(* [local] *)
let loop_setup_full_inst_ok_less = prove
 (`loop_setup names exit_names ssa na =
  (setup_prog,ssa_refreshed,na_refreshed) ==>
   full_inst_ok_less c setup_prog`,
  CHEAT_TAC);;

(*Prove that the transform sets up arbitrary programs with
  the appropriate conventions*)
let ssa_cc_trans_pre_alloc_conventions = prove
 (`!prog ssa na lt.
   is_alloc_var na /\
   ssa_map_ok na ssa ==>
   (let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
   pre_alloc_conventions prog')`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:10716-10731: a proof *)

(* HOL4 word_allocProofScript.sml:10733-10736: a proof *)

(* HOL4 word_allocProofScript.sml:10738-10741: a proof *)

(* HOL4 word_allocProofScript.sml:10743: a proof *)

(* [local] *)
let setup_ssa_props_2 = prove
 (`is_alloc_var lim ==>
   (let ((mov:'a wordLang_prog),ssa,na) = setup_ssa n lim (prog:'a
     wordLang_prog) in
     ssa_map_ok na ssa /\
     is_alloc_var na /\
     pre_alloc_conventions mov /\
     lim <= na)`,
  CHEAT_TAC);;

let full_ssa_cc_trans_pre_alloc_conventions = prove
 (`!n prog.
    pre_alloc_conventions (full_ssa_cc_trans n prog)`,
  CHEAT_TAC);;

(* [local] *)
let fake_moves_distinct_tar_reg = prove
 (`!ls ssal ssar na l r a b c conf.
   fake_moves prio ls ssal ssar na = (l,r,a,b,c) ==>
   every_inst distinct_tar_reg l /\
   every_inst distinct_tar_reg r`,
  CHEAT_TAC);;

let ssa_cc_trans_distinct_tar_reg = prove
 (`!prog ssa na lt.
     is_alloc_var na /\
     wordLang_every_var (\x. x < na) prog /\
     ssa_map_ok na ssa ==>
     every_inst distinct_tar_reg (FST (ssa_cc_trans prog ssa na
       lt))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:10922-10939: a proof *)

(* HOL4 word_allocProofScript.sml:10941-10944: a proof *)

(* HOL4 word_allocProofScript.sml:10946-10949: a proof *)

(* HOL4 word_allocProofScript.sml:10951: a proof *)

let full_ssa_cc_trans_distinct_tar_reg = prove
 (`!n prog.
     every_inst distinct_tar_reg (full_ssa_cc_trans n prog)`,
  CHEAT_TAC);;

(* [local] *)
let exp_to_addr_ShareInst = prove
 (`exp_to_addr exp = SOME (Addr n c) <=>
     ((exp = Var n /\ c = (n2w 0)) \/ (exp = wordLang_Op asm_Add
       [Var n; Const c]))`,
  CHEAT_TAC);;

(* [local] *)
let fake_moves_conventions2 = prove
 (`!ls ssal ssar na l r a b c conf.
   fake_moves prio ls ssal ssar na = (l,r,a,b,c) ==>
   full_inst_ok_less conf l /\
   full_inst_ok_less conf r /\
   every_inst distinct_tar_reg l /\
   every_inst distinct_tar_reg r`,
  CHEAT_TAC);;

(* [local] *)
let ssa_cc_trans_full_inst_ok_less = prove
 (`!prog ssa na lt c.
     wordLang_every_var (\x. x < na) prog /\
     is_alloc_var na /\
     ssa_map_ok na ssa /\
     full_inst_ok_less c prog ==>
     full_inst_ok_less c (FST (ssa_cc_trans prog ssa na lt))`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:11124-11140: a proof *)

(* HOL4 word_allocProofScript.sml:11142-11145: a proof *)

(* HOL4 word_allocProofScript.sml:11147-11150: a proof *)

(* HOL4 word_allocProofScript.sml:11152: a proof *)

let full_ssa_cc_trans_full_inst_ok_less = prove
 (`!prog n c.
   full_inst_ok_less c prog ==>
   full_inst_ok_less c (full_ssa_cc_trans n prog)`,
  CHEAT_TAC);;

(* word_alloc syntactic stuff *)

(* HOL4 word_allocProofScript.sml:11176-11180: a proof *)

(* [local] *)
let call_arg_convention_preservation = prove
 (`!prog f.
   wordLang_every_var (\x. is_phy_var x ==> f x = x) prog /\
   call_arg_convention prog ==>
   call_arg_convention (apply_colour f prog)`,
  CHEAT_TAC);;

(*Composing with a function using apply_colour*)
let every_var_inst_apply_colour_inst = prove
 (`!P inst' Q f.
   every_var_inst P inst' /\
   (!x. P x ==> Q (f x)) ==>
   every_var_inst Q (apply_colour_inst f inst')`,
  CHEAT_TAC);;

let every_var_exp_apply_colour_exp = prove
 (`!P exp Q f.
   every_var_exp P exp /\
   (!x. P x ==> Q (f x)) ==>
   every_var_exp Q (apply_colour_exp f exp)`,
  CHEAT_TAC);;

(* [local] *)
let every_apply_nummap_key_helper = prove
 (`!f names P Q.
   EVERY P (MAP FST (toAList names)) /\ (!x. P x ==> Q (f x)) ==>
   EVERY Q (MAP FST (toAList (fromAList (MAP (\((x:num),(y:1)). (f
     x,one)) (toAList names)))))`,
  CHEAT_TAC);;

let every_var_apply_colour = prove
 (`!P prog Q f.
   wordLang_every_var P prog /\
   (!x. P x ==> Q (f x)) ==>
   wordLang_every_var Q (apply_colour f prog)`,
  CHEAT_TAC);;

let every_stack_var_apply_colour = prove
 (`!P prog Q f.
   every_stack_var P prog /\
   (!x. P x ==> Q (f x)) ==>
   every_stack_var Q (apply_colour f prog)`,
  CHEAT_TAC);;

(* [local] *)
let every_var_exp_get_reads_exp = prove
 (`!exp. every_var_exp (\x. MEM x (get_reads_exp exp)) exp`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:11302-11305: a proof *)

(* [local] *)
let every_var_in_get_clash_tree = prove
 (`!prog lt.
   wordLang_every_var (in_clash_tree (get_clash_tree prog lt)) prog`,
  CHEAT_TAC);;

(* [local] *)
let every_var_T = prove
 (`!prog.
   wordLang_every_var (\x. T) prog`,
  CHEAT_TAC);;

(* [local] *)
let every_var_is_phy_var_total_colour = prove
 (`wordLang_every_var is_phy_var (apply_colour (total_colour col)
  prog)`,
  CHEAT_TAC);;

(* [local] *)
let oracle_colour_ok_conventions = prove
 (`pre_alloc_conventions prog /\
   oracle_colour_ok k col_opt (get_clash_tree prog lt) prog ls = SOME
     x ==>
   post_alloc_conventions k x`,
  CHEAT_TAC);;

let pre_post_conventions_word_alloc = prove
 (`!fc c alg prog k col_opt.
   pre_alloc_conventions prog ==>
   post_alloc_conventions k (word_alloc fc c alg k prog col_opt)`,
  CHEAT_TAC);;

(*word_alloc preserves syntactic conventions*)
(* [local] *)
let word_alloc_full_inst_ok_less_lem = prove
 (`!f prog c.
   full_inst_ok_less c prog /\
   EVERY (\(x,y). ~((f x) = (f y))) (get_forced c prog []) ==>
   full_inst_ok_less c (apply_colour f prog)`,
  CHEAT_TAC);;

(* HOL4 word_allocProofScript.sml:11437-11448: code that the source
   has in a comment *)

(* [local] *)
let forced_distinct_col = prove
 (`EVERY (\(x,y). (sp_default spcol) x = (sp_default spcol) y ==> x = y)
  ls /\
   EVERY (\(x,y). ~(x = y)) ls ==>
   EVERY (\(x,y). ~((total_colour spcol) x = (total_colour spcol)
     y)) ls`,
  CHEAT_TAC);;

let word_alloc_full_inst_ok_less = prove
 (`!fc alg k prog col_opt c.
   full_inst_ok_less c prog ==>
   full_inst_ok_less c (word_alloc fc c alg k prog col_opt)`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "mem";
   "not";
   "sloc";
   "val"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
