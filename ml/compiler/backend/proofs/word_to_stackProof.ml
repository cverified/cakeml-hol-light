(* ======================================================== *)
(*  word_to_stackProof: ported from HOL4's
    compiler/backend/proofs/word_to_stackProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_to_stack
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/reg_alloc/parmove.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: (* for extend_with_resource_limit
   *) (* for list_Seq *) (* for extract_labels *) (* for
   word_add_carry_def *) *)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/lab_to_targetProof.ml";;
needs "compiler/backend/proofs/stack_removeProof.ml";;
needs "compiler/backend/reg_alloc/parmove.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* Set up ML bindings *)
(* HOL4 ML code, not ported:
open preamble semanticsPropsTheory stackSemTheory wordSemTheory
     word_to_stackTheory wordPropsTheory wordConvsTheory
       stackPropsTheory
     parmoveTheory helperLib;
*)

(* HOL4 ML code, not ported:
val get_labels_def = stackSemTheory.get_labels_def;
val extract_labels_def = stackPropsTheory.extract_labels_def
*)
(* HOL4 type abbreviation (expanded in the port):
     state = (α,β,γ)wordSem$state *)
(* HOL4 overload (expanded in the port):
     word_cmp = wordSem$word_cmp *)

(* HOL4 ML code, not ported:
val nn = ``(NONE:(num # 'a wordLang$prog # num # num) option)``
*)

(* HOL4 ML code, not ported:
val s = ``s:('a,num # 'c,'ffi) wordSem$state``
val t = ``t:('a,'c,'ffi) stackSem$state``
*)

(* TODO: move to word/stackProps? *)

(* Move to props END *)

(* TODO delete *)

(* delete END *)

(*misc word stuff*)
(*misc word_stuff end*)

(* TODO figure a normal form.
  Should set_store be pushed out always?*)

(*Equality theorems available if n ≤ LENGTH ls*)

(*Strengthened version of LASTN_DROP after change to make it total*)
(* TODO: many things in this file need moving *)

(* HOL4 ML code, not ported:
val the_eqn = backendPropsTheory.the_eqn
*)

let index_list_def = cake_define_list
  [`index_list [] n = []`;
   `index_list (x :: xs) n = (n + LENGTH xs,x) :: index_list xs n`];;

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)

(*MEM to an EL characterization for index lists*)

let list_LUPDATE_def = cake_define_list
  [`list_LUPDATE [] n ys = ys`;
   `list_LUPDATE (x :: xs) n ys = list_LUPDATE xs (n + 1) (LUPDATE x
  n ys)`];;

(* move to stackProps? *)

(* move to wordProps? *)

(* state relation *)

(*Abstracts a stackLang stack w.r.t. wordLang's
  Note: requires assumption on dimindex(:'a) stated in state_rel *)
let abs_stack_def = cake_define
  `abs_stack bitmaps x2 stack x4 =
        match (bitmaps,x2,stack,x4) with
          ((bitmaps:('a word) list),[],stack,[]) ->
       (if stack = [wordLang_Word ((n2w 0):'a word)] then SOME []
         else NONE)
        | (bitmaps,((StackFrame n l0 l NONE) :: xs),(w :: stack),(len
          :: lens)) ->
       (match full_read_bitmap bitmaps w with NONE -> NONE | SOME
         bits ->
           (if ~(LENGTH bits = len) then NONE else
           if LENGTH stack < len then NONE else
             let frame = TAKE len stack in
             let rest = DROP len stack in
               match abs_stack bitmaps xs rest lens with NONE -> NONE
                 | SOME ys -> SOME ((NONE,bits,frame) :: ys)))
        | (bitmaps,((StackFrame n l0 l (SOME _1)) :: xs),(w ::
          stack),(len :: lens)) ->
       (if ~(w = wordLang_Word (n2w 1)) then NONE else
         (match stack with loc :: hv :: w :: stack ->
            (match full_read_bitmap bitmaps w with NONE -> NONE |
              SOME bits ->
                 (if ~(LENGTH bits = len) then NONE else
                 if LENGTH stack < len then NONE else
                   let frame = TAKE len stack in
                   let rest = DROP len stack in
                     match abs_stack bitmaps xs rest lens with NONE
                       -> NONE | SOME ys -> SOME ((SOME
                       (loc,hv),bits,frame) :: ys))) | _2 -> NONE))
        | (bitmaps,_3,_4,_5) -> NONE`;;

(* HOL4 ML code, not ported:
val abs_stack_ind = theorem"abs_stack_ind";
*)

(*TODO this should probably be an Overload*)
let MAP_FST_def = cake_define
  `MAP_FST f xs = MAP (\(x,y). (f x,y)) xs`;;

let adjust_names_def = cake_define
  `adjust_names n = n DIV 2`;;

(*handler_val counts the total number of words in the list of frames*)
let handler_val_def = cake_define_list
  [`handler_val [] = 1`;
   `handler_val ((NONE,_6,frame) :: stack) =
        1 + LENGTH frame + handler_val stack`;
   `handler_val ((SOME _7,_8,frame) :: stack) =
        4 + LENGTH frame + handler_val stack`];;

let is_handler_frame_def = cake_define
  `is_handler_frame x1 =
        match x1 with
          StackFrame n l0 l NONE -> F
        | _9 -> T`;;

(*Checks for consistency of the values*)
let stack_rel_aux_def = cake_define
  `stack_rel_aux k len x3 x4 =
        match (x3,x4) with
          ([],[]) -> T
        | (((StackFrame n l0 l NONE) :: xs),((NONE,bits,frame) ::
          stack)) ->
       (!n v.
         ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ==>
         adjust_names n < k + LENGTH bits /\
         oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F
           /\
         ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
       filter_bitmap bits (index_list frame k) = SOME (MAP_FST
         adjust_names l,[]) /\
       the (LENGTH frame + 1) n = LENGTH frame + 1 /\
       stack_rel_aux k len xs stack
        | (((StackFrame n l0 l (SOME (h1,l1,l2))) :: xs),((SOME
          (loc,hv),bits,frame) :: stack)) ->
       (h1 < LENGTH stack /\
       is_handler_frame (EL (LENGTH stack - (h1 + 1)) xs) ==>
       hv = wordLang_Word (n2w (len - handler_val (LASTN (h1 + 1)
         stack)))) /\
       loc = Loc l1 l2 /\
       (!n v.
         ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ==>
         adjust_names n < k + LENGTH bits /\
         oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F
           /\
         ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
       filter_bitmap bits (index_list frame k) = SOME (MAP_FST
         adjust_names l,[]) /\
       the (LENGTH frame + 1) n = LENGTH frame + 1 /\
       stack_rel_aux k len xs stack
        | (_10,_11) -> F`;;

let sorted_env_def = cake_define
  `sorted_env (StackFrame n l0 l _12) = SORTED (\x y. FST x > FST y)
  l`;;

let stack_rel_def = cake_define
  `word_to_stackProof_stack_rel k s_handler s_stack t_handler
  t_rest_of_stack t_stack_length t_bitmaps lens <=>
     EVERY sorted_env s_stack /\
     (?stack.
       abs_stack t_bitmaps s_stack t_rest_of_stack lens = SOME stack
         /\
       (
       s_handler < LENGTH s_stack /\
       is_handler_frame (EL (LENGTH s_stack - (s_handler + 1))
         s_stack) ==>
       t_handler = SOME (wordLang_Word (n2w (t_stack_length -
         handler_val (LASTN (s_handler + 1) stack))))) /\
       stack_rel_aux k t_stack_length s_stack stack)`;;

(*f is the size of the current frame + 1 most of the time
  (extra word for the bitmap pointer)
  f' is the size of the current frame
  lens tracks the size of each remaining stack frame on the stackLang
    stack
*)

(* Stack size as predicted by the wordLang state is a conservative
   estimate of the
   actual stack usage. *)
let stack_size_rel_def = cake_define
  `stack_size_rel f s_locals_size s_stack_limit s_stack_max s_stack
     t_stack t_stack_space (extra:num) <=>
     (~(f = 0) ==> the f s_locals_size = f) /\
     s_stack_limit = LENGTH t_stack /\
     (!sm. s_stack_max = SOME sm ==>
       LENGTH t_stack - t_stack_space - f - extra <= sm /\
       IS_SOME s_locals_size /\
       (?ss. stack_size s_stack = SOME ss /\
         ss = LENGTH t_stack - t_stack_space - f - extra))`;;

let state_rel_def = cake_define
  `word_to_stackProof_state_rel ac k f f'
  (s:('a,num#'c,'ffi)wordSem_state) (t:('a,'c,'ffi)stackSem_state) lens
  extra <=>
     (?_clock s = ?_clock t) /\ (?_gc_fun s = ?_gc_fun t) /\
       (wordSem_state_permute s = K I) /\
     (?_ffi t = ?_ffi s) /\ stackSem_state_use_stack t /\
       stackSem_state_use_store t /\ stackSem_state_use_alloc t /\
     (?_memory t = ?_memory s) /\ (?_mdomain t = ?_mdomain s) /\ 4 <
       k /\
     (?_sh_mdomain t = ?_sh_mdomain s) /\
     (?_store s = ?_store t \\ Handler) /\ gc_fun_ok (?_gc_fun t) /\
       wordSem_state_termdep s = 0 /\ ?_be
     t = ?_be s /\ ?_ffi t = ?_ffi s /\ Handler IN FDOM (?_store t)
       /\ ?_fp_regs
     t = ?_fp_regs s /\ ?_data_buffer
     t = ?_data_buffer s /\ ?_code_buffer
     t = ?_code_buffer s /\ ?_compile
     s = (\(bm0,cfg) progs.
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
       OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND
         bm,cfg)))
         (?_compile t cfg progs)) /\ ?_compile_oracle
     t = (\n.
       let ((bm0,cfg),progs) = ?_compile_oracle s n in
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
         (cfg,progs,append (FST bm))) /\
     (!n. let ((bm0,cfg),progs) = ?_compile_oracle s n in
         EVERY (post_alloc_conventions k o SND o SND) progs /\
         EVERY (flat_exp_conventions o SND o SND) progs /\
         EVERY ((<>) raise_stub_location o FST) progs /\
         EVERY ((<>) store_consts_stub_location o FST) progs /\
         (n = 0 ==> bm0 = LENGTH (stackSem_state_bitmaps t))) /\
     domain (?_code t) = raise_stub_location INSERT
                       store_consts_stub_location INSERT domain
                         (?_code s) /\
     (!n word_prog arg_count.
        (sptree_lookup n (?_code s) = SOME (arg_count,word_prog)) ==>
        post_alloc_conventions k word_prog /\
        flat_exp_conventions word_prog /\
        (?bs i bs2 i2 f stack_prog.
          word_to_stack_compile_prog ac F word_prog arg_count k
            (bs,i) = (stack_prog,f,(bs2,i2)) /\
          LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH
            (stackSem_state_bitmaps t) /\
          isPREFIX (append bs2) (DROP (i - LENGTH (append bs))
            (stackSem_state_bitmaps t)) /\
          (sptree_lookup n (?_code t) = SOME stack_prog) /\
          the f (sptree_lookup n (wordSem_state_stack_size s)) = f))
            /\
     (sptree_lookup raise_stub_location (?_code t) = SOME (raise_stub
       F k)) /\
     (sptree_lookup store_consts_stub_location (?_code t) = SOME
       (store_consts_stub k)) /\
     good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
     LENGTH (stackSem_state_bitmaps t) + LENGTH (buffer_buffer
       (?_data_buffer s)) + buffer_space_left (?_data_buffer s) + 1 <
       dimword (:'ga) /\
     1 <= LENGTH (stackSem_state_bitmaps t) /\ HD
       (stackSem_state_bitmaps t) = (n2w 4) /\
       stackSem_state_stack_space
     t + f <= LENGTH (?_stack t) /\ LENGTH (?_stack t) < dimword
       (:'a) /\
     (if f' = 0 then f = 0 else (f = f' + 1)) /\
     wf (wordSem_state_locals s) /\
     stack_size_rel f (wordSem_state_locals_size s)
       (wordSem_state_stack_limit s) (wordSem_state_stack_max s)
       (?_stack s) (?_stack
       t) (stackSem_state_stack_space t) (extra:num) /\
     (let stack = DROP (stackSem_state_stack_space t + extra)
       (?_stack t) in
     let current_frame = TAKE f stack in
     let rest_of_stack = DROP f stack in
       word_to_stackProof_stack_rel k (wordSem_state_handler s)
         (?_stack s) (FLOOKUP (?_store t) Handler)
         rest_of_stack (LENGTH (?_stack t)) (stackSem_state_bitmaps
           t) lens /\
       (!n v.
         (sptree_lookup n (wordSem_state_locals s) = SOME v) ==>
         EVEN n /\
         (if n DIV 2 < k then (FLOOKUP (stackSem_state_regs t) (n DIV
           2) = SOME v) else ((\l n. oEL n l) current_frame (f - 1 - (n
           DIV 2 - k)) = SOME v) /\
              n DIV 2 < k + f')))`;;

(* correctness proof *)

(* HOL4 ML code, not ported:
val convs_def = LIST_CONJ
  [wordConvsTheory.post_alloc_conventions_def,
   wordConvsTheory.call_arg_convention_def,
   wordConvsTheory.flat_exp_conventions_def,
   wordLangTheory.every_var_def,
   wordLangTheory.every_var_imm_def,
   wordLangTheory.every_stack_var_def,
   wordLangTheory.every_name_def]
*)

(*
Theorem LENGTH_write_bitmap[local]:
  state_rel ac k f f' (s:('a,'ffi) wordSem$state) t /\ 1 <= f ==>
    (LENGTH ((write_bitmap (names:num_set) k f'):'a word list) + f' = f)
Proof
  fs [state_rel_def,write_bitmap_def,LET_DEF]
  \\ fs [LENGTH_word_list] \\ rpt strip_tac
  \\ `~(dimindex (:'a) <= 1) /\ f <> 0` by decide_tac \\ fs []
  \\ decide_tac
QED
*)

(* HOL4 ML code, not ported:
val MEM_SORT = SORTS_SORT_key_val_compare
  |> SIMP_RULE std_ss [SORTS_DEF]
  |> SPEC_ALL |> CONJUNCT1
  |> MATCH_MP MEM_PERM |> GSYM |> GEN_ALL
*)

(*Might need to extend c as well*)

(*These two are actually implied by s_key_eq*)

let abs_frame_eq_def = cake_define
  `abs_frame_eq p q <=>
   FST p = FST q /\
   FST (SND p) = FST (SND q) /\
   LENGTH (SND (SND p)) = LENGTH (SND (SND q))`;;

(*Prove the inductive bits first...*)


(* HOL4 type abbreviation (expanded in the port):
     result = 'a wordSem$result *)

let compile_result_def = cake_define_list
  [`compile_result (Result w1 w2:word_to_stackProof_result) = Result
  w1`;
   `compile_result (Exception w1 w2:word_to_stackProof_result) =
  Exception w1`;
   `compile_result TimeOut = TimeOut`;
   `compile_result wordSem_NotEnoughSpace = Halt (wordLang_Word (n2w
  1))`;
   `compile_result (FinalFFI f:word_to_stackProof_result) = FinalFFI
  f`;
   `compile_result (Break k:word_to_stackProof_result) = Break k`;
   `compile_result (Continue k:word_to_stackProof_result) = Continue
  k`;
   `compile_result Error = Error`];;

(* HOL4 ML code, not ported:
val stack_evaluate_add_clock_NONE =
  stackPropsTheory.evaluate_add_clock
  |> Q.SPECL [`p`,`s`,`NONE`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL
*)

let push_locals_def = cake_define
  `push_locals l0 l s = ?_stack_fupd (K (StackFrame
  (wordSem_state_locals_size s) l0 l NONE :: ?_stack s))
  (wordSem_state_locals_size_fupd (K (SOME 0))
  (wordSem_state_locals_fupd (K LN) s))`;;

(* Allow prefixes of (frames of) stacks to be directly dropped
  using handler_val
*)
(*
Theorem wRegWrite1_thm3 =
  wRegWrite1_thm2
  |> Q.INST [`t`|-> `set_var v1 v2 t`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm4 =
  wRegWrite1_thm1
  |> Q.INST [`t`|-> `set_var v1 v2 t`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm5 =
  wRegWrite1_thm2
  |> Q.INST [`t`|-> `set_var v1 v2 (set_var v3 v4 t)`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];

Theorem wRegWrite1_thm6 =
  wRegWrite1_thm1
  |> Q.INST [`t`|-> `set_var v1 v2 (set_var v3 v4 t)`]
  |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const];
*)

(* TODO: Delete?

Theorem wRegWrite1_thm2:
   state_rel ac k f f' s t lens ∧
   m < f' + k ∧
   get_var (2 * m) s = SOME w ∧
   mem_store a w s = SOME s' ∧
   (∀n. get_var n t = SOME w ⇒
     evaluate (kont n, t) = (NONE, THE(mem_store a w t)))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' s' t' lens
Proof
  rw[wRegWrite1_def,LET_THM,TWOxDIV2] \\ fs[]
  >- (
    old_drule (GEN_ALL state_rel_get_var_imp)
    \\ ONCE_REWRITE_TAC[MULT_COMM]
    \\ disch_then drule
    \\ simp[GSYM stackSemTheory.get_var_def]
    \\ imp_res_tac state_rel_mem_store
    \\ simp[] )
  \\ rw[stackSemTheory.evaluate_def]
  \\ imp_res_tac state_rel_mem_store
  \\ fs[] \\ rveq \\ fs[]
  \\ fs[stackSemTheory.mem_store_def,wordSemTheory.mem_store_def]
  \\ rveq \\ fs[]
  \\ IF_CASES_TAC >- fs[state_rel_def]
  \\ IF_CASES_TAC >- (fs[state_rel_def] \\ `F` by decide_tac)
  \\ fs[stackSemTheory.get_var_def]
  \\ qpat_abbrev_tac`w = EL _ _`
  \\ qmatch_assum_abbrev_tac`state_rel _ _ _ _ t1 _`
  \\ qmatch_abbrev_tac`state_rel _ _ _ _ t2 _`
  \\ `t1 = t2`
  by (
    unabbrev_all_tac
    \\ simp[stackSemTheory.state_component_equality]
    \\ match_mp_tac (GSYM LUPDATE_SAME)
    \\ fs[state_rel_def]
    \\ Cases_on`f = 0`\\fs[]
    \\ decide_tac )
  \\ fs[]
QED
*)

(*
Theorem wRegWrite1_thm2:
   state_rel ac k f f' s t lens ∧
   mem_store a b s = SOME s' ∧
   m < f' + k ∧
   (∀n. n ≤ k ⇒
      evaluate (kont n, t) =
        (NONE, THE(mem_store a b (if n < k then t else set_var k (EL
          (t.stack_space + (f-1-(m-k))) t.stack) t))))
   ⇒
   ∃t'.
   evaluate (wRegWrite1 kont (2 * m) (k,f,f'), t) = (NONE, t') ∧
   state_rel ac k f f' s' t' lens
Proof
  rw[wRegWrite1_def,LET_THM,TWOxDIV2]
  \\ `s.memory = t.memory ∧ s.mdomain = t.mdomain` by fs[state_rel_def]
  >- (
    first_x_assum(qspec_then`m`mp_tac)
    \\ simp[]
    \\ fs[wordSemTheory.mem_store_def,stackSemTheory.mem_store_def]
    \\ rw[]
    \\ fs[state_rel_def]
    \\ metis_tac[] )
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[wordSemTheory.mem_store_def,stackSemTheory.mem_store_def]
  \\ IF_CASES_TAC >- fs[state_rel_def]
  \\ IF_CASES_TAC >- (fs[state_rel_def] \\ `F` by decide_tac)
  \\ simp[stackSemTheory.get_var_def,Once
    stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ qmatch_goalsub_abbrev_tac`EL n t.stack`
  \\ `n < LENGTH t.stack`
  by (
    fs[state_rel_def]
    \\ simp[Abbr`n`]
    \\ rw[]
    \\ Cases_on`f'=0`\\fs[]
    \\ decide_tac )
  \\ simp[LUPDATE_SAME]
  \\ qpat_abbrev_tac`t'':('a,'b)stackSem$state = _ _`
  \\ `t'' = set_var k (EL n t.stack) (t with memory := (a =+ b)
    t.memory)`
  by (
    simp[Abbr`t''`,stackSemTheory.set_var_def
      ,stackSemTheory.state_component_equality] )
  \\ simp[]
  \\ rveq
  \\ fs[state_rel_def]
  \\ metis_tac[]
QED
*)
(*
Theorem wStackLoad_thm1:
   wReg1 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)wordSem$state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
                  state_rel ac k f f' s' t' lens extra /\
                  LENGTH t'.stack = LENGTH t.stack /\
                  t'.stack_space = t.stack_space) ∧
   (¬(n1 < k) ⇒
    ∃t'. evaluate (kont k,
                   set_var k (EL (t.stack_space + (f+k-(n1+1))) t.stack)
                     t) =
         (NONE, t') ∧
         state_rel ac k f f' s' t' lens extra /\
         LENGTH t'.stack = LENGTH t.stack /\
         t'.stack_space = t.stack_space)
   ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra /\
     LENGTH t'.stack = LENGTH t.stack /\
     t'.stack_space = t.stack_space
Proof
  simp[wReg1_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
(*
Theorem wStackLoad_thm1_weak:
   wReg1 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒
     ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
     state_rel ac k f f' s' t' lens extra) ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont k, set_var k (EL (t.stack_space +
     (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel ac k f f' s' t' lens extra)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra
Proof
  simp[wReg1_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
(*
Theorem wStackLoad_thm2:
   wReg2 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
     state_rel ac k f f' s' t' lens extra /\
     LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space)
       ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont (k+1), set_var (k+1) (EL
     (t.stack_space + (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel ac k f f' s' t' lens extra /\ LENGTH t'.stack = LENGTH
      t.stack /\
    t'.stack_space = t.stack_space)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra /\
     LENGTH t'.stack = LENGTH t.stack /\
     t'.stack_space = t.stack_space
Proof
  simp[wReg2_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
(*
Theorem wStackLoad_thm2_weak:
   wReg2 (2 * n1) (k,f,f') = (l,n2) ∧
   get_var (2*n1) (s:('a,num # 'c,'ffi)state) = SOME x ∧
   state_rel ac k f f' s t lens extra ∧
   (n1 < k ⇒ ∃t'. evaluate (kont n1, t) = (NONE, t') ∧
     state_rel ac k f f' s' t' lens extra) ∧
   (¬(n1 < k) ⇒ ∃t'. evaluate (kont (k+1), set_var (k+1) (EL
     (t.stack_space + (f+k-(n1+1))) t.stack) t) = (NONE, t')
    ∧ state_rel ac k f f' s' t' lens extra)
  ⇒
   ∃t'.
     evaluate (wStackLoad l (kont n2),t) = (NONE,t') ∧
     state_rel ac k f f' s' t' lens extra
Proof
  simp[wReg2_def,TWOxDIV2]
  \\ rw[] \\ rw[wStackLoad_def] \\ fs[]
  \\ rw[stackSemTheory.evaluate_def]
  \\ fs[state_rel_def,LET_THM,get_var_def]>>
  res_tac>>
  fs[TWOxDIV2]>>rfs[]>>
  Cases_on`f'`>>fs[]>>
  DECIDE_TAC
QED
*)
(*
Theorem wStackLoad_thm3 =
 wStackLoad_thm2
 |> Q.INST [`t`|->`set_var v1 v2 t`]
 |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const]
*)
let map_var_def = cake_define_list
  [`map_var f (wordLang_Var num') = Var (f num')`;
   `map_var f (wordLang_Load exp) = Load (map_var f exp)`;
   `map_var f (wordLang_Op wop ls) = wordLang_Op wop (MAP (map_var f)
  ls)`;
   `map_var f (wordLang_Shift sh e1 e2) = Shift sh (map_var f e1)
  (map_var f e2)`;
   `map_var f (wordLang_Const c) = Const c`;
   `map_var f (wordLang_Lookup v) = wordLang_Lookup v`];;
(*
Theorem word_exp_thm1:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   every_var_exp is_phy_var e ∧
   DIV2 (max_var_exp e) < k ∧
   state_rel ac k f f' s t lens extra ⇒
   word_exp t (map_var DIV2 e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
    ,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,get_store_def]
  \\ TRY (
    qmatch_assum_rename_tac`option_CASE (the_words _) _ _ = SOME (Word
      _)`
    \\ qpat_x_assum`_ = SOME (Word _)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ imp_res_tac the_words_EVERY_IS_SOME_Word
    \\ fs[MEM_MAP,PULL_EXISTS] )
  \\ TRY (
    first_x_assum drule
    \\ ntac 2 strip_tac
    \\ last_x_assum drule
    \\ disch_then drule
    \\ impl_tac
    >- (
      qmatch_asmsub_abbrev_tac`MAX_LIST ls`
      \\ qspec_then`ls`mp_tac MAX_LIST_max
      \\ simp[EVERY_MEM,Abbr`ls`,EVERY_MAP]
      \\ disch_then drule
      \\ qspec_then`2`mp_tac DIV_LE_MONOTONE
      \\ simp[]
      \\ fs[DIV2_def]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ decide_tac )
    \\ simp[] )
  \\ TRY(
    first_x_assum old_drule \\ strip_tac
    \\ first_x_assum old_drule \\ simp[] \\ strip_tac
    \\ first_x_assum old_drule \\ simp[]
    \\ impl_tac
    >- (
      qmatch_asmsub_abbrev_tac`MAX_LIST ls`
      \\ qspec_then`ls`mp_tac MAX_LIST_max
      \\ simp[EVERY_MEM,Abbr`ls`,EVERY_MAP]
      \\ disch_then drule
      \\ qspec_then`2`mp_tac DIV_LE_MONOTONE
      \\ simp[]
      \\ fs[DIV2_def]
      \\ ntac 2 strip_tac
      \\ first_x_assum drule
      \\ decide_tac )
    \\ simp[] )
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2,get_var_def]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2] )
  \\ strip_tac
  \\ fs[MAP_MAP_o,o_DEF]
  \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ AP_TERM_TAC
  \\ imp_res_tac the_words_SOME_eq \\ rw[]
  \\ simp[MAP_EQ_f,MAP_MAP_o]
  \\ rw[]
  \\ res_tac \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`MAX_LIST ls`
  \\ qspec_then`ls`mp_tac MAX_LIST_max
  \\ simp[EVERY_MEM,Abbr`ls`,EVERY_MAP]
  \\ disch_then drule
  \\ qspec_then`2`mp_tac DIV_LE_MONOTONE
  \\ simp[]
  \\ fs[DIV2_def]
  \\ ntac 2 strip_tac
  \\ first_x_assum drule
  \\ simp[]
QED

Theorem word_exp_thm2:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp ($= (2 * v)) e ∧
   ¬(v < k) ⇒
   word_exp (set_var k (EL (t.stack_space + (f + k - (v + 1))) t.stack)
     t) (map_var (K k) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
    ,GSYM
    EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def
    ,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >- (
    strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm3:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   v1 < k ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var (k+1) (EL (t.stack_space + (f + k - (v2 + 1))) t.stack) t)
     (map_var (λx. if x = 2*v2 then k+1 else DIV2 x) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
    ,GSYM
    EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def
    ,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >-
    (strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm4:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   v1 < k ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var k (EL (t.stack_space + (f + k - (v2 + 1))) t.stack) t)
     (map_var (λx. if x = 2*v2 then k else DIV2 x) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
    ,GSYM
    EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def
    ,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >-
    (strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm5:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   every_var_exp (λx. x = 2*v1 ∨ x = 2*v2) e ∧
   ¬(v1 < k) ∧ ¬(v2 < k)
   ⇒
   word_exp
     (set_var (k+1) (EL (t.stack_space + (f + k - (v2 + 1))) t.stack)
       (set_var k (EL (t.stack_space + (f + k - (v1 + 1))) t.stack) t))
     (map_var (λx. if x = 2*v1 then k else k+1) e) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
    ,GSYM
    EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def,get_store_def
    ,get_var_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ TRY (
    qmatch_abbrev_tac`hidee`
    \\ qpat_x_assum`_ = SOME _`mp_tac
    \\ rpt ( TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ simp[Abbr`hidee`]
    \\ fs[state_rel_def,LET_THM]
    \\ rfs[DOMSUB_FLOOKUP_THM]
    \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
    \\ fs[DIV2_def,TWOxDIV2]
    \\ first_x_assum drule
    \\ simp[TWOxDIV2]
    \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
    \\ simp[ADD_COMM] )
  >-
    (strip_tac>>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>metis_tac[])
  >>
    qpat_x_assum`A=SOME(Word x)` mp_tac>>TOP_CASE_TAC>>fs[]>>
    disch_then sym_sub_tac>>
    AP_TERM_TAC>>
    imp_res_tac the_words_SOME_eq>>
    simp[MAP_EQ_f,MAP_MAP_o,o_DEF]>>
    rw[]>>
    imp_res_tac the_words_MAP_exists>>
    fs[]>>res_tac>>
    simp[]
QED

Theorem word_exp_thm6:
   ∀s e x. word_exp s e = SOME (Word x) ∧
   state_rel ac k f f' s t lens 0 ∧
   e = Op b [Var (2 * v1); Var (2 * v1)] ∧
   ¬(v1 < k)
   ⇒
   word_exp
     (set_var (k+1) (EL (t.stack_space + (f + k - (v1 + 1))) t.stack)
       (set_var k (EL (t.stack_space + (f + k - (v1 + 1))) t.stack) t))
     (Op b [Var k; Var (k+1)]) = SOME x
Proof
  ho_match_mp_tac word_exp_ind
  \\ simp[word_exp_def,stackSemTheory.word_exp_def]
  \\ rw[wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
    ,GSYM EVEN_MOD2,EVEN_EXISTS,wordLangTheory.max_var_exp_def]
  \\ fs[EVERY_MAP,EVERY_MEM] \\ rw[]
  \\ fs[IS_SOME_EXISTS,stackSemTheory.set_var_def,FLOOKUP_UPDATE]
  \\ fs[wordSemTheory.word_exp_def,the_words_def]
  \\ rpt(qpat_x_assum`_ = SOME _`mp_tac)
  \\ rpt(FULL_CASE_TAC>>fs[])
  \\ fs[state_rel_def,LET_THM]
  \\ rfs[DOMSUB_FLOOKUP_THM]
  \\ rfs[wordSemTheory.mem_load_def,stackSemTheory.mem_load_def]
  \\ fs[DIV2_def,TWOxDIV2,get_var_def]
  \\ first_x_assum drule
  \\ simp[TWOxDIV2]
  \\ simp[LLOOKUP_THM,EL_TAKE,EL_DROP]
  \\ simp[ADD_COMM]
QED
*)

(*The last two are weakened to allow easy irule
*)

(*For calls*)

(*For returning calls*)


(*
Theorem evaluate_wStackLoad_wRegImm2[local]:
  wRegImm2 ri (k,f,f') = (x,r') ∧
  (case ri of Reg r => EVEN r | _ => T) ∧
  get_var_imm ri (s:('a,num # 'c,'ffi)state) = SOME (Word c) ∧
  state_rel ac k f f' s t lens ⇒
  ∃t':('a,'c,'ffi) stackSem$state.
  evaluate(wStackLoad x Skip, t) = (NONE,t') ∧
  t.clock = t'.clock ∧
  get_var_imm r' t' = SOME(Word c) ∧
  (∀r. r ≠ k+1 ⇒ get_var r t' = get_var r t) ∧
  state_rel ac k f f' s t' lens ∧
  LENGTH t'.stack = LENGTH t.stack /\ t'.stack_space = t.stack_space
Proof
  Cases_on`ri`>>rw[wRegImm2_def,LET_THM,wReg2_def,EVEN_EXISTS]>>
  fs[wStackLoad_def,stackSemTheory.evaluate_def,LET_THM
    ,stackSemTheory.get_var_def,stackSemTheory.get_var_imm_def
    ,get_var_imm_def]>>simp[]>-
    (imp_res_tac state_rel_get_var_imp>>
    first_assum match_mp_tac>>
    simp[TWOxDIV2])>>
  IF_CASES_TAC>-fs[state_rel_def]>>
  reverse IF_CASES_TAC>-
    (fs[state_rel_def,LET_THM,get_var_def]>>
    res_tac>>fs[TWOxDIV2]>>rfs[]>>
    Cases_on`f'`>>fs[])>>
  imp_res_tac state_rel_get_var_imp2>>
  fs[]>>
  simp[stackSemTheory.set_var_def,FLOOKUP_UPDATE]>>
  fs[TWOxDIV2]
QED
*)

(*NB this lemma can be slightly simpler with
EL (x + offset) stack' = EL (x) stack'*)

(* HOL4 ML code, not ported:
val evaluate_stack_move_clock = Q.prove(`
  ∀a b c d (t:('a,'c,'ffi)stackSem$state).
  let prog = stack_move a b c d Skip in
  evaluate (prog,t with clock:=clk) =
  (FST (evaluate(prog,t:('a,'c,'ffi)stackSem$state)),
   (SND (evaluate(prog,t)) with clock:=clk))`,
  Induct>>fs[LET_THM,stack_move_def,stackSemTheory.evaluate_def]>>rw[]>>
  TRY(pairarg_tac>>fs[])>>
  simp[]>>
*)
  (*get_var_set_var?*)
(* HOL4 ML code, not ported:
  fs[stackSemTheory.get_var_def,stackSemTheory.set_var_def
    ,FLOOKUP_UPDATE])|>SIMP_RULE arith_ss [LET_THM];
*)

(* Used in backendProof *)

(* HOL4 ML code, not ported:
val goal = ``
   λ(prog:'a wordLang$prog,s:('a,num # 'c,'ffi) wordSem$state).
     ∀k f f' res s1 t bs n bs' n' sprog lens.
     (wordSem$evaluate (prog,s) = (res,s1)) /\ res <> SOME Error /\
     state_rel ac k f f' s t lens 0 /\
     post_alloc_conventions k prog /\
     flat_exp_conventions prog /\
     comp ac F prog (bs,n) (k,f,f') = (sprog, (bs',n')) /\
     LENGTH (append bs) ≤ n ∧ n - LENGTH (append bs) ≤ LENGTH t.bitmaps
       ∧
     isPREFIX (append bs') (DROP (n - LENGTH (append bs)) t.bitmaps) ∧
     get_labels sprog SUBSET loc_check t.code /\
     max_var prog < 2 * f' + 2 * k ==>
     ?ck t1:('a,'c,'ffi) stackSem$state res1.
       (stackSem$evaluate (sprog,t with clock := t.clock + ck) =
         (res1,t1)) /\
       if OPTION_MAP compile_result res <> res1
       then res1 = SOME (Halt (Word 2w)) /\
            t1.ffi.io_events ≼ s1.ffi.io_events /\
            the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit
       else
         case res of
         | NONE => state_rel ac k f f' s1 t1 lens 0
         | SOME (Result _ ys) =>
            state_rel ac k 0 0 s1 t1 lens (LENGTH ys - (k - 1)) /\
            (∀i. i < LENGTH ys ==> (if i + 1 < k then
              (FLOOKUP t1.regs (i+1) = SOME (EL i ys)) else
            (LLOOKUP (DROP t1.stack_space t1.stack) (LENGTH ys - (i +
              1)) = SOME (EL i ys))))
         | SOME (Exception _ y) =>
           ∃l0 l.
           state_rel ac k 0 0 (push_locals l0 l s1) t1 (LASTN
             (s.handler+1) lens) 0 /\
           s1.locals = union (fromAList l) (fromAList l0) ∧
           FLOOKUP t1.regs 1 = SOME y
         | SOME (Break _) => state_rel ac k f f' s1 t1 lens 0
         | SOME (Continue _) => state_rel ac k f f' s1 t1 lens 0
         | SOME _ => s1.ffi = t1.ffi /\ s1.clock = t1.clock``
*)

(* HOL4 ML code, not ported:
val ind_thm = evaluate_ind |> ISPEC goal |> GEN_BETA_RULE;
*)


(* HOL4 ML code, not ported:
Resume comp_correct[Skip]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac `0` \\
  fs[comp_def] \\ rw[] \\
  fs [wordSemTheory.evaluate_def,
                         stackSemTheory.evaluate_def,comp_def] \\ rw []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Alloc]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac `0`
  \\ fs
    [wordSemTheory.evaluate_def,stackSemTheory.evaluate_def,comp_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ `n = 2` by (fs [convs_def]) \\ rveq
  \\ `1 < k` by fs[state_rel_def]
  \\ `get_var 1 t = get_var 2 s`
     by (`EVEN 2` by fs[]  \\
     imp_res_tac state_rel_get_var_imp' \\
     rfs[] \\ fs[])
  \\ Cases_on `cut_envs names s.locals`
  THEN1 fs [wordSemTheory.alloc_def]
  \\ Q.MATCH_ASSUM_RENAME_TAC `cut_envs names s.locals = SOME envs`
  \\ Cases_on`1 ≤ f`
  THEN1 (
    old_drule $ GEN_ALL evaluate_wLive
    \\ rpt $ (disch_then (drule_at Any))
    \\ impl_keep_tac
    THEN1 (
      fs[convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2]>>
      fs[GSYM toAList_domain,EVERY_MEM]>>
      fs[X_LE_DIV,reg_allocTheory.is_phy_var_def,LET_THM]>>
      rw[]>>res_tac>>DECIDE_TAC)
    \\ REPEAT STRIP_TAC \\ fs []
    \\ rw[]
    \\ fs [stackSemTheory.evaluate_def,LET_THM]
    \\ `t5.use_alloc` by fs [state_rel_def] \\ fs [convs_def]
    \\ Cases_on `alloc c t5` \\ fs []
    \\ rename1 `alloc c t5 = (res1,t1)` \\ fs []
    \\ drule_all alloc_IMP_alloc
    \\ simp[PULL_EXISTS]
    \\ rpt GEN_TAC \\ Cases_on `res = NONE` \\ fs[]) >>
  `f=0` by DECIDE_TAC>>
  `f' = 0` by fs[state_rel_def]>>
  `t.use_alloc` by fs[state_rel_def] >>
  fs[wLive_def]>>rveq>>fs[stackSemTheory.evaluate_def,LET_THM]>>
  fs[cut_env_def]>>
  `domain (FST names) = {}` by (
    CCONTR_TAC>>fs[convs_def,wordLangTheory.max_var_def]>>
    `∃x. x ∈ domain (FST names)` by fs[MEMBER_NOT_EMPTY]>>
    fs[GSYM toAList_domain]>>
    drule MAX_LIST_PROPERTY >>
    fs[EVERY_MEM] >> res_tac >>
    DECIDE_TAC) >>
  `domain (SND names) = {}` by (
    CCONTR_TAC>>fs[convs_def,wordLangTheory.max_var_def]>>
    `∃x. x ∈ domain (SND names)` by fs[MEMBER_NOT_EMPTY]>>
    fs[GSYM toAList_domain]>>
    drule MAX_LIST_PROPERTY >>
    fs[EVERY_MEM] >> res_tac >>
    DECIDE_TAC) >>
  drule_all alloc_IMP_alloc2>>
  fs[PULL_EXISTS]>>
  Cases_on`res=NONE`>>fs[]
QED
*)

(* ?
Theorem insert_bitmap_append:
  ∀bs xs new_bs i.
    insert_bitmap xs (bs,n) = ((new_bs,n'),i) ⇒
    ∃ys zs. new_bs = ys ++ xs ++ zs ∧ i = LENGTH ys
Proof
  Induct \\ rw [insert_bitmap_def]
  \\ TRY (qexists_tac ‘[]’ \\ fs [IS_PREFIX_APPEND] \\ NO_TAC)
  \\ pairarg_tac \\ gvs []
  \\ res_tac \\ gvs []
  \\ qexists_tac ‘h::ys'’ \\ fs []
QED *)

(* HOL4 ML code, not ported:
Resume comp_correct[StoreConsts]:
  gvs [wordSemTheory.evaluate_def,AllCaseEqs(),PULL_EXISTS]
  \\ rpt strip_tac \\ gvs [comp_def]
  \\ pairarg_tac \\ gvs []
  \\ qexists_tac ‘0’
  \\ ‘t.use_store ∧ t.use_alloc ∧ good_dimindex (:'a)’ by fs
    [state_rel_def]
  \\ gvs
    [stackSemTheory.evaluate_def,stackSemTheory.inst_def
    ,stackSemTheory.assign_def,
          stackSemTheory.word_exp_def,post_alloc_conventions_def
            ,call_arg_convention_def]
  \\ IF_CASES_TAC
  THEN1
   (qsuff_tac ‘F’ \\ fs []
    \\ fs [check_store_consts_opt_def]
    \\ gvs [state_rel_def,store_consts_stub_def])
  \\ gvs [store_const_sem_def]
  \\ IF_CASES_TAC THEN1 fs [state_rel_def] \\ fs []
  \\ fs
    [stackSemTheory.get_var_def,stackSemTheory.set_var_def,lookup_insert
    ,
         FLOOKUP_UPDATE]
  \\ ‘FLOOKUP t.regs 2 = SOME (Word a) ∧ FLOOKUP t.regs 3 = SOME (Word
    off)’ by
    (fs [state_rel_def,get_var_def] \\ res_tac \\ ‘3 < k’ by fs [] \\ fs
      [])
  \\ fs [stackSemTheory.unset_var_def]
  \\ ‘LENGTH t.bitmaps < dimword (:α)’ by fs [state_rel_def]
  \\ ‘∃xs ys. t.bitmaps = xs ++ const_words_to_bitmap words (LENGTH
    words) ++ ys ∧
              LENGTH xs = i’ by (
    fs[insert_bitmap_def]>>rw[]>>
    fs[append_thm]>>
    old_drule isPREFIX_DROP>>
    disch_then(qspec_then`LENGTH(append bs)` mp_tac)>>
    simp[DROP_APPEND,DROP_LENGTH_NIL]>>
    DEP_REWRITE_TAC[DROP_DROP]>> simp[]>>
    old_drule IS_PREFIX_LENGTH>> simp[]>>
    strip_tac>>
    gvs [IS_PREFIX_APPEND]>>
    strip_tac>>
    qexists_tac`TAKE i t.bitmaps`>>qexists_tac`l'`>>simp[]>>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC]>> pop_assum sym_sub_tac>>
    simp[])
  \\ gvs []
  \\ ‘s.mdomain = t.mdomain’ by fs [state_rel_def]
  \\ old_drule (GEN_ALL copy_words_correct)
  \\ fs [] \\ disch_then kall_tac
  \\ fs [state_rel_def,set_var_def,unset_var_def,lookup_insert]
  \\ rpt strip_tac
  \\ TRY (res_tac \\ NO_TAC)
  \\ rpt (irule wf_insert)
  \\ rpt (irule wf_delete)
  \\ fs []\\ gvs [AllCaseEqs(),lookup_delete]
  \\ gvs [DOMSUB_FLOOKUP_THM,FLOOKUP_UPDATE]
  \\ fs [DIV_LT_X]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ fs [DIV_EQ_X]
  \\ res_tac
  \\ rename1`nn < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rename1`nn + 2 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn + 2 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rename1`nn + 4 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs []
  \\ rename1`SUC nn + 4 < 2 * k`
  \\ Cases_on ‘nn’ \\ fs [ADD1]
  \\ rw [] \\ fs []
QED
*)

(* ?
Theorem insert_bitmap_append:
  ∀bs xs new_bs i.
    insert_bitmap xs (bs,n) = ((new_bs,n'),i) ⇒
    ∃ys zs. new_bs = ys ++ xs ++ zs ∧ i = LENGTH ys
Proof
  Induct \\ rw [insert_bitmap_def]
  \\ TRY (qexists_tac ‘[]’ \\ fs [IS_PREFIX_APPEND] \\ NO_TAC)
  \\ pairarg_tac \\ gvs []
  \\ res_tac \\ gvs []
  \\ qexists_tac ‘h::ys'’ \\ fs []
QED *)

(* HOL4 ML code, not ported:
Resume comp_correct[Inst]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[comp_def,wordSemTheory.evaluate_def]
  \\ last_x_assum mp_tac
  \\ TOP_CASE_TAC \\ fs[]
  \\ strip_tac \\ rveq
  \\ qexists_tac`0` \\ simp[]
  \\ fs[convs_def,wordLangTheory.max_var_def]
  \\ old_drule evaluate_wInst \\ simp[]
  \\ disch_then drule
  \\ strip_tac \\ simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Assign]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[flat_exp_conventions_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Get]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[flat_exp_conventions_def]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def,get_store_def]
  \\ last_x_assum mp_tac
  \\ TOP_CASE_TAC \\ simp[]
  \\ strip_tac \\ rveq \\ simp[]
  \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM
    EVEN_MOD2,EVEN_EXISTS]
  \\ rw[]
  \\ qexists_tac`0` \\ simp[]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`NONE` \\ simp[]
  \\ qmatch_goalsub_abbrev_tac `wRegWrite1 kont (2 * m)`
  \\ qmatch_goalsub_abbrev_tac `state_rel _ _ _ _ (set_var _ v _)`
  \\ drule_then(qspecl_then [`v`,`m`,`kont`] mp_tac) (GEN_ALL
    wRegWrite1_thm1)
  \\ unabbrev_all_tac
  \\ simp[stackSemTheory.evaluate_def]
  \\ fs[wordLangTheory.max_var_def,GSYM LEFT_ADD_DISTRIB]
  \\ impl_tac >- (fs[state_rel_def] \\ rfs[DOMSUB_FLOOKUP_THM])
  \\ metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Set]:
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ Cases_on`exp`>>fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
       ,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ fs[wordSemTheory.word_exp_def]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[stackSemTheory.evaluate_def]
  \\ `t'.use_store` by fs[state_rel_def]
  \\ fs[]
  \\ irule state_rel_set_store \\ fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[OpCurrHeap]:
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
       ,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def
    ,the_words_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[evaluate_wRegWrite1_seq]
  \\ pairarg_tac \\ fs[]
  \\ `t'.use_store` by fs[state_rel_def]
  \\ simp[stackSemTheory.evaluate_def,stackSemTheory.word_exp_def]
*)
  (*TODO remove by changing word_exp_def*)
(* HOL4 ML code, not ported:
  \\ fs[GSYM stackSemTheory.get_var_def]
*)
  (*TODO remove by changing get_store_def*)
(* HOL4 ML code, not ported:
  \\ fs[wordSemTheory.get_store_def]
  \\ ‘FLOOKUP t'.store CurrHeap = FLOOKUP s.store CurrHeap’ by
    fs [state_rel_def,DOMSUB_FLOOKUP_THM] \\ fs []
  \\ old_drule (GEN_ALL evaluate_wStackStore_wReg1)
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then `Word z` strip_assume_tac)
  \\ simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Store]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[flat_exp_conventions_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Tick]:
  REPEAT STRIP_TAC \\
  fs [comp_def] \\ rw[] \\
  fs[get_labels_def] \\
  qexists_tac `0` \\ fs
    [wordSemTheory.evaluate_def,stackSemTheory.evaluate_def,comp_def]
  \\ rw []
  \\ simp[wordSemTheory.evaluate_def,stackSemTheory.evaluate_def
    ,comp_def]
  \\ `s.clock = t.clock` by fs [state_rel_def] \\ fs [] \\ rw []
  \\ fs
    [state_rel_def,wordSemTheory.dec_clock_def
    ,stackSemTheory.dec_clock_def]
  \\ metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[MustTerminate]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,LET_DEF,
      stackSemTheory.evaluate_def,comp_def]
  \\ Cases_on `s.termdep = 0` \\ fs [state_rel_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Seq]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,LET_DEF,
        stackSemTheory.evaluate_def,comp_def]
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs []
  \\ pairarg_tac \\ fs [get_labels_def]
  \\ `max_var c1 < 2 * f' + 2 * k /\ max_var c2 < 2 * f' + 2 * k` by
    (fs [wordLangTheory.max_var_def] \\ decide_tac)
  \\ `post_alloc_conventions k c1 /\
      post_alloc_conventions k c2 /\
      flat_exp_conventions c1 /\
      flat_exp_conventions c2` by fs [convs_def]
  \\ imp_res_tac comp_IMP_isPREFIX
  \\ imp_res_tac comp_IMP_LENGTH
  \\ rfs[]
  \\ reverse (Cases_on `res' = NONE`) \\ fs [] \\ rpt var_eq_tac
  THEN1 (
    first_x_assum old_drule \\ fs []
    \\ Cases_on`bs''`
    \\ disch_then old_drule \\ fs []
    \\ impl_tac >- (
      fs[get_labels_def]>>
      metis_tac[IS_PREFIX_TRANS] )
    \\ strip_tac
    \\ qexists_tac `ck` \\ fs [] \\ Cases_on `res` \\ fs []
    \\ Cases_on `res1 = NONE`
    \\ fs [stackSemTheory.evaluate_def,LET_THM])
  \\ first_x_assum old_drule \\ fs []
  \\ Cases_on`bs''`
  \\ disch_then old_drule \\ fs []
  \\ impl_tac >- (
    fs[get_labels_def]>>
    metis_tac[IS_PREFIX_TRANS] )
  \\ strip_tac
  \\ reverse (Cases_on `res1 = NONE`) \\ fs []
  >- (
    qexists_tac `ck`
    \\ last_x_assum kall_tac
    \\ `good_dimindex (:'a)` by fs [state_rel_def]
    \\ fs [Halt_EQ_compile_result,stackSemTheory.evaluate_def,LET_THM]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
    \\ `s.ffi = t.ffi` by fs [state_rel_def]
    \\ imp_res_tac evaluate_io_events_mono \\ fs []
    \\ imp_res_tac wordPropsTheory.evaluate_io_events_mono \\ fs []
    \\ rfs [] \\ fs [] \\ metis_tac
      [IS_PREFIX_TRANS,evaluate_stack_limit_stack_max])
  \\ first_x_assum old_drule \\ fs []
  \\ disch_then drule
  \\ impl_tac >- (
    fs[]>>imp_res_tac evaluate_mono>>fs[]>> rw[]
    >- (old_drule IS_PREFIX_LENGTH>>fs[])
    >- metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]
    >>
      fs[get_labels_def]>>
      metis_tac[SUBSET_TRANS,loc_check_SUBSET])
  \\ rw [] \\ fs []
  \\ fs [stackSemTheory.evaluate_def,LET_THM]
  \\ imp_res_tac stack_evaluate_add_clock_NONE \\ fs []
  \\ pop_assum (qspec_then `ck'` assume_tac)
  \\ qexists_tac `ck+ck'` \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ `s.handler = s1'.handler` by
    (Q.ISPECL_THEN [`c1`,`s`] assume_tac evaluate_stack_swap>>rfs[])
  \\ fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Return]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac `0` \\
  gvs[wordSemTheory.evaluate_def,AllCaseEqs()] \\
  gvs[comp_def,UNCURRY_EQ] \\
  `EVEN n` by (fs[convs_def,reg_allocTheory.is_phy_var_def,EVEN_MOD2])
    \\
  simp[evaluate_wStackLoad_seq] \\
  dxrule_all evaluate_wStackLoad_wReg1 \\
  rw[] \\
  simp[Once stackSemTheory.evaluate_def] \\
  DEP_REWRITE_TAC[evaluate_SeqStackFree] \\
  CONJ_ASM1_TAC >- (fs [state_rel_def] \\ decide_tac) \\
  fs [stackSemTheory.evaluate_def] \\
  `(t.stack_space + skip_free (k,f,f') ms) <= LENGTH t.stack`
      by fs[state_rel_def,skip_free_def] \\
  fs[] \\
  CONJ_TAC >- (
      fs[state_rel_def,flush_state_def] \\
      CONJ_TAC >- METIS_TAC[] \\
      CONJ_TAC >- (
        fs[stack_size_rel_def]>>rw[]
        >- (
          gvs[skip_free_def,num_stack_ret_def]>>
          imp_res_tac get_vars_length_lemma >>
          simp[])
        >- (
          PURE_REWRITE_TAC[skip_free_def,num_stack_ret_def]>>
          imp_res_tac get_vars_length_lemma >>
          fs[wordLangTheory.max_var_def,GSYM MAX_DEF] >>
          fs[convs_def] >>
          qpat_x_assum `ms = _` SUBST_ALL_TAC >>
          fs[MAX_LIST_GENLIST_evens2] >>
          fs[GSYM LEFT_ADD_DISTRIB] >>
          gvs[IS_SOME_EXISTS,the_eqn] >>
          Cases_on `f' = 0` >> fs[])) >>
      CONJ_TAC >- (
        simp[skip_free_def,num_stack_ret_def]>>
        imp_res_tac get_vars_length_lemma >>
        simp[] >>
        `f = (f - (LENGTH ms + 1 - k) + (LENGTH ms + 1 - k))`
          suffices_by fs[DROP_DROP_EQ] >>
        fs[wordLangTheory.max_var_def,GSYM MAX_DEF] >>
        fs[convs_def] >>
        qpat_x_assum `ms = _` SUBST_ALL_TAC >>
        fs[MAX_LIST_GENLIST_evens2] >>
        fs[GSYM LEFT_ADD_DISTRIB] >>
        gvs[IS_SOME_EXISTS,the_eqn] >>
        Cases_on `f' = 0` >> fs[]) >>
      simp[lookup_def]) \\
  rpt strip_tac \\
  `get_var (EL i ms) s = SOME (EL i ys)`
    by(
       qpat_x_assum `get_vars _ _ = _` mp_tac \\
       qpat_x_assum `i < LENGTH ys` mp_tac \\
       rpt (pop_assum kall_tac) \\
       map_every qid_spec_tac [`i`,`ys`,`ms`] \\
       Induct_on `i` \\ fs[] \\ rw[]
       >- (Cases_on `ms` >> gvs[get_vars_def,AllCaseEqs()])
       >- (Cases_on `ys` >> fs[] >>
           Cases_on `ms` >> gvs[get_vars_def,AllCaseEqs()])
           ) \\
  `EL i ms = 2 * ((i + 1))`
     by(
       imp_res_tac get_vars_length_lemma \\
       fs[convs_def] \\
       qpat_assum `ms = _` (ONCE_REWRITE_TAC o single) \\
       DEP_REWRITE_TAC[EL_GENLIST] \\ fs[]) \\
  pop_assum SUBST_ALL_TAC \\
  pop_assum (assume_tac o SRULE[get_var_def]) \\
  fs[state_rel_def] \\
  first_x_assum old_drule \\
  simp[EVEN_DOUBLE] \\
  IF_CASES_TAC >- simp[] >>
  strip_tac >> simp[] \\
  imp_res_tac LLOOKUP_TAKE_IMP \\
  fs[LLOOKUP_DROP,skip_free_def,num_stack_ret_def] \\
  gvs[] \\
  imp_res_tac get_vars_length_lemma \\
  fs[] \\
  `f' + k > LENGTH ms`
     by(
        fs[convs_def,wordLangTheory.max_var_def
          ,reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS] \\
        rveq \\ fs[] \\
        qpat_x_assum `ms = GENLIST _ _` SUBST_ALL_TAC \\
        fs[MAX_LIST_GENLIST_evens2]) \\
      fs[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Raise]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,jump_exc_def]
  \\ `1 < k` by (fs [state_rel_def] \\ decide_tac)
  \\ qpat_x_assum `xxx = (aa,bb)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
  \\ qpat_x_assum `_ = (_,s1)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
  \\ pop_assum mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw []
  \\ qexists_tac `1`
  \\ rename1 `LASTN (s.handler + 1) s.stack =
        StackFrame o' ll0 ll (SOME (h1,l3,l4))::rest`
  \\ fs[comp_def] \\ rw[]
  \\ fs [wordSemTheory.evaluate_def,LET_DEF,
      stackSemTheory.evaluate_def,jump_exc_def,
      stackSemTheory.find_code_def]
  \\ `lookup raise_stub_location t.code = SOME (raise_stub F k)` by fs
    [state_rel_def]
  \\ fs []
  \\ pop_assum kall_tac
  \\ fs
    [stackSemTheory.dec_clock_def,raise_stub_F
    ,wordLangTheory.max_var_def]
  \\ fs
    [state_rel_def,LET_DEF,stackSemTheory.evaluate_def,LET_THM
    ,stack_size_rel_iff]
  \\ fs [DROP_DROP_EQ] \\ fs [stack_rel_def]
  \\ qpat_x_assum` A ⇒ B` mp_tac
  \\ impl_tac >- (
    `s.handler+1 ≤ LENGTH s.stack` by DECIDE_TAC>>
    imp_res_tac LASTN_HD>>
    ntac 3 (pop_assum sym_sub_tac)>>
    fs[is_handler_frame_def])
  \\ strip_tac
  \\ fs[LET_DEF,get_var_set_var]
  \\ fs [stackSemTheory.set_var_def]
  \\ `(LENGTH t.stack - handler_val (LASTN (s.handler+1) stack)) <
    dimword (:'a)`
       by decide_tac \\ fs []
  \\ `SORTED (\x y. FST x > FST y) ll` by
    (imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [sorted_env_def])
  \\ `LENGTH t.stack - handler_val (LASTN (s.handler+1) stack) + 3 <=
    LENGTH t.stack` by
       (imp_res_tac stack_rel_raise \\ rfs[]
        \\ PairCases_on`payload`\\simp[handler_val_def])
  \\ IF_CASES_TAC \\ fs []
  \\ fs
    [stackSemTheory.get_var_def,FLOOKUP_UPDATE
    ,stackSemTheory.set_store_def]
  \\ fs
    [stackSemTheory.get_var_def,FLOOKUP_UPDATE,push_locals_def
    ,lookup_def]
  \\ drule_at (Pos (el 5)) stack_rel_raise
  \\ rpt (disch_then (drule_at Any))
  \\ simp[]
  \\ strip_tac
  \\ fsrw_tac[][]
  \\ qexists_tac`ll0`
  \\ qexists_tac`(FST (env_to_list (fromAList ll) (K I)))`
  \\ simp[GSYM CONJ_ASSOC]
  \\ conj_tac THEN1 metis_tac[]
  \\ conj_tac >- (
     imp_res_tac stack_rel_aux_stack_size >>
     rw[the_eqn] >> PURE_TOP_CASE_TAC >> rw[handler_val_def] >>
     qpat_x_assum `IS_SOME _ ==> IS_SOME (stack_size _)` assume_tac >>
     fsrw_tac[][IS_SOME_EXISTS,miscTheory.the_def] >>
     drule_then old_drule LASTN_stack_size_SOME >>
     impl_tac >- simp[] >>
     strip_tac >>
     fs[stack_size_eq2] >>
     Cases_on `payload` >> fs[handler_val_def,stack_size_frame_def] >>
     rveq >> fs[miscTheory.the_def]
   )
  \\ conj_tac THEN1 (
       strip_tac >> last_x_assum old_drule >> simp[IS_SOME_EXISTS] >>
       strip_tac >>
       drule_then old_drule LASTN_stack_size_SOME >>
       impl_tac >- simp[] >>
       rw[stack_size_eq2,stack_size_frame_def]
     )
  \\ conj_tac THEN1 (
       rw [handler_val_def]>>
       imp_res_tac stack_rel_aux_stack_size >>
       rw[the_eqn] >>
       PURE_TOP_CASE_TAC >> rw[handler_val_def] >>
       Cases_on `payload` >>
       fsrw_tac[][miscTheory.the_def,handler_val_def,stack_size_eq] >>
       `LENGTH t.stack -
        (LENGTH r + (handler_val (LASTN s.handler stack) + 4)) <=
        LENGTH t.stack` by intLib.COOPER_TAC >>
       simp[SUB_RIGHT_ADD] >>
       reverse IF_CASES_TAC
       >- intLib.COOPER_TAC >>
       imp_res_tac abs_stack_LENGTH >>
       qpat_x_assum `handler_val (_::_) = LENGTH (DROP _ _)` (mp_tac o
         GSYM) >>
       simp[handler_val_def,LENGTH_DROP]
     )
  \\ conj_tac THEN1 (
    fs [sorted_env_def]
    \\ Cases_on `env_to_list (fromAList ll) (K I)`
    \\ imp_res_tac env_to_list_K_I_IMP \\ fs [])
  \\ conj_tac >- (
     rpt (qpat_x_assum`∀x. _`kall_tac)
     \\imp_res_tac LASTN_LENGTH_BOUNDS
     \\imp_res_tac abs_stack_IMP_LENGTH \\ fs[]
     \\imp_res_tac EVERY_IMP_EVERY_LASTN \\ fs [])
  \\ `FST (env_to_list (fromAList ll) (K I)) = ll` by (
    Cases_on `env_to_list (fromAList ll) (K I)` \\ fs []
    \\ imp_res_tac env_to_list_K_I_IMP \\ rw []
    \\ metis_tac [SORTED_FST_PERM_IMP_ALIST_EQ])
  \\ pop_assum (SUBST_ALL_TAC) \\ simp[]
  \\ reverse CONJ_TAC>- (
    fs [get_var_def,FLOOKUP_UPDATE,convs_def,lookup_def]>>
    `1 < k` by fs[state_rel_def]>>
    res_tac>>qpat_x_assum`!n.P` kall_tac>>rfs[])
  \\ rfs[FLOOKUP_SIMP,handler_val_def]
  \\ rw[]
  \\ Cases_on`h1+1 = SUC (LENGTH rest)`>- (
      fs[is_handler_frame_def])>>
  `h1 < LENGTH rest ∧ SUC(LENGTH rest) - (h1+1) = SUC(LENGTH rest -
    (h1+1))` by DECIDE_TAC>>
  fs[]
  \\ sg `h1 <= LENGTH (LASTN (s.handler+1) stack)`
  \\ fs [LASTN_CONS]
  \\ imp_res_tac abs_stack_IMP_LENGTH \\ fs[] >>
  simp[LASTN_CONS,FLOOKUP_UPDATE]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[If]:
  rw[] >> fs[comp_def]>>
  rpt(pairarg_tac>>gvs[])>>
  rename1`_ = (q1,bss)`>>
  Cases_on`bss`>>
  qpat_x_assum`evaluate _ =_` mp_tac >>
  simp[evaluate_def, CaseEq "option", CaseEq"word_loc"]>>rw[]>>
*)
  (* prevent splitting *)
(* HOL4 ML code, not ported:
  qmatch_asmsub_abbrev_tac`ifcase = (res,s1)`>>
  `EVEN r1 ∧ (case ri of Reg r => EVEN r | _ => T)` by (
    Cases_on`ri`>>
    fs[convs_def,EVEN_MOD2,reg_allocTheory.is_phy_var_def]
  )>>
  gvs[AllCaseEqs(),UNCURRY_EQ] >>
  gvs[wordSemTheory.get_var_imm_def]
  >~ [`If _ _ (Reg _) _ _`]
  >- ( (* Reg case *)
    fs[get_labels_wStackLoad,get_labels_def]>>
    simp[wStackLoad_append]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg1>>
    strip_tac >>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg2>>
    strip_tac >>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.evaluate_def,evaluate_wStackLoad_clock] >>
    simp[stackSemTheory.get_var_imm_def]>>
    gvs[markerTheory.Abbrev_def,convs_def,wordLangTheory.max_var_def] >>
    `!a b c. max3 a b c = MAX a (MAX b c)`
       by simp[max3_def,MAX_DEF] >>
    fs[]
    >- (
      last_x_assum (old_drule )>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET])>>
      rw[])
    >- (
      last_x_assum (drule)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET]
                  )>>
      rw[]))
  >~[`If _ _ (Imm _) _ _`]
  >- (
    fs[get_labels_wStackLoad,get_labels_def]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg1>>
    rw[]>>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.evaluate_def,evaluate_wStackLoad_clock
      ,stackSemTheory.get_var_imm_def]>>
    gvs[markerTheory.Abbrev_def,convs_def,wordLangTheory.max_var_def] >>
    `!a b c. max3 a b c = MAX a (MAX b c)`
       by simp[max3_def,MAX_DEF] >>
    fs[]
    >- (
      last_x_assum (old_drule )>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET])>>
      rw[])
    >- (
      last_x_assum (drule)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET]
                  )>>
      rw[])
     )
  >- (
    fs[get_labels_wStackLoad,get_labels_def]>>
    dxrule_all evaluate_const_inst>>
    disch_then (qspec_then `i` mp_tac) >>
    rw[] >>
    simp[Once stackSemTheory.evaluate_def,evaluate_const_inst_clock]>>
    simp[evaluate_wStackLoad_seq]>>
    dxrule_all evaluate_wStackLoad_wReg1 >>
    rw[]>>
    simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]>>
    simp[stackSemTheory.get_var_imm_def] >>
    gvs[markerTheory.Abbrev_def,convs_def,wordLangTheory.max_var_def] >>
    `!a b c. max3 a b c = MAX a (MAX b c)`
       by simp[max3_def,MAX_DEF] >>
    fs[]
    >- (
      last_x_assum (drule)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac IS_PREFIX_LENGTH>>fs[])
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET])>>
      rw[])
    >- (
      last_x_assum (drule_at Any)>>
      rpt(disch_then (drule_at Any))>>
      impl_tac>- (
        imp_res_tac comp_IMP_isPREFIX>>
        imp_res_tac comp_IMP_LENGTH>>rfs[]>>
        imp_res_tac evaluate_mono>>fs[]>>rw[]
        >- (imp_res_tac IS_PREFIX_LENGTH>>fs[])
        >- (imp_res_tac comp_IMP_isPREFIX>> fs[]>>
          metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
        >>
          metis_tac[SUBSET_TRANS,loc_check_SUBSET]
                  )>>
      rw[])
     )
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[LocValue]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs[comp_def,wordSemTheory.evaluate_def]
  \\ fs[convs_def,reg_allocTheory.is_phy_var_def,GSYM
    EVEN_MOD2,EVEN_EXISTS]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ qexists_tac`0` \\ simp[]
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`NONE` \\ simp[]
  \\ match_mp_tac wRegWrite1_thm1_weak
  \\ simp[stackSemTheory.evaluate_def]
  \\ fs[wordLangTheory.max_var_def,GSYM LEFT_ADD_DISTRIB]
  \\ imp_res_tac state_rel_code_domain
  \\ fs[SUBSET_DEF]
  \\ Cases_on `loc_check t.code (l1,0)` \\ fs []
  \\ fs [wRegWrite1_def]
  \\ sg `F` \\ fs [] \\ pop_assum mp_tac \\ fs [IN_DEF]
  \\ fs [loc_check_def,IN_DEF]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Install]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  qexists_tac`0` \\
  fs[comp_def,wordSemTheory.evaluate_def]
  \\ gvs[convs_def,case_eq_thms,UNCURRY_EQ]
  \\ fs[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2]
  \\ simp[wStackLoad_append]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac \\ simp[Once stackSemTheory.evaluate_def]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg2
  \\ strip_tac \\ simp[Once stackSemTheory.evaluate_def]
  \\ imp_res_tac state_rel_get_var_imp' \\ fs[]
  \\ (rpt (pop_assum (fn x => (if is_forall (concl x) then kall_tac x
    else NO_TAC))))
  \\ `4 < k` by fs[state_rel_def]
  \\ fs[]
  \\ `t''.code_buffer = s.code_buffer /\
     t''.data_buffer = s.data_buffer /\
     t''.use_stack` by fs[state_rel_def]
  \\ full_simp_tac(srw_ss())[stackSemTheory.evaluate_def]
  \\ qhdtm_assum`state_rel`(fn th =>
       let val conjs = th |> REWRITE_RULE[state_rel_def] |> CONJUNCTS
           val conjs =(filter ((fn tm => is_eq tm andalso is_pabs(rhs
             tm)) o concl) conjs)
       in
           map_every assume_tac conjs
       end)
  \\ full_simp_tac(srw_ss())[]
  \\ rename1 `(cfg,(k',prog)::progs)`
  \\ LET_ELIM_TAC
  \\ fs[EXISTS_PULL_FORALL1,EXISTS_PULL_FORALL2,EXISTS_PULL_FORALL3]
  \\ rpt strip_tac
  \\ `? prog' progs'. progs'' = (k',prog')::progs'`
      by (Cases_on `prog`
      \\ fs[compile_word_to_stack_def]
      \\ rpt (pairarg_tac \\ gvs[]))
  \\ fs[]
  \\ fs[CONV_RULE (LHS_CONV SYM_CONV) UNCURRY_EQ]
  \\ gvs[Abbr`new_oracle`]
  \\ fs[shift_seq_def]
  \\ Cases_on `s.compile_oracle 1` >> gvs[]
  \\ pairarg_tac \\ fs[]
  \\ qpat_x_assum`compile_word_to_stack ac F k r _ = _`kall_tac
  \\ qmatch_assum_rename_tac`compile_word_to_stack ac F k ps (_,_) =
    (ps',_)`
  \\ fs[state_rel_def]
  \\ CONJ_TAC
  >- (
    qx_gen_tac`z`
    \\ last_x_assum(qspec_then`0`kall_tac)
    \\ last_assum(qspec_then`0`mp_tac)
    \\ last_x_assum(qspec_then`z+1`mp_tac)
    \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ rw[] \\ gvs[]
    \\ Cases_on `bm`
    \\ old_drule (GEN_ALL compile_word_to_stack_IMP_LENGTH)
    \\ fs[])
  \\ conj_tac
  >- (
    simp[domain_union,domain_fromAList]
    \\ imp_res_tac MAP_FST_compile_word_to_stack
    \\ rw[INSERT_UNION_EQ]
    \\ fs[] )
  \\ conj_tac
  >- (
    fs[lookup_union,lookup_fromAList]
    \\ rpt gen_tac
    \\ reverse TOP_CASE_TAC
    >- (
      strip_tac \\ rveq
      \\ last_x_assum drule
      \\ fs[]
      \\ strip_tac \\ fs[]
      \\ asm_exists_tac \\ fs[]
      \\ fs[IS_PREFIX_APPEND]
      \\ fs[lookup_def,the_eqn]
      \\ qexists_tac`l' ++append (FST bm)`
      \\ simp[DROP_APPEND]
      \\ `i - (LENGTH (append bs') + LENGTH t.bitmaps) = 0` by
        fs[]
      \\ simp[])
    \\ strip_tac
    \\ imp_res_tac ALOOKUP_MEM
    \\ last_x_assum(qspec_then`0`kall_tac)
    \\ last_x_assum(qspec_then`0`mp_tac)
    \\ simp[EVERY_MEM]
    \\ strip_tac
    \\ res_tac \\ fs[]
    \\ Cases_on`bm`
    \\ old_drule compile_word_to_stack_IMP_ALOOKUP
    \\ disch_then drule
    \\ fs[]
    \\ disch_then(qspec_then`t.bitmaps ++ append q`mp_tac)
    \\ simp[DROP_APPEND,DROP_LENGTH_NIL]
    \\ strip_tac
    \\ asm_exists_tac \\ simp[]
    \\ CASE_TAC
    \\ fs[EXTENSION,domain_lookup]
    \\ last_x_assum(qspec_then`n'`mp_tac)
    \\ simp[lookup_def,the_eqn]
  )
  \\ conj_tac >- simp[lookup_union]
  \\ conj_tac >- simp[lookup_union]
  \\ conj_tac >- (
    fs[buffer_flush_def]
    \\ rveq \\ fs[] \\rfs[] )
  \\ conj_tac >- ( Cases_on`t.bitmaps` \\ gvs[] )
  \\ conj_tac >- ( Cases_on`t.bitmaps` \\ gvs[] )
  \\ conj_tac >- (
    match_mp_tac wf_insert
    \\ gvs[cut_env_def,case_eq_thms,cut_envs_def,cut_names_def]
    \\ match_mp_tac wf_union
    \\ simp[])
  \\ conj_tac >- ( fs[stack_size_rel_def])
  \\ conj_tac >- (
    fs[stack_rel_def]
    \\ metis_tac[abs_stack_bitmaps_prefix] )
  \\ fs[lookup_insert]
  \\ rpt gen_tac
  \\ gvs[cut_env_def,cut_envs_def,cut_names_def,case_eq_thms
    ,lookup_union,lookup_inter]
  \\ simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
  \\ strip_tac \\ rveq \\ fs[]
  \\ fs[EVERY_MAP,EVERY_MEM,MEM_toAList,FORALL_PROD]
  \\ rpt(first_x_assum drule)
  \\ simp[reg_allocTheory.is_phy_var_def,GSYM EVEN_MOD2,EVEN_EXISTS]
  \\ strip_tac \\ strip_tac
  \\ rveq \\ fs[TWOxDIV2]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[CodeBufferWrite]:
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
       ,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ simp[wStackLoad_append]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg2
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ fs[stackSemTheory.evaluate_def]
  \\ `t''.code_buffer = s.code_buffer` by fs[state_rel_def]
  \\ fs[]
  \\ fs[state_rel_def]
  \\ gvs[]
  \\ metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[DataBufferWrite]:
  REPEAT STRIP_TAC \\ qexists_tac `0`
  \\ fs[get_labels_def]
  \\ fs[convs_def]
  \\ fs[wordLangTheory.max_var_def,wordLangTheory.max_var_exp_def,
     wordLangTheory.every_var_exp_def,reg_allocTheory.is_phy_var_def
       ,GSYM EVEN_MOD2]
  \\ fs[comp_def]
  \\ fs[wordSemTheory.evaluate_def]
  \\ gvs[AllCaseEqs(),UNCURRY_EQ]
  \\ simp[wStackLoad_append]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg1
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ simp[evaluate_wStackLoad_seq]
  \\ dxrule_all evaluate_wStackLoad_wReg2
  \\ strip_tac
  \\ simp[Once stackSemTheory.evaluate_def,evaluate_wStackLoad_clock]
  \\ fs[stackSemTheory.evaluate_def]
  \\ `t''.use_stack` by fs[state_rel_def]
  \\ `t''.data_buffer = s.data_buffer` by fs[state_rel_def]
  \\ fs[]
  \\ fs[state_rel_def,buffer_write_def]
  \\ gvs[]
  \\ metis_tac[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[FFI]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [EVAL ``post_alloc_conventions k (FFI ffi_index ptr1 len1 ptr2 len2
    names)``]
  \\ rw [] \\ fs [] \\ rw []
  \\ fs [wordSemTheory.evaluate_def]
  \\ qpat_x_assum `aaa = (res,s1)` mp_tac
  \\ rpt (ntac 2 (TOP_CASE_TAC \\ fs []))
  \\ fs [LET_DEF] \\ fs [] \\ rw [] \\ fs []
  \\ fs [comp_def]
  \\ rw[]
  \\ fs[stackSemTheory.evaluate_def]
  \\ fs [stackSemTheory.get_var_def]
  \\ `FLOOKUP t.regs 1 = get_var 2 s /\
      FLOOKUP t.regs 2 = get_var 4 s` by
   (fs [state_rel_def,LET_DEF,wordSemTheory.get_var_def] \\ res_tac
     \\ `4 < k * 2 /\ 1 < k` by decide_tac \\ fs [DIV_LT_X]) \\ fs []
  \\ `FLOOKUP t.regs 3 = get_var 6 s /\
      FLOOKUP t.regs 4 = get_var 8 s` by
   (fs [state_rel_def,LET_DEF,wordSemTheory.get_var_def] \\ res_tac
    \\ `8 < k * 2 /\ 6 < k * 2` by decide_tac \\ fs [DIV_LT_X]) \\ fs []
  \\ `t.be = s.be /\ t.mdomain = s.mdomain /\
      s.memory = t.memory /\ s.ffi = t.ffi /\
      s.sh_mdomain = t.sh_mdomain` by
        fs [state_rel_def] \\ fs [LET_THM]
  \\ qexists_tac `0` \\ fs []
  \\ fs [state_rel_def,LET_THM]
  \\ conj_tac THEN1 metis_tac[]
  \\ conj_tac
  >- (
    gvs[cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()]
    \\ simp[wf_union])
  \\ ntac 3 strip_tac
  \\ gvs[cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()]
  \\ fs [lookup_union,lookup_inter_alt,AllCaseEqs()]
  \\ fs [CONV_RULE (DEPTH_CONV ETA_CONV) (GSYM toAList_def)
         |> INST_TYPE [``:'a``|->``:unit``] |> SIMP_RULE (srw_ss()) []]
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,DIV_LT_X,FORALL_PROD,MEM_toAList]
  \\ fs [domain_lookup] \\ res_tac
  \\ `~(n' < k * 2)` by decide_tac \\ fs []
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[ShareInst]:
  rpt strip_tac >>
  gvs[EVAL ``post_alloc_conventions k (ShareInst op v exp)``,comp_def]
    >>
  old_drule flat_exp_conventions_ShareInst_exp_simp >>
  rpt strip_tac >>
  gvs[wordLangTheory.exp_to_addr_def,evaluate_ShareInst_Var_eq_Op_Add]
    >>
  gvs[wordLangTheory.every_var_exp_def,
      reg_allocTheory.is_phy_var_def,
      wordLangTheory.max_var_def,
      wordLangTheory.max_var_exp_def] >>
  gvs[GSYM EVEN_MOD2,EVEN_EXISTS,GSYM LEFT_ADD_DISTRIB] >>
  drule_all evaluate_ShareInst_correct_lemma >>
  rpt strip_tac >>
  gvs[] >>
  first_x_assum $ irule_at (Pos hd) >>
  gvs[]
QED
*)

(* TODO: clean up *)
(* HOL4 ML code, not ported:
val cruft_tac =
    rpt(PRED_ASSUM is_forall kall_tac) >>
    rpt(qpat_x_assum `_.compile_oracle = _` kall_tac) >>
    rpt(qpat_x_assum `_.compile = _` kall_tac) >>
    rpt(qpat_x_assum `_.clock = _` kall_tac) >>
    rpt(qpat_x_assum `domain _ = _` kall_tac) >>
    rpt(qpat_x_assum `_.store = _` kall_tac) >>
    rpt(qpat_x_assum `_.memory = _` kall_tac) >>
    rpt(qpat_x_assum `_.code_buffer = _` kall_tac) >>
    rpt(qpat_x_assum `_.data_buffer = _` kall_tac) >>
    rpt(qpat_x_assum `_.gc_fun = _` kall_tac) >>
    rpt(qpat_x_assum `_.fp_regs = _` kall_tac) >>
    rpt(qpat_x_assum `_.ffi = _` kall_tac) >>
    rpt(qpat_x_assum `_.be = _` kall_tac) >>
    rpt(qpat_x_assum `_ ∈ _` kall_tac) >>
    rpt(qpat_x_assum `_.mdomain = _` kall_tac) >>
    rpt(qpat_x_assum `(λbm0 cfg progs. _) = (λbm0 cfg progs. _)`
      kall_tac) >>
    rpt(qpat_x_assum `_.use_stack` kall_tac) >>
    rpt(qpat_x_assum `_.use_store` kall_tac) >>
    rpt(qpat_x_assum `_.use_alloc` kall_tac) >>
    rpt(qpat_x_assum `gc_fun_ok _` kall_tac) >>
    rpt(qpat_x_assum `_.ffi_save_regs = _` kall_tac) >>
    rpt(qpat_x_assum `_.code = _.code` kall_tac) >>
    rpt(qpat_x_assum `T` kall_tac) >>
    rpt(qpat_x_assum `_.termdep = _` kall_tac) >>
    rpt(qhdtm_x_assum `stack_rel` kall_tac) >>
    rpt(qhdtm_x_assum `list$isPREFIX` kall_tac) >>
    rpt(qhdtm_x_assum `wf` kall_tac) >>
    rpt(qhdtm_x_assum `post_alloc_conventions` kall_tac) >>
    rpt(qhdtm_x_assum `flat_exp_conventions` kall_tac) >>
    rpt(qhdtm_x_assum `good_dimindex` kall_tac) >>
    rpt(qpat_x_assum `_.clock <> _` kall_tac) >>
    rpt(qpat_x_assum `_.store \\ _ = _` kall_tac) >>
    rpt(qpat_x_assum `_ < dimword _` kall_tac)
*)

(* HOL4 ML code, not ported:
fun uncurry_case_rand x = x
                         |> TypeBase.case_rand_of
                         |> ISPEC ``(UNCURRY (A:'uniquea -> 'uniqueb ->
                           'uniquec))``
                         |> GEN ``(A:'uniquea -> 'uniqueb ->
                           'uniquec)``;
*)

(* HOL4 ML code, not ported:
fun note_tac s g = (print ("comp_Call_correct: " ^ s ^ "\n"); ALL_TAC
  g);
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Loop]:
  REPEAT GEN_TAC \\
  DISCH_THEN $ ASSUME_NAMED_TAC "IND" \\
  REPEAT STRIP_TAC \\
  fs[comp_def] \\ pairarg_tac \\ fs[] \\ rveq \\
  qpat_x_assum `evaluate (Loop _ _ _, _) = _` mp_tac \\
  simp[Once wordSemTheory.evaluate_def] \\
  Cases_on `cut_state (names,LN) s` \\ fs[] \\
  Cases_on `evaluate (c,x)` \\ fs[] \\
  strip_tac \\
  `q ≠ SOME Error` by (
    strip_tac \\ gvs[]) \\
  simp[Once stackSemTheory.evaluate_def] \\
  LABEL_ASSUM "IND" (mp_tac o CONJUNCT2) \\
  disch_then (qspec_then `x` mp_tac) \\ simp[] \\
  disch_then (qspecl_then
    [`k`,`f`,`f'`,`t`,`bs`,`n`,`bs'`,`n'`,`q1`,`lens`] mp_tac) \\
  impl_tac
  >- (
    conj_tac >- (drule_all state_rel_cut_state \\ simp[]) \\
    fs[wordConvsTheory.post_alloc_conventions_def,
       wordConvsTheory.call_arg_convention_def,
       wordConvsTheory.flat_exp_conventions_def,
       wordLangTheory.every_var_def,
       wordLangTheory.every_stack_var_def,
       wordLangTheory.max_var_def,
       miscTheory.max3_def,
       get_labels_def]) \\
  strip_tac \\
  rename1 `evaluate (q1, _) = (res_b, t1_b)` \\
  reverse (Cases_on `OPTION_MAP compile_result q = res_b`) \\ fs[]
  >- (
*)
    (* stack-overflow sub-case *)
(* HOL4 ML code, not ported:
    qexists_tac `ck` \\
    qexists_tac `t1_b` \\
    qexists_tac `SOME (Halt (Word 2w))` \\
    simp[stackSemTheory.cont_loop_def, stackSemTheory.exit_loop_def] \\
    `good_dimindex (:'a)` by fs[state_rel_def] \\
    `OPTION_MAP compile_result res ≠ SOME (Halt (Word 2w))` by (
      Cases_on `res` \\ fs[] \\
      metis_tac[Halt_EQ_compile_result]) \\
    `∀z. res = SOME z ⇒ Halt (Word 2w) ≠ compile_result z` by (
      rpt strip_tac \\ fs[] \\ metis_tac[Halt_EQ_compile_result]) \\
    simp[] \\
    `r.ffi.io_events ≼ s1.ffi.io_events ∧
     the (s1.stack_limit + 1) s1.stack_max > s1.stack_limit` by (
      qpat_x_assum `_ = (res, s1)` mp_tac \\
      Cases_on `cont_loop q` \\ fs[]
      >- (
        Cases_on `r.clock = 0` \\ fs[]
        >- (strip_tac \\ rveq \\ fs[wordSemTheory.flush_state_def]) \\
        simp[wordSemTheory.STOP_def] \\ strip_tac \\
        imp_res_tac wordPropsTheory.evaluate_io_events_mono \\
        imp_res_tac wordPropsTheory.evaluate_stack_limit_stack_max \\
        fs[wordSemTheory.dec_clock_def]) \\
      Cases_on `q = SOME (Break 0)` \\ fs[]
      >- (every_case_tac \\ strip_tac \\ rveq \\ fs[] \\
          fs[wordSemTheory.cut_state_def, AllCaseEqs()] \\ rveq \\ fs[])
            \\
      strip_tac \\ rveq \\ fs[]) \\
    `t1_b.ffi.io_events ≼ s1.ffi.io_events` by
      metis_tac[IS_PREFIX_TRANS] \\
    fs[]) \\
*)
  (* non-stack-overflow: res_b = OPTION_MAP compile_result q, so IH's
     "else"
     branch gives us state_rel-like facts about r and t1_b per q. *)
(* HOL4 ML code, not ported:
  Cases_on `cont_loop q` \\ fs[]
  >- (
*)
    (* cont_loop q: either q = NONE or q = SOME (Continue 0) *)
(* HOL4 ML code, not ported:
    Cases_on `r.clock = 0` \\ fs[]
    >- (
*)
      (* TimeOut: s1 = flush_state T r, res = SOME TimeOut *)
(* HOL4 ML code, not ported:
      qexists_tac `ck` \\
      `state_rel ac k f f' r t1_b lens 0` by (
        Cases_on `q` \\ gvs[] \\
        Cases_on `x'` \\ gvs[]) \\
      `t1_b.clock = 0 ∧ r.ffi = t1_b.ffi` by fs[state_rel_def] \\
      gvs[wordSemTheory.flush_state_def, stackSemTheory.empty_env_def]
        \\
      `cont_loop (OPTION_MAP compile_result q)` by
        (Cases_on `q` \\ gvs[] \\ Cases_on `x'` \\ gvs[]) \\
      qexists_tac `t1_b with <|regs := FEMPTY; stack := []|>` \\
      qexists_tac `SOME TimeOut` \\ gvs[]) \\
*)
    (* recursive case: clock ≠ 0, recurse with dec_clock *)
(* HOL4 ML code, not ported:
    `state_rel ac k f f' r t1_b lens 0` by (
      Cases_on `q` \\ gvs[] \\ Cases_on `x'` \\ gvs[]) \\
    `cont_loop res_b ∧ res_b ≠ SOME TimeOut ∧ t1_b.clock ≠ 0` by (
      `r.clock = t1_b.clock` by fs[state_rel_def] \\
      Cases_on `q` \\ gvs[wordSemTheory.cont_loop_def,
                          stackSemTheory.cont_loop_def] \\
      Cases_on `x'` \\ gvs[wordSemTheory.cont_loop_def,
                           stackSemTheory.cont_loop_def]) \\
    `subspt t.code t1_b.code ∧ t.bitmaps ≼ t1_b.bitmaps` by
      (drule stackPropsTheory.evaluate_mono \\ simp[]) \\
    fs[] \\
    `state_rel ac k f f' (dec_clock r) (dec_clock t1_b) lens 0` by
      metis_tac[state_rel_dec_clock] \\
    `comp ac F (Loop names c exit_names) (bs,n) (k,f,f') = (Loop q1,
      bs', n')` by
      (simp[comp_def] \\ pairarg_tac \\ fs[]) \\
    LABEL_ASSUM "IND" (assume_tac o CONJUNCT1) \\
    first_x_assum (qspecl_then [`x`,`q`,`r`] mp_tac) \\ simp[] \\
    strip_tac \\
    first_x_assum drule \\
    disch_then (qspecl_then [`bs`,`n`,`bs'`,`n'`,`Loop q1`] mp_tac) \\
    impl_tac
    >- (
      `LENGTH t.bitmaps ≤ LENGTH t1_b.bitmaps` by
        (imp_res_tac IS_PREFIX_LENGTH \\ fs[]) \\
      `DROP (n - LENGTH (append bs)) t.bitmaps ≼
       DROP (n - LENGTH (append bs)) t1_b.bitmaps` by fs[isPREFIX_DROP]
         \\
      `append bs' ≼ DROP (n - LENGTH (append bs)) t1_b.bitmaps` by
        metis_tac[isPREFIX_TRANS] \\
      `loc_check t.code ⊆ loc_check t1_b.code` by
        (match_mp_tac loc_check_SUBSET \\ fs[]) \\
      `get_labels (Loop q1) ⊆ loc_check t1_b.code` by
        (drule get_labels_loc_check_subspt \\ fs[]) \\
      fs[wordSemTheory.STOP_def, stackSemTheory.STOP_def,
         stackSemTheory.dec_clock_def]) \\
    strip_tac \\
    rename1 `evaluate (Loop q1, _) = (res1_ih, t1_ih)` \\
    qexists_tac `ck + ck'` \\
    qexists_tac `t1_ih` \\
    qexists_tac `res1_ih` \\
    `∀extra. evaluate (q1, t with clock := ck + extra + t.clock) =
     (res_b, t1_b with clock := t1_b.clock + extra)` by (
      rpt strip_tac \\
      qspecl_then [`q1`, `t with clock := ck + t.clock`, `res_b`,
        `t1_b`]
        mp_tac stackPropsTheory.evaluate_add_clock \\
      impl_tac >- fs[] \\ simp[]) \\
    `evaluate (q1, t with clock := ck + ck' + t.clock) =
     (res_b, t1_b with clock := t1_b.clock + ck')` by fs[] \\
    `x.handler = s.handler` by
      (fs[wordSemTheory.cut_state_def, AllCaseEqs()] \\ rveq \\ fs[]) \\
    `r.handler = s.handler` by
      (drule_all evaluate_cont_loop_handler \\ fs[]) \\
    simp[wordSemTheory.STOP_def, stackSemTheory.STOP_def,
         stackSemTheory.dec_clock_def, wordSemTheory.dec_clock_def] \\
    `ck' + t1_b.clock - 1 = ck' + (t1_b.clock - 1)` by decide_tac \\
    pop_assum SUBST1_TAC \\
    conj_tac
    >- (qpat_x_assum `evaluate (Loop q1,_) = _` mp_tac \\
        simp[stackSemTheory.dec_clock_def]) \\
    fs[]) \\
  reverse (Cases_on `q = SOME (Break 0)`) \\ fs[]
  >- (
*)
    (* passthrough: s1 = r, stack exit_loop matches *)
(* HOL4 ML code, not ported:
    qexists_tac `ck` \\
    `x.handler = s.handler` by
      (fs[wordSemTheory.cut_state_def, AllCaseEqs()] \\ rveq \\ fs[]) \\
    Cases_on `q` \\ gvs[] \\
    Cases_on `x'` \\ fs[] \\ gvs[] \\
    rpt (qexists_tac `t1_b`) \\ gvs[] \\
    metis_tac[]) \\
*)
  (* Break 0: s1 = cut_state (exit_names,LN) r *)
(* HOL4 ML code, not ported:
  qexists_tac `ck` \\
  Cases_on `cut_state (exit_names, LN) r` \\ gvs[] \\
  metis_tac[state_rel_cut_state]
QED
*)


(* HOL4 ML code, not ported:
Resume comp_correct[Call]:
  REPEAT GEN_TAC \\
  DISCH_THEN $ ASSUME_NAMED_TAC "IND" \\
  REPEAT STRIP_TAC \\
  fs[comp_def,UNCURRY_EQ]\\ rveq \\
  Cases_on `ret` \\ fs[] \\ rveq \\
  fs[get_labels_def]
  >- suspend "Call_tail"
  >- suspend "Call_returning"
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Call_tail]:
    note_tac "comp_correct tail call case"
    \\ fs[AllCaseEqs()] \\ rveq
    \\ qpat_x_assum `_ = (res,s1)` mp_tac
    \\ simp[wordSemTheory.evaluate_def,Ntimes (AllCaseEqs())
      6,PULL_EXISTS]
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ drule_all call_dest_lemma
    \\ disch_then (Q.SPEC_THEN `NONE` mp_tac)
    \\ simp[] \\ strip_tac
    \\ old_drule (GEN_ALL evaluate_add_clock) \\ fsrw_tac[] []
    \\ simp[Once stackSemTheory.evaluate_def]
    \\ disch_then kall_tac
    \\ `t4.clock = s.clock /\ t4.use_stack` by fsrw_tac[]
      [state_rel_def]
    \\ `!n p ck. evaluate (SeqStackFree n p,t4 with clock := ck) =
                 evaluate (Seq (StackFree n) p,t4 with clock := ck)` by
     (rw [] \\ match_mp_tac evaluate_SeqStackFree
      \\ fsrw_tac[] [state_rel_def] \\ decide_tac) \\ fsrw_tac[][]
    \\ pop_assum kall_tac
    \\ qmatch_goalsub_abbrev_tac `(Seq _ CALL)`
    \\ fsrw_tac[] [stackSemTheory.evaluate_def]
    \\ `~ (LENGTH t.stack <
         t.stack_space + stack_free dest' (LENGTH args) (k,f,f'))`
        by (fsrw_tac[] [stack_free_def]
         \\ Cases_on `dest'` \\ fsrw_tac[] [stack_arg_count_def]
         \\ fsrw_tac[] [state_rel_def,LET_DEF] \\ decide_tac)
    \\ fsrw_tac[] [LET_DEF,Abbr`CALL`]
    \\ simp[Once stackSemTheory.evaluate_def]
    \\ simp[Once (AllCaseEqs())] \\ strip_tac \\ rveq
    THEN1 (qexists_tac `0` \\ simp[flush_state_def] \\
      fs[state_rel_def])
    \\ fs[TypeBase.case_eq_of ``:'a option``,TypeBase.case_eq_of ``:'a #
      'b``]
    \\ rveq \\ fs[]
    \\ Cases_on `bad_fun_return res'` \\ gvs[]
    \\ fsrw_tac[][]
    \\ imp_res_tac compile_prog_stack_size
    \\ qhdtm_x_assum `compile_prog` mp_tac
    \\ fsrw_tac[][compile_prog_def]
    \\ LET_ELIM_TAC \\ fsrw_tac[][] \\ rveq
    \\ simp[stackSemTheory.evaluate_def]
    \\ fsrw_tac[][stack_free_def]
    \\ `Abbrev (stack_arg_count' = stack_arg_count dest' (LENGTH args)
      k) `
          by (
          simp[Abbr`stack_arg_count'`,markerTheory.Abbrev_def] \\
          `LENGTH xs = LENGTH args` by
          (imp_res_tac get_vars_length_lemma) \\
          pop_assum mp_tac \\
          qhdtm_x_assum `wordSem$find_code` (mp_tac) \\
          qhdtm_x_assum `call_dest` (mp_tac) \\
          rpt (pop_assum kall_tac) \\
          rpt strip_tac \\
          Cases_on `dest` \\
          fs[find_code_def,call_dest_def,CaseEq"option",CaseEq"prod"
            ,CaseEq"word_loc",CaseEq"num",
            add_ret_loc_def] \\
          rveq \\ fs[] \\
          rfs[LENGTH_FRONT] \\
          fs[stack_arg_count_def] \\
          `args <> []` by(CCONTR_TAC \\ fs[]) \\
          fs[UNCURRY_EQ] \\
          rveq \\ fs[])
    \\ fs[]
    \\ `LENGTH args - 1 < f' + k`
       by
         (
         fsrw_tac[][convs_def] \\
         qpat_x_assum `max_var _ < _` mp_tac \\
         qpat_x_assum `args = _` SUBST_ALL_TAC \\
         simp[wordLangTheory.max_var_def] \\
         simp[MAX_LIST_GENLIST_evens] \\
         simp[GSYM LEFT_ADD_DISTRIB])
    \\ `LENGTH xs >= (LENGTH args1)`
           by (qpat_x_assum`A=SOME(q,q',r')` mp_tac>>
              Cases_on`dest`>>fsrw_tac[][find_code_def
                ,add_ret_loc_def]>>
              simp[AllCaseEqs()] >> strip_tac >>
              rveq >> fsrw_tac[][] >>
              simp[LENGTH_FRONT])
    \\ `LENGTH xs = LENGTH args` by
       (imp_res_tac get_vars_length_lemma)
*)
    (*preconditions for negation rules*)
(* HOL4 ML code, not ported:
    \\ `stack_arg_count' <= f /\ stack_arg_count' <= f''`
        by  (fsrw_tac[][state_rel_def] \\
         `stack_arg_count' <= stack_var_count`
              by (fs[Abbr `stack_var_count`]) \\
         `stack_var_count <= f''`
              by(fs[Abbr`f''`]) \\
         `stack_arg_count' = LENGTH args1 -k`
            by (UNABBREV_ALL_TAC  \\ fsrw_tac[][]) \\
          Cases_on `f' = 0` >> fs[])
    \\ fs[SF CONJ_ss]
    \\ PURE_TOP_CASE_TAC
    THEN1 ( (* Hit stack limit case *)
      fsrw_tac[][PULL_EXISTS] \\
      `∀z. Halt (Word 2w) ≠ compile_result (z:'a wordSem$result)` by
         fs[state_rel_def,compile_result_NOT_2] \\
      fsrw_tac[][] \\
      `t4.ffi = s.ffi` by fs[state_rel_def] \\
      fsrw_tac[][] \\
      imp_res_tac wordPropsTheory.evaluate_io_events_mono \\
      fs[] \\
      imp_res_tac evaluate_stack_limit \\
      imp_res_tac evaluate_stack_max \\
      fsrw_tac[][call_env_def] \\
      PURE_FULL_CASE_TAC >- fs[the_eqn] \\
      fsrw_tac[][] \\ rveq \\
      fsrw_tac[][state_rel_def] \\
      qhdtm_x_assum `stack_size_rel` mp_tac \\
      fsrw_tac[][stack_size_rel_def] \\
      Cases_on `s'.stack_max` \\ fsrw_tac[][the_eqn] \\
      rveq \\ fs[GREATER_EQ])
    \\ fsrw_tac[][stackSemTheory.dec_clock_def]
    \\ (fn g =>
         qabbrev_tac `t5 = ^((qexists_tac`0`
         \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t5)`) g
         |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g)
    \\ `state_rel ac k f'' stack_var_count (call_env args1 ss (dec_clock
      s)) t5 lens 0` by
        (
        fsrw_tac[][state_rel_def,dec_clock_def,Abbr`t5`] \\
        fsrw_tac[][call_env_def] \\
        CONJ_TAC >-
        (rpt (PRED_ASSUM (not o is_forall) kall_tac) \\
        METIS_TAC[]) \\
        CONJ_TAC >- (fs[Abbr`f''`]) \\
        CONJ_TAC >- (fs[Abbr`f''`]) \\
        CONJ_TAC >- (fs[wf_fromList2]) \\
        CONJ_TAC >- (
          qhdtm_x_assum `stack_size_rel` mp_tac \\
          simp[stack_size_rel_def] \\
          rpt (gen_tac ORELSE disch_tac) \\
          rpt (CHANGED_TAC (fsrw_tac[][] \\ rveq)) \\
          TIDY_ABBREVS \\ fs[MAX_DEF]) \\
        fsrw_tac[][LET_THM] \\
        CONJ_TAC >- (TIDY_ABBREVS \\ fs[DROP_DROP_EQ]) \\
        rpt (GEN_TAC ORELSE DISCH_TAC) \\ fsrw_tac[][] \\
        imp_res_tac (GSYM domain_lookup)>>
        imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
        `lookup n' s.locals = SOME v`
           by (
            fsrw_tac[][convs_def] >>
            qpat_x_assum`args=_` SUBST_ALL_TAC>>
            imp_res_tac get_vars_fromList2_eq>>
            `isPREFIX args1 xs` by (
              qpat_x_assum`_=SOME(q,q',r')` mp_tac>>
              Cases_on`dest`>>fsrw_tac[][find_code_def
                ,add_ret_loc_def]>>
              simp[AllCaseEqs()] >> strip_tac >>
              fsrw_tac[][] >> rveq >> fsrw_tac[][] >>
              Cases_on`xs`>>fsrw_tac[][IS_PREFIX_BUTLAST])>>
            imp_res_tac lookup_fromList2_prefix >>
            res_tac) >>
        IF_CASES_TAC>-
          (res_tac \\
          rpt (PRED_ASSUM
          (fn x => is_forall x orelse is_eq x orelse
            markerSyntax.is_abbrev x) kall_tac) \\ rfs[]) \\
        fsrw_tac[][LLOOKUP_THM]>>
        `stack_var_count <> 0`
          by
           (fsrw_tac[] [markerTheory.Abbrev_def] \\ rpt var_eq_tac \\
             fsrw_tac[] []
            \\ fsrw_tac[] [lookup_fromList2,lookup_fromList]
            \\ decide_tac) >>
        simp[Abbr`f''`]>>
        fsrw_tac[][lookup_fromList2,lookup_fromList]>>
        CONJ_ASM2_TAC
          >- (
            TIDY_ABBREVS \\
            first_x_assum(qspecl_then[`n'`,`v`] mp_tac)>>
            simp[EL_TAKE,EL_DROP]>>
            strip_tac>>
            qpat_x_assum`_=v` mp_tac>>
            simp[EL_TAKE,EL_DROP]>>
            disch_then sym_sub_tac>>
            AP_THM_TAC>>AP_TERM_TAC>>
            `(n' DIV 2 +1) ≤ f+k` by
              (Cases_on`f'`>>fsrw_tac[][]>>
              DECIDE_TAC)>>
            simp[])>>
        unabbrev_all_tac>>
        fsrw_tac[][] >>
        simp[MAX_DEF]) \\
    LABEL_X_ASSUM "IND" mp_tac
    \\ simp[]
    \\ DISCH_THEN drule
    \\ disch_then (drule_at Any) \\ fsrw_tac[] []
    \\ impl_tac THEN1 (
      CONJ_ASM1_TAC>-
        (qpat_x_assum`_=SOME(q,q',r')`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][add_ret_loc_def,wordSemTheory.find_code_def]>>
        simp[AllCaseEqs()] >> strip_tac >>
        fsrw_tac[][] >> rveq >> fsrw_tac[][] >>
        fsrw_tac[][state_rel_def] >>
        metis_tac[])>>
      CONJ_ASM1_TAC>-
        (qpat_x_assum`_=SOME(q,q',r')`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][add_ret_loc_def,wordSemTheory.find_code_def]>>
        simp[AllCaseEqs()] >> strip_tac >>
        fsrw_tac[][] >> rveq >> fsrw_tac[][] >>
        fsrw_tac[][state_rel_def] >>
        metis_tac[])>>
      imp_res_tac evaluate_mono>>fs[]>>
      CONJ_TAC>- (old_drule IS_PREFIX_LENGTH>>fs[Abbr`t5`]) >>
      CONJ_TAC>-
        (fs[Abbr`t5`]>>metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]) >>
      CONJ_TAC >-
       (qunabbrev_tac `t5` \\ simp_tac (srw_ss()) []
        \\ old_drule find_code_IMP_get_labels
        \\ fs [get_labels_def])
      >>
        (`EVEN (max_var prog)` by
            (ho_match_mp_tac max_var_intro>>
            fsrw_tac[][convs_def]>>
            match_mp_tac every_var_mono>>
            HINT_EXISTS_TAC>>fsrw_tac[][reg_allocTheory.is_phy_var_def
              ,EVEN_MOD2])>>
        simp[Abbr`stack_var_count`] >>
        fsrw_tac[][EVEN_EXISTS,GSYM LEFT_ADD_DISTRIB]>>
        simp[GSYM LEFT_ADD_DISTRIB ] >>
        fsrw_tac[][MULT_COMM,MAX_DEF]>>rw[]>>
        DECIDE_TAC))
    \\ strip_tac \\ fsrw_tac[] []
    \\ qunabbrev_tac `t5` \\ fsrw_tac[] []
    \\ `ck + (s.clock - 1) = ck + s.clock - 1` by decide_tac
    \\ qexists_tac `ck` \\ fsrw_tac[] []
    \\ IF_CASES_TAC
    >- (fs[PULL_EXISTS]
        \\ Cases_on `res` \\ fs[]
        \\ Cases_on `x` \\ gvs[compile_result_def, bad_fun_return_def]
        \\ Cases_on `res1` \\ fs[bad_fun_return_def]
        \\ Cases_on `x` \\ fs[bad_fun_return_def])
    \\ fs[PULL_EXISTS]
    \\ IF_CASES_TAC >- fs[]
    \\ Cases_on `res` \\ fs[]
    \\ Cases_on `x` \\ fs[bad_fun_return_def]
    \\ qexistsl[`l0`,`l`] \\ simp[]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Call_returning]:
  note_tac "comp_correct returning call case(s)"
  \\ fs[UNCURRY_EQ,TypeBase.case_eq_of ``:'a # 'b``] \\ rveq
  \\ qpat_x_assum `_ = (res,s1)` mp_tac
  \\ simp[wordSemTheory.evaluate_def,Ntimes (AllCaseEqs())
    7,PULL_EXISTS]
  \\ rpt strip_tac
  \\ rveq \\ fsrw_tac[][]
  \\ drule_all call_dest_lemma
  \\ disch_then (qspec_then `SOME (vs,live,ret_code,l1,l2)` mp_tac)
  \\ strip_tac \\ rfs[] \\ fsrw_tac[][]
  \\ imp_res_tac evaluate_call_dest_clock
  \\ pop_assum(qspec_then`t` assume_tac)
  \\ Cases_on `bs''`
  \\ old_drule ((GEN_ALL evaluate_wLive)|> REWRITE_RULE[GSYM
    AND_IMP_INTRO])
  \\ rpt $ disch_then (drule_at Any)
  \\ simp[]
  \\ impl_keep_tac>- (
    rpt(qpat_x_assum`!x. _` kall_tac) >>
    LABEL_X_ASSUM "IND" kall_tac >>
    fsrw_tac[][convs_def,lambdify reg_allocTheory.is_phy_var_def,
    GSYM EVEN_MOD2,SF ETA_ss]>>
    fsrw_tac[][GSYM toAList_domain,EVERY_MEM]>>
    fsrw_tac[][X_LE_DIV,LET_THM]>>
    qhdtm_x_assum `cut_envs` mp_tac >>
    Cases_on `live` >> simp[cut_envs_def,AllCaseEqs()] >>
    rpt (disch_then strip_assume_tac) >>
    rveq >> fsrw_tac[][] >>
    qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
    pure_rewrite_tac[wordLangTheory.max_var_def] >>
    `!x y z. max3 x y z = MAX x (MAX y z)`
      by fs[MAX_DEF,max3_def] >>
    pop_assum (pure_rewrite_tac o single) >>
    fsrw_tac[][LET_DEF] >> strip_tac >>
    namedCases_on `handler`["","h"] >>
    TRY (PairCases_on `h`) >>
    rveq >> fs[] >>
    rveq >> fs[] >>
*)
    (* Two subgoals *)
(* HOL4 ML code, not ported:
    (CONJ_TAC
    >- (
      GEN_TAC >> disch_tac >>
      first_x_assum drule >>
      simp[]) >>
    CONJ_TAC
    >- (
      GEN_TAC >> disch_tac >>
      first_x_assum drule >>
      simp[]) >>
    CONJ_TAC
    >- (
    `∃nn. MEM nn (MAP FST (toAList q'))` by
      (CCONTR_TAC>>
      fsrw_tac[][toAList_domain]>>
      `domain q' = {}` by
        fsrw_tac[][EXTENSION])>>
    first_x_assum drule>>
    drule MAX_LIST_PROPERTY >>
    rpt strip_tac >>
    `nn < 2*f'+2*k` by
      (DECIDE_TAC)>>
    `f' ≠ 0` by DECIDE_TAC>>
    fsrw_tac[][state_rel_def]) >>
    CONJ_TAC
    >- (
    old_drule evaluate_mono>> strip_tac>>
    old_drule IS_PREFIX_LENGTH>>
    simp[])>>
    fs[UNCURRY_EQ] >>
    imp_res_tac comp_IMP_isPREFIX>> fsrw_tac[][]>>
    old_drule evaluate_mono>>
    metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])) >>
  strip_tac>>
  imp_res_tac evaluate_wLive_clock>>
  pop_assum (qspec_then`t4` assume_tac)>>
  Cases_on`handler`>> fs[] >> rveq >> fs[]
  >- (
    note_tac "No handler case">>
    simp[Ntimes stackSemTheory.evaluate_def 2]>>
    imp_res_tac compile_prog_stack_size >>
    qhdtm_x_assum `compile_prog` mp_tac >>
    fsrw_tac[][compile_prog_def] >>
    LET_ELIM_TAC >> fs[] >> rveq >>
*)
    (*TODO shouldn't be unfolding here*)
(* HOL4 ML code, not ported:
    simp[StackArgs_def,stackSemTheory.evaluate_def,
    Once evaluate_stack_move_seq]>>
    simp[uncurry_case_rand ``:bool``] >>
*)
    (*Get through the eval of stack_move*)
(* HOL4 ML code, not ported:
    `t5.use_stack` by fsrw_tac[][state_rel_def] >>
    pop_assum (simp o single) >>
    `Abbrev (stack_arg_count' = stack_arg_count dest' (LENGTH args + 1)
      k)`
       by(
       simp[Abbr`stack_arg_count'`,markerTheory.Abbrev_def
         ,stack_arg_count_def] >>
       `LENGTH args = LENGTH xs`
          by (imp_res_tac get_vars_length_lemma >> fsrw_tac[][]) >>
       pop_assum mp_tac >>
       qhdtm_x_assum `call_dest` mp_tac >>
       qpat_x_assum `¬bad_dest_args _ _` mp_tac >>
       qhdtm_x_assum `wordSem$find_code` mp_tac >>
       rpt (pop_assum kall_tac) >>
       simp[oneline call_dest_def,AllCaseEqs()] >>
       rpt strip_tac >> fs[bad_dest_args_def] >>
       gvs[UNCURRY_EQ] >>
       qhdtm_x_assum `wordSem$find_code` mp_tac >>
       simp[wordSemTheory.find_code_def,add_ret_loc_def,AllCaseEqs()] >>
       strip_tac >> fs[] >> rveq >>
       fs[LENGTH_FRONT,ADD1]) >>
    fs[] >>
    Cases_on `t.stack_space < stack_arg_count'` >> fs[]
    >- (
       `!x. compile_result x ≠ Halt (Word 2w)`
          by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
        fsrw_tac[][] >>
        `t5.ffi = s.ffi` by fsrw_tac[][state_rel_def] >>
        `stack_arg_count' = LENGTH args1 − k` by
        fsrw_tac[][Abbr`stack_arg_count'`] >>
        `the (s.stack_limit + 1)
          (call_env args1 ss (push_env envs NONE s)).stack_max >
        s.stack_limit`
          by (simp[call_env_def,the_eqn] >>
          PURE_TOP_CASE_TAC >- simp[] >>
          fsrw_tac[][state_rel_def,stack_size_rel_def,GREATER_DEF] >>
          rveq >>
          fsrw_tac[][push_env_def,ELIM_UNCURRY,LET_DEF,stack_size_eq] >>
          rveq >> fsrw_tac[][the_eqn] >>
          rveq >> fsrw_tac[][] >>
          rfs[]) >>
        qpat_x_assum `_ = (res,s1)` mp_tac >>
        simp[Once $ AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        CONJ_TAC >-(
            pop_assum mp_tac >>
            simp[AllCaseEqs()] >>
            strip_tac >> rveq >> fs[] >>
            imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
            imp_res_tac wordPropsTheory.pop_env_const >>
            fsrw_tac[][] >>
            rpt (qpat_x_assum `_ ≼ _` mp_tac) >>
            rpt (pop_assum kall_tac) >>
            METIS_TAC[IS_PREFIX_TRANS]) >>
        pop_assum mp_tac >>
        simp[AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        imp_res_tac wordPropsTheory.pop_env_const >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[dec_clock_def] >>
        drule_then match_mp_tac evaluate_stack_limit_stack_max >>
        simp[dec_clock_def])  >>
    qabbrev_tac`t6 = t5 with <|stack_space :=t5.stack_space -
      stack_arg_count'|>` >>
    `!ck. t5 with <|stack_space:=t5.stack_space - stack_arg_count';
      clock:=ck+t.clock|> =
        t6 with clock:=ck+t.clock` by
       simp[stackSemTheory.state_component_equality,Abbr`t6`]>>
     rev_full_simp_tac std_ss [] >>
    Q.ISPECL_THEN [`stack_arg_count'`,`0n`,`t6`,`f`] mp_tac
      evaluate_stack_move>>
    impl_tac >- (
      simp[Abbr`t6`] >>
      fsrw_tac[][state_rel_def] >>
      qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
      pure_rewrite_tac[wordLangTheory.max_var_def] >>
      `!x y z. max3 x y z = MAX x (MAX y z)`
        by fs[MAX_DEF,max3_def] >>
      pop_assum (pure_rewrite_tac o single) >>
      fsrw_tac[][LET_DEF] >> strip_tac >>
      fsrw_tac[][convs_def]>>
      qpat_x_assum`args = A` SUBST_ALL_TAC>>
      fsrw_tac[][MAX_LIST_GENLIST_evens2]>>
      rveq >>
      Cases_on `f' = 0` >> fsrw_tac[][] >>
      Cases_on `dest'` >>
      fsrw_tac[][stack_arg_count_def] >>
      fsrw_tac[][Abbr`stack_arg_count'`] >>
*)
      (*TODO this is very slow*)
(* HOL4 ML code, not ported:
      gvs[]) >>
    strip_tac  >>
    rfs[evaluate_stack_move_clock] >>
    fs[Abbr`t6`] >>
    `find_code dest' (t'_regs \\0) t5.code = find_code dest' t4.regs
      t4.code` by (
      `subspt t4.code t5.code` by
        (unabbrev_all_tac>>
        fs[stackSemTheory.state_component_equality]>>
        imp_res_tac evaluate_mono>>fs[]>>
        metis_tac[evaluate_consts])>>
      Cases_on`dest'`>>fs[stackSemTheory.find_code_def]
      >- metis_tac[subspt_def,domain_lookup] >>
      qpat_x_assum`A=SOME stack_prog` mp_tac>>
      qpat_x_assum`A=(q0,INR y)` mp_tac>>
      Cases_on`dest`>>simp[call_dest_def]>>
      IF_CASES_TAC>>simp[]>>
      simp[wReg2_def]>>IF_CASES_TAC>>fs[]
      >- (
        `LAST args DIV 2≠ 0 ∧ LAST args DIV 2 ≠ k` by (
          fs[convs_def]>>
          qpat_x_assum`args = A` SUBST_ALL_TAC>>
          `LENGTH args <> 0` by (strip_tac \\ fs[]) >>
          old_drule LAST_GENLIST_evens>>
          LET_ELIM_TAC>>simp[]>>
          Cases_on`reg`>>fs[]>>
          rename1`SUC xx DIV _ ≠ _`>>
          Cases_on`xx`>>fs[]>>
          simp[ADD_DIV_RWT,ADD1])>>
        strip_tac>>rveq>>
        simp[DOMSUB_FLOOKUP_THM]>>
        fs[stackSemTheory.get_var_def]>>
        qpat_x_assum`subspt _ _` mp_tac>>
        rpt (pop_assum kall_tac)>>
        EVERY_CASE_TAC>>rw[]>>
        metis_tac[subspt_def,domain_lookup])
      >>
        strip_tac>>rveq>>
        simp[DOMSUB_FLOOKUP_THM]>>
        fs[stackSemTheory.get_var_def]>>
        qpat_x_assum`subspt _ _` mp_tac>>
        rpt (pop_assum kall_tac)>>
        EVERY_CASE_TAC>>rw[]>>
        metis_tac[subspt_def,domain_lookup])>>
    pop_assum SUBST_ALL_TAC >>
    fsrw_tac[][] >>
    `t.clock = s.clock` by fs[state_rel_def] >>
    pop_assum SUBST_ALL_TAC >>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    IF_CASES_TAC>- (
      rw[]>>qexists_tac`0`>>
      simp[] >>
      fsrw_tac[][state_rel_def]) >>
    fsrw_tac[][] >>
    rpt $ (qpat_x_assum `!_. evaluate (_,_ with clock := _) = _`
      kall_tac) >>
    strip_tac >>
    simp[stackSemTheory.evaluate_def]>>
    `stack_arg_count' <= f''`
        by  (fsrw_tac[][state_rel_def] \\
         `stack_arg_count' <= stack_var_count`
              by (fs[Abbr `stack_var_count`]) \\
         `stack_var_count <= f''`
              by(fs[Abbr`f''`]) \\
         `stack_arg_count' = LENGTH args1 -k`
            by (UNABBREV_ALL_TAC  \\ fsrw_tac[][]) \\
          Cases_on `f' = 0` >> fs[]) >>
    fs[SF CONJ_ss] >>
    `t5.use_stack` by fsrw_tac[][state_rel_def] >>
    pop_assum (simp o single) >>
    PURE_TOP_CASE_TAC
    THEN1 ((* Hit stack limit case *)
    `!x. compile_result x ≠ Halt (Word 2w)`
       by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
    fsrw_tac[][] >>
    `t5.ffi = s.ffi` by fsrw_tac[][state_rel_def] >>
    `stack_arg_count' = LENGTH args1 − k` by
    fsrw_tac[][Abbr`stack_arg_count'`] >>
    `the (s.stack_limit + 1)
      (call_env args1 ss (push_env envs NONE s)).stack_max >
    s.stack_limit`
      by (simp[call_env_def,the_eqn] >>
      PURE_TOP_CASE_TAC >- simp[] >>
      fsrw_tac[][state_rel_def,stack_size_rel_def,GREATER_DEF] >>
      rveq >>
      fsrw_tac[][push_env_def,ELIM_UNCURRY,LET_DEF,stack_size_eq] >>
      rveq >> fsrw_tac[][the_eqn] >>
      rveq >> fsrw_tac[][] >>
      rfs[]) >>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    simp[Once $ AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    CONJ_TAC >-(
        pop_assum mp_tac >>
        simp[AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
        imp_res_tac wordPropsTheory.pop_env_const >>
        fsrw_tac[][] >>
        rpt (qpat_x_assum `_ ≼ _` mp_tac) >>
        rpt (pop_assum kall_tac) >>
        METIS_TAC[IS_PREFIX_TRANS]) >>
    pop_assum mp_tac >>
    simp[AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    imp_res_tac wordPropsTheory.pop_env_const >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def] >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def])
    >> fsrw_tac[][] >>
    simp[]>>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    qpat_abbrev_tac`word_state = call_env args1 ss st`>>
    strip_tac >>
*)
    (*This looks hacky but it works*)
(* HOL4 ML code, not ported:
    (fn g =>
         qabbrev_tac `stack_state = ^((qexists_tac`0`
         \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t7)`) g
         |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g) >>
    `state_rel ac k f'' stack_var_count word_state stack_state
      (f'::lens) 0` by(
       `stack_arg_count' = (LENGTH args1 -k)` by
          (simp[Abbr`stack_arg_count'`]) >>
       `stack_arg_count' <= stack_var_count` by
         fsrw_tac[][Abbr`stack_var_count`] >>
      ntac 2 $ qpat_x_assum `state_rel _ _ _ _ _ t5 _ _` mp_tac >>
      qmatch_goalsub_abbrev_tac `P` >>
      rpt $ qhdtm_x_assum `state_rel` mp_tac >>
      simp[AND_IMP_INTRO] >>
        disch_then (ASSUME_NAMED_TAC "old_state_rels") >>
      Q.UNABBREV_TAC `P` >>
      ntac 2 strip_tac >>
      fsrw_tac[][state_rel_def,Abbr`word_state`,Abbr`stack_state`]>>
      PURE_ONCE_REWRITE_TAC [dec_clock_def,
        stackSemTheory.dec_clock_def,
        call_env_def, push_env_def, env_to_list_def] >>
      fsrw_tac[][] >>
      conj_tac >- (simp[push_env_def,env_to_list_def] >>
        simp[FUN_EQ_THM]) >>
      conj_tac >- metis_tac [] >>
      conj_tac >- (cruft_tac >> rveq >>
                   `f'' <= LENGTH t.stack` by intLib.COOPER_TAC >>
                   qsuff_tac `t.stack_space <= LENGTH t.stack` >-
                     (qpat_x_assum `¬(t.stack_space < LENGTH args1 - k)`
                       mp_tac >>
                      qpat_x_assum `t4.stack_space = t.stack_space`
                        mp_tac >>
                      `LENGTH t4.stack = LENGTH t.stack` by rw[] >>
                      rw[SUB_RIGHT_SUB,SUB_RIGHT_ADD]) >>
                   intLib.COOPER_TAC) >>
      conj_tac >- (rev_full_simp_tac(srw_ss())[]) >>
      conj_tac >- (fsrw_tac[][Abbr`f''`]) >>
      conj_tac >- simp[wf_fromList2] >>
      conj_tac >- (cruft_tac >>
                  qhdtm_x_assum `stack_size_rel` mp_tac >>
                  fsrw_tac[][stack_size_rel_def,LET_THM] >>
                  simp[env_to_list_def,stack_size_eq,push_env_def] >>
                  strip_tac >> gvs[the_eqn] >>
                  strip_tac >> gvs[the_eqn] >>
                  strip_tac >> gvs[the_eqn] >>
                  simp[MAX_DEF]) >>
      fsrw_tac[][LET_THM]>>
      conj_tac >-
        (
         qpat_x_assum`stack_rel A B C D E G H (f'::lens)` mp_tac>>
         qpat_x_assum `DROP _ _ = DROP _ _` mp_tac >>
         fsrw_tac[][push_env_def,env_to_list_def,dec_clock_def]>>
         fsrw_tac[][DROP_DROP_EQ,LET_THM,ELIM_UNCURRY]>>
         simp[]) >>
      ntac 3 strip_tac>>
      rpt(WEAKEN_TAC (can (find_term (same_const ``the``)))) >>
      rpt(qpat_x_assum`!a b c. A ⇒ B` kall_tac)>>
      imp_res_tac (GSYM domain_lookup)>>
      imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
      fsrw_tac[][wordConvsTheory.post_alloc_conventions_def
        ,wordConvsTheory.call_arg_convention_def]>>
      `isPREFIX args1 (Loc l1 l2::xs)` by (
        qpat_x_assum`A=SOME(args1,_)` mp_tac>>
        Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
        simp[AllCaseEqs()] >> strip_tac >>
        rveq >> fsrw_tac[][IS_PREFIX_BUTLAST]) >>
      drule_all_then assume_tac lookup_fromList2_prefix>>
      rename1`nn DIV 2 < k`>>
      Cases_on`nn=0`>- (
        fsrw_tac[][lookup_fromList2,lookup_fromList]>>
        simp[FLOOKUP_UPDATE,stackSemTheory.set_var_def]) >>
      `lookup nn s.locals = SOME v` by (
        qpat_x_assum`args=A` SUBST_ALL_TAC>>
        imp_res_tac get_vars_fromList2_eq_cons)>>
      IF_CASES_TAC>- (
        `nn DIV 2 ≠ 0 ∧ nn DIV 2 ≠ k` by (
          fsrw_tac[][lookup_fromList2,lookup_fromList]>>
          full_simp_tac(srw_ss())[EVEN_EXISTS] >>
          rev_full_simp_tac(srw_ss())[] >>
          DECIDE_TAC) >>
        fsrw_tac[][FLOOKUP_UPDATE,stackSemTheory.set_var_def,
        stackSemTheory.get_var_def]>>
        metis_tac[])>>
       `f'' = stack_var_count + 1`
         by (
         `k ≤ LENGTH args1` by (
          fsrw_tac[][lookup_fromList2,lookup_fromList]
          \\ rpt(qpat_x_assum`nn DIV 2 < _`mp_tac)
          \\ qpat_x_assum`¬(nn DIV 2 < _)`mp_tac
          \\ rpt(pop_assum kall_tac)
          \\ decide_tac) >>
          fsrw_tac[] [lookup_fromList2,lookup_fromList,Abbr`f''`]>>
          Cases_on `stack_var_count = 0` >> fsrw_tac[][] >> simp[]) >>
       pop_assum SUBST_ALL_TAC >>
       DEP_REWRITE_TAC[LLOOKUP_TAKE] >> CONJ_TAC >- simp[] >>
       simp_tac(srw_ss()++ARITH_ss)[] >>
       simp[LLOOKUP_DROP] >>
       fsrw_tac[][LLOOKUP_THM,lookup_fromList2,lookup_fromList]>>
       simp_tac(srw_ss()++ARITH_ss)[] >>
       TIDY_ABBREVS >> fsrw_tac[][] >>
      `LENGTH args1 ≤ k+stack_var_count` by
        (qpat_x_assum`_ ≤ stack_var_count`mp_tac >>
        qpat_x_assum`stack_arg_count' = _`mp_tac >>
        rpt(pop_assum kall_tac) >> rw[] ) >>
      reverse conj_tac >- (
        qpat_x_assum`nn DIV 2 < _`mp_tac >>
        qpat_x_assum`nn DIV 2 < _`mp_tac >>
        pop_assum mp_tac >>
        rpt(pop_assum kall_tac) >> rw[] ) >>
      `stack_var_count +1 ≤ t.stack_space` by ( simp[] ) >>
      ntac 5 (pop_assum mp_tac) >>
      simp_tac(srw_ss()++ARITH_ss)[EL_DROP,EL_TAKE] >>
      rpt strip_tac >>
      first_x_assum(qspecl_then[`nn`,`v`] mp_tac)>>
      `k < nn DIV 2+1` by simp[]>>
      simp[EL_TAKE,GSYM AND_IMP_INTRO]>>
      disch_then (sym_sub_tac)>>
      simp[EL_DROP]>>
      strip_tac>>
      qpat_x_assum`!x. A ⇒ B = C` (mp_tac o GSYM) >>
      rpt(qpat_x_assum`!n.P` kall_tac)>>
      simp[EL_DROP]>>
      disch_then(qspec_then`LENGTH args1 - (nn DIV 2 +1)` mp_tac)>>
      simp[] >>
      rw[] >> fs[])>>
    Cases_on`evaluate(prog,word_state)`>>fsrw_tac[][]>>
    LABEL_X_ASSUM "IND" (fn x => mp_tac (CONJUNCT2 x) >>
    ASSUME_NAMED_TAC "IND" (CONJUNCT1 x)) >>
    simp[] >>
    disch_then (drule_at (Pos (el 2))) >>
    disch_then (drule_at Any)>>
    disch_then (drule_at Any)>>
    rename1`qres ≠ SOME Error ∧ _`>>
    Cases_on`qres = SOME Error`>>fsrw_tac[][]>>
    impl_tac>- (
      CONJ_ASM1_TAC>- (
        qpat_x_assum`A=SOME(args1,prog,ss)`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][state_rel_def,find_code_def]>>
        rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
      CONJ_TAC>- (
        qpat_x_assum`A=SOME(args1,prog,ss)`mp_tac>>
        Cases_on`dest`>>
        fsrw_tac[][state_rel_def,find_code_def]>>
        rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
      simp[CONJ_ASSOC] >>
      reverse CONJ_TAC >-
        (`EVEN (max_var prog)` by
            (ho_match_mp_tac max_var_intro>>
            fsrw_tac[][convs_def]>>
            match_mp_tac every_var_mono>>
            HINT_EXISTS_TAC>>fsrw_tac[][reg_allocTheory.is_phy_var_def
              ,EVEN_MOD2])>>
        unabbrev_all_tac>>fsrw_tac[][EVEN_EXISTS]>>
        rpt (pop_assum kall_tac)>>
        `m * 2 DIV 2 = m` by
          (Q.ISPECL_THEN[`2n`,`m`]assume_tac MULT_DIV>>fsrw_tac[][])>>
        fsrw_tac[][MULT_COMM,MAX_DEF]>>rw[]>>
        DECIDE_TAC)>>
      unabbrev_all_tac>>fsrw_tac[][]>>
      imp_res_tac evaluate_mono>>
      rpt (qpat_x_assum`!x. _` kall_tac)>>
      fsrw_tac[][]>>rw[]
      >- (imp_res_tac IS_PREFIX_LENGTH>>
        simp[])
      >- (imp_res_tac comp_IMP_isPREFIX>>
        fsrw_tac[][]>>
        metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
      >>
        old_drule find_code_IMP_get_labels
        \\ simp[get_labels_def]
        \\ metis_tac[loc_check_SUBSET,subspt_trans,SUBSET_TRANS])>>
    strip_tac>>
*)
    (*hit stack limit during function call*)
(* HOL4 ML code, not ported:
    Cases_on `OPTION_MAP compile_result qres ≠ res1` >> fsrw_tac[][]
    >- (
       rveq >> fsrw_tac[][] >>
       `!x. compile_result x ≠ Halt (Word 2w)`
          by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
        fsrw_tac[][] >>
        fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
        fsrw_tac[][stackSemTheory.set_var_def] >>
        qexists_tac `ck` >> full_simp_tac(srw_ss()++ARITH_ss)[] >>
        qpat_x_assum `_ = (res1,t1)` mp_tac >>
        simp[AC ADD_COMM ADD_ASSOC] >>
        disch_tac >>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
        imp_res_tac stackPropsTheory.evaluate_io_events_mono >>
        fs[] >>
        CONJ_TAC >-
            (qpat_x_assum `_ = (res,s1)` mp_tac >>
            simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
            imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
            imp_res_tac wordPropsTheory.pop_env_const>>
            fs[] >>
            metis_tac[IS_PREFIX_TRANS]) >>
        qpat_x_assum `_ = (res,s1)` mp_tac >>
        simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
        dxrule_then match_mp_tac evaluate_stack_limit_stack_max >>
        fs[] >>
        imp_res_tac wordPropsTheory.pop_env_const>>
        fs[]) >>
    fsrw_tac[][] >>
    Cases_on `res1 = SOME TimeOut` >> fs[]
    >- (
        `z = TimeOut` by (Cases_on `z` >> fsrw_tac[][]) >>
        fsrw_tac[][] >> rveq >>
        fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
        fsrw_tac[][stackSemTheory.set_var_def] >>
        qexists_tac `ck` >> full_simp_tac(srw_ss()++ARITH_ss)[] >>
        qpat_x_assum `_ = (res1,t1)` mp_tac >>
        simp[AC ADD_COMM ADD_ASSOC] >>
        rveq >> fs[]) >>
    qrefine `ck + clk'` >>
    drule_all $ GEN_ALL evaluate_add_clock >>
    fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
    fsrw_tac[][stackSemTheory.set_var_def] >>
    simp[AC ADD_COMM ADD_ASSOC] >>
    disch_then kall_tac >> fs[] >>
    fs[] >> gvs[] >>
    Cases_on `qres` >> fs[] >>
    (Cases_on `x`) >> fs[] >> rveq >> fs[]
    >> fs[DECIDE ``!a b.  (a :num) = b + a <=> b = 0``]
*)
    (*2 subgoals*)
(* HOL4 ML code, not ported:
    >- ((* Call_returning_no_handler_normal *)
    note_tac "No handler case, normal return">>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    ntac 3 (PURE_TOP_CASE_TAC >> fsrw_tac[][]) >>
    rveq >> fsrw_tac[][] >> strip_tac >>
    Q.ISPECL_THEN [`prog`,`word_state`] mp_tac evaluate_stack_swap>>
    simp[] >> simp[Abbr`word_state`] >>
    simp[push_env_def,ELIM_UNCURRY,s_key_eq_def2] >>
    strip_tac >>
    qpat_x_assum `!_. s_val_eq _ _ ==> _` kall_tac >>
    qpat_x_assum `s_frame_key_eq (StackFrame _ _ _ _) _` mp_tac >>
    simp[oneline s_frame_key_eq_def2] >> TOP_CASE_TAC >> fs[] >>
    strip_tac >> gvs[] >>
    qpat_x_assum `state_rel _ _ 0 0 _ _ _ _`
       (strip_assume_tac o SRULE[state_rel_def]) >>
    rfs[] >>
    drule_then assume_tac stack_rel_cons_LEN_NONE >>
    fs[] >>
    simp[evaluate_copy_ret_Seq'] >>
    simp[num_stack_ret_def] >>
    qmatch_goalsub_abbrev_tac `copy_ret_aux k f num_stack_ret'` >>
    Q.ISPECL_THEN [`k`,`f`,`num_stack_ret'`,`t1`] mp_tac
      evaluate_copy_ret_aux >>
    impl_tac >- (
      fs[Abbr`num_stack_ret'`] >>
      Cases_on `f' = 0` >>
      fsrw_tac[][state_rel_def]) >>
    strip_tac >>
    simp[Once stackSemTheory.evaluate_def,evaluate_copy_ret_aux_clock]
      >>
    `!n p ck. evaluate (SeqStackFree n p,t' with clock := ck) =
               evaluate (Seq (StackFree n) p,t' with clock := ck)` by
      (rw [] \\ match_mp_tac evaluate_SeqStackFree
      \\ fsrw_tac[] [state_rel_def] \\ decide_tac) \\
    rev_full_simp_tac(srw_ss())[] \\
    pop_assum kall_tac \\
    fsrw_tac[][stackSemTheory.evaluate_def] \\
    `LENGTH t'_stack' >= t1.stack_space + num_stack_ret'` by
      (fsrw_tac[][Abbr`num_stack_ret'`,state_rel_def] >>
      qpat_abbrev_tac `FREE = (LENGTH vs + 1 - k)` >>
      fs[]) \\
    fs[] \\ gvs[] \\
    (fn g =>
       qabbrev_tac `stack_state2 = ^((qexists_tac`0`
       \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t7)`) g
       |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g) >>
    `state_rel ac k f f' (set_vars vs l x) stack_state2 lens 0` by (
      ntac 2 $ qpat_x_assum `state_rel ac k _ _ _ t5 _ _` mp_tac >>
      qmatch_goalsub_abbrev_tac `P` >>
      rpt $ qhdtm_x_assum `state_rel` mp_tac >>
      rewrite_tac[AND_IMP_INTRO] >>
      disch_then (ASSUME_NAMED_TAC "old_state_rels") >>
      rpt $ qhdtm_x_assum `wordSem$evaluate` mp_tac >>
      rpt $ qhdtm_x_assum `stackSem$evaluate` mp_tac >>
      rewrite_tac[AND_IMP_INTRO] >>
      disch_then (ASSUME_NAMED_TAC "evaluate_stuff") >>
      Q.UNABBREV_TAC `P` >>
      rpt strip_tac >>
      fsrw_tac[][state_rel_def,set_vars_def,Abbr`stack_state2`]>>
      qhdtm_x_assum `pop_env` mp_tac >>
      simp[pop_env_def] >> strip_tac >> rveq >>
      simp[] >>
      CONJ_TAC>-
        metis_tac[evaluate_consts]>>
      CONJ_TAC >- (Cases_on `f' = 0` >> fs[]) >>
      CONJ_TAC>-
        simp[wf_alist_insert,wf_fromAList,wf_union]>>
      CONJ_TAC >- (
        rpt (qhdtm_x_assum `stack_size_rel` mp_tac) >>
        simp[stack_size_rel_def] >>
        rpt (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) >>
        first_x_assum old_drule >>
        simp[stack_size_eq] >>
        strip_tac >>
        CONJ_TAC >- (simp[]) >>
        full_simp_tac(srw_ss())[the_eqn] >>
        simp[]) >>
      CONJ_ASM1_TAC >- (
        old_drule stack_rel_DROP_NONE >>
        `f' + 1 = f` by (Cases_on `f' = 0` >> fsrw_tac[][]) >>
        POP_ASSUM SUBST_ALL_TAC >>
        simp[DROP_DROP_T]) >>
      rpt gen_tac >>
      simp[lookup_alist_insert] >>
      reverse TOP_CASE_TAC
      >- ( (*Arg from return*)
        strip_tac >> rveq >>
        `MEM (n'',v) (ZIP (vs,l))` by (
          DEP_REWRITE_TAC[ MEM_ALOOKUP ] >>
          simp[MAP_ZIP] >>
          fsrw_tac[][convs_def] >>
          qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x)
            >>
          simp[ALL_DISTINCT_GENLIST]) >>
        drule_then strip_assume_tac MEM_ZIP2 >>
        full_simp_tac(srw_ss())[] >>
        fsrw_tac[][convs_def] >>
        qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
        DEP_REWRITE_TAC[EL_GENLIST] >>
        fsrw_tac[][] >>
        simp[EVEN_DOUBLE] >>
        qpat_x_assum `!i. _ < LENGTH vs ==> _` old_drule >>
        strip_tac >> IF_CASES_TAC >>
        full_simp_tac(srw_ss())[] >>
        full_simp_tac(srw_ss())[stackSemTheory.get_var_def]
        >- (
          `n''' + 1 <> k` by DECIDE_TAC >>
          res_tac >> full_simp_tac(srw_ss())[]) >>
        DEP_REWRITE_TAC[LLOOKUP_TAKE] >>
        CONJ_ASM1_TAC >-
        (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
        simp[LLOOKUP_DROP] >>
        fsrw_tac[][Abbr`num_stack_ret'`] >>
        `LENGTH vs + 1 >= k` by
        (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
        simp[] >>
        `LENGTH vs + (t1.stack_space + 1) >= k` by
        (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
        reverse CONJ_ASM2_TAC >-
          (qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
          full_simp_tac(srw_ss())[wordLangTheory.max_var_def] >>
          `!a b c. max3 a b c = MAX a (MAX b c)`
            by simp[max3_def,MAX_DEF] >>
          fsrw_tac[][MAX_LIST_GENLIST_evens2,GSYM LEFT_ADD_DISTRIB] >>
          simp_tac(srw_ss())[LET_THM] >>
          strip_tac >> DECIDE_TAC) >>
        `f + k >= n''' + 2`
            by (
            Cases_on `f' = 0` >> full_simp_tac(srw_ss())[] >> simp[]) >>
        `f = f' + 1` by (Cases_on `f' = 0` >> full_simp_tac(srw_ss())[])
          >>
        full_simp_tac(srw_ss())[] >>
        qpat_x_assum `!_. _ ==> _ = _` mp_tac >>
        disch_then (qspec_then `LENGTH vs - (n''' + 1)` mp_tac) >>
        qpat_x_assum `LLOOKUP _ _ = SOME (EL _ _)` mp_tac >>
        disch_tac >>
        simp[EL_DROP] >>
        qpat_x_assum `LLOOKUP _ _ = SOME (EL _ _)` mp_tac >>
        full_simp_tac(srw_ss())[LLOOKUP_THM] >>
        simp[EL_DROP]) >>
      `~ MEM (n'') (vs)` by (
        imp_res_tac ALOOKUP_NONE >>
        pop_assum mp_tac >>
        simp[MAP_ZIP]) >>
      `n'' > 0 /\ EVEN n'' ==> (n'' DIV 2 >= LENGTH vs + 1)` by (
        fsrw_tac[][convs_def] >>
        qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
        fs[MEM_GENLIST] >>
        qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
        full_simp_tac(srw_ss())[wordLangTheory.max_var_def] >>
        `!a b c. max3 a b c = MAX a (MAX b c)`
         by simp[max3_def,MAX_DEF] >>
        pop_assum (full_simp_tac(srw_ss()) o single)>>
        fsrw_tac[][MAX_LIST_GENLIST_evens2,GSYM LEFT_ADD_DISTRIB] >>
        simp[] >>
        strip_tac >>
        simp[EVEN_EXISTS] >> strip_tac  >>
        first_x_assum (qspec_then `n'' DIV 2 - 1` mp_tac) >>
        impl_tac >- simp[DECIDE ``m = m - 1 + 1 <=> (m :num) > 0``] >>
        fs[GSYM GREATER_DEF,GSYM GREATER_EQ,SF DISJ_ss]) >>
      simp[lookup_union,lookup_fromAList,ALOOKUP_toAList] >>
*)
      (* GC cutset *)
(* HOL4 ML code, not ported:
      reverse TOP_CASE_TAC >- (
        strip_tac>> rveq >>
        rename1`EVEN nn`>>
        full_simp_tac(srw_ss())[] >>
        `MEM (nn,v) l0` by metis_tac[ALOOKUP_MEM]>>
        `MEM nn (MAP FST l0)`
          by (
           (pop_assum mp_tac) >>
           rpt (pop_assum $ K ALL_TAC) >>
           simp[MEM_MAP,EXISTS_PROD] >>
           metis_tac[]) >>
        `MEM nn (MAP FST (FST (env_to_list (SND envs) s.permute)))`
         by simp[] >>
        `MEM nn (MAP FST (toAList (SND envs)))`
          by (pop_assum mp_tac >>
            rpt (pop_assum $ K ALL_TAC) >>
            simp[MEM_MAP,env_to_list_def,PULL_EXISTS,
                 mem_list_rearrange,sort_MEM] >>
            METIS_TAC[]) >>
        `nn ∈ domain (SND envs)`
           by (fs[toAList_domain]) >>
        qhdtm_x_assum  `cut_envs`
          (strip_assume_tac o
            SRULE[AllCaseEqs(),cut_envs_def,cut_names_def]) >>
        rveq >> full_simp_tac(srw_ss())[domain_inter]  >>
        first_x_assum old_drule >>
        simp[] >> strip_tac >>
        fsrw_tac[][domain_lookup]>>
        full_simp_tac(srw_ss()++LET_ss)[] >>
        first_x_assum (qspecl_then [`nn`,`v'`]mp_tac)>>
        simp[] >> strip_tac >>
        fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
        qpat_abbrev_tac`ls = DROP A B`>>
        Cases_on`ls`>>simp[abs_stack_def]>>
        POP_ASSUM (ASSUME_NAMED_TAC "DROP_NOT_NIL") >>
        DISCH_THEN (strip_assume_tac o SRULE[AllCaseEqs()]) >>
        rveq >> fs[] >>
        ntac 4 $ qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
        rveq>>simp[stack_rel_aux_def]>>
        ntac 4 strip_tac>>
        old_drule filter_bitmap_MEM>>
        disch_then (qspecl_then [`nn DIV 2,v`] mp_tac) >>
        impl_tac >- (
         simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
         METIS_TAC[]) >>
        disch_then (mp_tac o (MATCH_MP MEM_index_list_EL))>>
        strip_tac >> rveq >>
        `t' = TL (DROP (num_stack_ret' + t1.stack_space) t1.stack)`
        by (LABEL_X_ASSUM "DROP_NOT_NIL" assume_tac >> TIDY_ABBREVS >>
          simp[]) >>
        LABEL_X_ASSUM "DROP_NOT_NIL" (assume_tac o
          SRULE[markerTheory.Abbrev_def]) >>
        reverse (fs[])
        >- full_simp_tac(srw_ss())[LLOOKUP_THM,Excl "SUB_RIGHT_LESS",
           LENGTH_TAKE_EQ_MIN] >>
        simp[LLOOKUP_THM,Excl"SUB_RIGHT_LESS"] >>
        DEP_REWRITE_TAC[EL_TAKE,EL_DROP,GSYM EL] >>
        rewrite_tac[CONJ_ASSOC] >>
        CONJ_ASM1_TAC >- (
           full_simp_tac(srw_ss())[LLOOKUP_THM,Excl "SUB_RIGHT_LESS",
           LENGTH_TAKE_EQ_MIN] >>
           fs[MIN_DEF,Excl "SUB_RIGHT_LESS"]) >>
        qmatch_goalsub_abbrev_tac `EL A _ = EL B _` >>
        `B = A` by
          (cruft_tac >>
          full_simp_tac(srw_ss())[Abbr`A`,Abbr`B`,Abbr`num_stack_ret'`]
            >>
          Cases_on `f = 0` >> full_simp_tac(srw_ss())[] >>
          simp[]) >>
        pop_assum (SUBST_TAC o single) >>
        simp[Abbr`A`] >>
        qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` kall_tac >>
        qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` mp_tac >>
        disch_then (qspec_then `f + k - (nn DIV 2 + 1)` mp_tac) >>
        impl_tac >- (
          `nn > 0`
             by (fs[EVEN_EXISTS] >>
             rveq >>
             fs[]) >>
          fs[Abbr`num_stack_ret'`]) >>
        simp[EL_DROP])>>
*)
      (* NON-GC cutset *)
(* HOL4 ML code, not ported:
      strip_tac >>
      qhdtm_x_assum  `cut_envs`
      (strip_assume_tac o
        SRULE[AllCaseEqs(),cut_envs_def,cut_names_def]) >>
      rveq >> full_simp_tac(srw_ss())[domain_inter]  >>
      strip_tac >>
      rename [`EVEN nn`] >>
      `nn ∈ domain (inter s.locals (FST live))`
         by (fs[domain_lookup]) >>
      `nn ∈ domain (FST live) ∧ nn ∈ domain s.locals` by (
          full_simp_tac(srw_ss())[domain_inter]) >>
      fsrw_tac[][domain_lookup]>>
      first_x_assum (qspecl_then [`nn`,`v''`]mp_tac)>>
      simp[]>>
      strip_tac>>
      rveq >> fs[] >>
      fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
      qpat_abbrev_tac`ls = DROP A B`>>
      Cases_on`ls`>>simp[abs_stack_def]>>
      POP_ASSUM (ASSUME_NAMED_TAC "DROP_NOT_NIL") >>
      DISCH_THEN (strip_assume_tac o SRULE[AllCaseEqs()]) >>
      rveq >> fs[] >>
      ntac 4 $ qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
      rveq>>simp[stack_rel_aux_def]>>
      ntac 4 strip_tac>>
      PRED_ASSUM is_forall mp_tac >>
      simp[ALOOKUP_toAList] >>
      disch_then (qspec_then `nn` mp_tac) >>
      simp[] >>
      res_tac >> fs[] >>
      simp[ALOOKUP_index_list] >>
      `t' = TL (DROP (num_stack_ret' + t1.stack_space) t1.stack)`
         by (LABEL_X_ASSUM "DROP_NOT_NIL" assume_tac >> TIDY_ABBREVS >>
           simp[]) >>
      LABEL_X_ASSUM "DROP_NOT_NIL" (assume_tac o
        SRULE[markerTheory.Abbrev_def]) >>
      fs[] >>
      simp[LLOOKUP_TAKE,TL_DROP_SUC,DROP_SUC] >>
      simp[Once LLOOKUP_DROP] >>
      simp[] >>
      strip_tac>>
      pop_assum mp_tac>>
      ntac 2 (pop_assum kall_tac)>>
      qmatch_goalsub_abbrev_tac `LLOOKUP (DROP _ _) A = _ ==> LLOOKUP
        (DROP _ _) B = _` >>
      `A = B` by (
        fs[Abbr`A`,Abbr`B`] >>
        `LENGTH bits = f - 1`
          by (Cases_on `f = 0` >> fs[]) >>
        fs[]) >>
      simp[Abbr`A`,Abbr`B`] >>
      simp[LLOOKUP_THM] >>
      disch_then sym_sub_tac >>
      qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` kall_tac >>
      qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` irule >>
      simp[Abbr`num_stack_ret'`] >>
      Cases_on `f = 0` >> fsrw_tac[][] >>
      rveq >>
      fsrw_tac[][EVEN_EXISTS] >>
      rveq >>
      fs[]) >>
    LABEL_X_ASSUM "IND" mp_tac \\ simp[] \\
    disch_then old_drule \\
    disch_then (drule_at (Pos (el 3))) \\
    impl_tac >- (
      fsrw_tac[][convs_def,Abbr`stack_state2`]>>
      simp[CONJ_ASSOC]>>
      REVERSE CONJ_TAC
      >- (
        qpat_x_assum`A<2 * _ + 2 * _:num` mp_tac>>
        `!a b c. max3 a b c = MAX a (MAX b c)` by simp[MAX_DEF,max3_def]
          >>
        simp[wordLangTheory.max_var_def])>>
      REVERSE CONJ_TAC
      >- (
        fs [comp_def,get_labels_def,get_labels_copy_ret] \\
        imp_res_tac evaluate_mono \\ fs[] \\
        rpt (qpat_x_assum `subspt _ _` mp_tac) \\
        rpt (qpat_x_assum `get_labels _  ⊆ _` mp_tac) \\
        rpt (pop_assum kall_tac) \\
        metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans]) >>
      rw[]
      >- (
        imp_res_tac wLive_LENGTH>>
        fs[])
      >- (
        imp_res_tac wLive_LENGTH>>
        rfs[]>>
        imp_res_tac evaluate_mono >>
        fs[]>>
        imp_res_tac IS_PREFIX_LENGTH>>
        fs[])
      >> (
        imp_res_tac wLive_LENGTH>>
        rfs[]>>
        imp_res_tac evaluate_mono >>
        fs[]>>
        metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]))>>
    rw[]>>
    `x.handler = s.handler`
      by (qhdtm_x_assum `pop_env` mp_tac >>
          rw[pop_env_def] >> simp[]) >>
    fs[] >>
    qexists_tac`ck'`>>
    fsrw_tac[][Abbr`stack_state2`])
    >> note_tac "No handler case, exception">>
    qexists_tac`0`>> fs[]>>
    `word_state.handler = s.handler` by
      simp[Abbr`word_state`,call_env_def,push_env_def,env_to_list_def
        ,dec_clock_def]>>
    imp_res_tac state_rel_IMP_LENGTH>>
    Q.ISPECL_THEN [`prog`,`word_state`] assume_tac
      evaluate_stack_swap>>rfs[]>>
    fs[push_env_def,env_to_list_def,LET_THM]>>
    `s.handler+1 ≤ LENGTH lens` by
*)
      (*because it can't be the top frame of word_state, which is NONE*)
(* HOL4 ML code, not ported:
      (CCONTR_TAC>>
      `s.handler+1 =LENGTH s.stack+1` by DECIDE_TAC>>
      fs[Abbr`word_state`,call_env_def,dec_clock_def,LASTN_CONS]>>
      fs[LASTN_CONS_ID,GSYM ADD1])>>
    fs[LASTN_CONS] >>
    asm_exists_tac >> fs[]
)
  >- (
  note_tac "Handler case">>
  rename1 `push_env _ (SOME handler)` >>
  fs[UNCURRY_EQ,TypeBase.case_eq_of ``:'a # 'b``] >> rveq >>
  simp[Ntimes stackSemTheory.evaluate_def 2] >>
  imp_res_tac compile_prog_stack_size >>
  qhdtm_x_assum `compile_prog` mp_tac >>
  fsrw_tac[][compile_prog_def] >>
  LET_ELIM_TAC >> fs[] >> rveq >>
*)
  (*Space to store handler case*)
(* HOL4 ML code, not ported:
  reverse(Cases_on`3 ≤ t5.stack_space`) >- (
    qpat_x_assum `_.stack_space = _.stack_space` kall_tac >>
    qpat_x_assum `LENGTH _.stack = LENGTH _.stack` kall_tac >>
    simp[PushHandler_F,stackSemTheory.evaluate_def,uncurry_case_rand
      ``:bool``] >>
    `t5.use_stack` by fsrw_tac[][state_rel_def] >>
    `!x. compile_result x ≠ Halt (Word 2w)`
        by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
    fsrw_tac[][] >>
    `t5.ffi = s.ffi` by fsrw_tac[][state_rel_def] >>
    `the (s.stack_limit + 1)
          (call_env args1 ss (push_env envs (SOME
            (handle_var,handle_code,h1,h2))
          s)).stack_max >
        s.stack_limit`
       by (simp[call_env_def,the_eqn] >>
          PURE_TOP_CASE_TAC >- simp[] >>
          fsrw_tac[][state_rel_def,stack_size_rel_def,GREATER_DEF] >>
          rveq >>
          fsrw_tac[][push_env_def,ELIM_UNCURRY,LET_DEF,stack_size_eq] >>
          rveq >> fsrw_tac[][the_eqn] >>
          rveq >> fsrw_tac[][] >>
          rfs[]) >>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    simp[Once $ AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    CONJ_TAC >-(
            pop_assum mp_tac >>
            simp[AllCaseEqs()] >>
            strip_tac >> rveq >> fs[] >>
            imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
            imp_res_tac wordPropsTheory.pop_env_const >>
            fsrw_tac[][] >>
            rpt (qpat_x_assum `_ ≼ _` mp_tac) >>
            rpt (pop_assum kall_tac) >>
            METIS_TAC[IS_PREFIX_TRANS]) >>
    pop_assum mp_tac >>
    simp[AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    imp_res_tac wordPropsTheory.pop_env_const >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def] >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def])  >>
*)
  (* Needs to go in wordSem?*)
(* HOL4 ML code, not ported:
  drule_then old_drule (GEN_ALL evaluate_PushHandler)>>
  disch_then(qspecl_then[`h2`,`h1`,`handle_code`,`handle_var`,`f`]
    mp_tac)>>
  impl_tac THEN1 (
   fs [comp_def,get_labels_def] >>
   imp_res_tac evaluate_mono>>
   `loc_check t.code ⊆ loc_check t5.code` by
     metis_tac[subspt_trans,SUBSET_DEF,loc_check_SUBSET]>>
    fs[SUBSET_DEF,FORALL_PROD,IN_DEF]
   )>>
  strip_tac>>
  simp[evaluate_PushHandler_clock,Once stackSemTheory.evaluate_def]>>
  simp[Once stackSemTheory.evaluate_def,
  StackHandlerArgs_F,StackArgs_def,evaluate_stack_move_seq]>>
  simp[stackSemTheory.evaluate_def]>>
  simp[uncurry_case_rand ``:bool``] >>
  `t'.use_stack` by fsrw_tac[][state_rel_def]>>fsrw_tac[][]>>
  `Abbrev (stack_arg_count' = stack_arg_count dest' (LENGTH args + 1)
    k)` by(
    simp[Abbr`stack_arg_count'`,markerTheory.Abbrev_def
      ,stack_arg_count_def] >>
    `LENGTH args = LENGTH xs`
       by (imp_res_tac get_vars_length_lemma >> fsrw_tac[][]) >>
    pop_assum mp_tac >>
    qhdtm_x_assum `call_dest` mp_tac >>
    qpat_x_assum `¬bad_dest_args _ _` mp_tac >>
    qhdtm_x_assum `wordSem$find_code` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[oneline call_dest_def,AllCaseEqs()] >>
    rpt strip_tac >> fs[bad_dest_args_def] >>
    gvs[UNCURRY_EQ] >>
    qhdtm_x_assum `wordSem$find_code` mp_tac >>
    simp[wordSemTheory.find_code_def,add_ret_loc_def,AllCaseEqs()] >>
    strip_tac >> fs[] >> rveq >>
    fs[LENGTH_FRONT,ADD1]) >>
  fs[] >>
*)
  (*Space to store args*)
(* HOL4 ML code, not ported:
  Cases_on`t'.stack_space < stack_arg_count'`
  >- (
    `!x. compile_result x ≠ Halt (Word 2w)`
      by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
    fsrw_tac[][] >>
    `t'.ffi = s.ffi` by fsrw_tac[][state_rel_def] >>
    `stack_arg_count' = LENGTH args1 − k` by
    fsrw_tac[][Abbr`stack_arg_count'`] >>
    `the (s.stack_limit + 1)
      (call_env args1 ss (push_env envs (SOME
        (handle_var,handle_code,h1,h2))
      s)).stack_max >
    s.stack_limit`
      by (simp[call_env_def,the_eqn] >>
      PURE_TOP_CASE_TAC >- simp[] >>
      fsrw_tac[][state_rel_def,stack_size_rel_def,GREATER_DEF] >>
      rveq >>
      fsrw_tac[][push_env_def,ELIM_UNCURRY,LET_DEF,stack_size_eq] >>
      rveq >> fsrw_tac[][the_eqn] >>
      rveq >> fsrw_tac[][] >>
      rfs[]) >>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    simp[Once $ AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    CONJ_TAC >-(
        pop_assum mp_tac >>
        simp[AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
        imp_res_tac wordPropsTheory.pop_env_const >>
        fsrw_tac[][] >>
        rpt (qpat_x_assum `_ ≼ _` mp_tac) >>
        rpt (pop_assum kall_tac) >>
        METIS_TAC[IS_PREFIX_TRANS]) >>
    pop_assum mp_tac >>
    simp[AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    imp_res_tac wordPropsTheory.pop_env_const >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def] >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def])  >>
  simp[]>>fsrw_tac[][]>>
  qabbrev_tac`t6 = t' with stack_space :=t'.stack_space -
    stack_arg_count'`>>
  `!ck. t' with <|stack_space:=t'.stack_space - stack_arg_count';
    clock:=ck+t.clock|> = t6 with clock:=ck+t.clock` by
      simp[stackSemTheory.state_component_equality,Abbr`t6`]>>
  simp[evaluate_stack_move_clock]>>
  Q.ISPECL_THEN [`stack_arg_count'`,`0n`,`t6`,`f+3`] mp_tac
    evaluate_stack_move>>
  impl_tac >- (
    simp[Abbr`t6`] >>
    fsrw_tac[][state_rel_def] >>
    qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
    pure_rewrite_tac[wordLangTheory.max_var_def] >>
    `!x y z. max3 x y z = MAX x (MAX y z)`
      by fs[MAX_DEF,max3_def] >>
    pop_assum (pure_rewrite_tac o single) >>
    fsrw_tac[][LET_DEF] >> strip_tac >>
    fsrw_tac[][convs_def]>>
    qpat_x_assum`args = A` SUBST_ALL_TAC>>
    fsrw_tac[][MAX_LIST_GENLIST_evens2]>>
    rveq >>
    Cases_on `f' = 0` >> fsrw_tac[][] >>
    Cases_on `dest'` >>
    fsrw_tac[][stack_arg_count_def] >>
    fsrw_tac[][Abbr`stack_arg_count'`] >>
*)
    (*TODO this is very slow*)
(* HOL4 ML code, not ported:
    gvs[]) >>
  strip_tac>> rfs[evaluate_stack_move_clock] >>
  `find_code dest' (t'_regs \\0) t6.code = find_code dest' t4.regs
    t4.code` by (
    `subspt t4.code t6.code` by (
       fs[stackSemTheory.state_component_equality]>>
       metis_tac[evaluate_mono])>>
    Cases_on`dest'`>>fsrw_tac[][stackSemTheory.find_code_def]>>
    qpat_x_assum`A=SOME stack_prog` mp_tac
    >- metis_tac[subspt_def,domain_lookup]>>
    qpat_x_assum`A=(q0,INR y)` mp_tac>>
    Cases_on`dest`>>simp[call_dest_def]>>
    IF_CASES_TAC>>simp[]>>
    simp[wReg2_def]>>IF_CASES_TAC>>fsrw_tac[][]
    >- (
      `LAST args DIV 2≠ 0 ∧ LAST args DIV 2 ≠ k` by (
        fs[convs_def]>>
        qpat_x_assum`args = A` SUBST_ALL_TAC>>
        `LENGTH args <> 0` by (strip_tac \\ fs[]) >>
        old_drule LAST_GENLIST_evens>>
        LET_ELIM_TAC>>simp[]>>
        Cases_on`reg`>>fs[]>>
        rename1`SUC xx DIV _ ≠ _`>>
        Cases_on`xx`>>fs[]>>
        simp[ADD_DIV_RWT,ADD1])>>
      strip_tac>>rveq>>
      simp[DOMSUB_FLOOKUP_THM]>>
      fs[stackSemTheory.get_var_def,Abbr`t6`]>>
      qpat_x_assum`subspt _ _` mp_tac>>
      rpt (pop_assum kall_tac)>>
      EVERY_CASE_TAC>>rw[]>>
      metis_tac[subspt_def,domain_lookup])
    >- (
      strip_tac>>rveq>>
      simp[DOMSUB_FLOOKUP_THM]>>
      fsrw_tac[][stackSemTheory.get_var_def,Abbr`t6`,FLOOKUP_UPDATE]>>
      qpat_x_assum`subspt _ _` mp_tac>>
      rpt (pop_assum kall_tac)>>
      every_case_tac>>fs[subspt_def]>>
      metis_tac[domain_lookup]))>>
  pop_assum SUBST_ALL_TAC >>
  fsrw_tac[][] >>
  `t.clock = s.clock` by fs[state_rel_def] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `_ = (res,s1)` mp_tac >>
  IF_CASES_TAC>- (
    strip_tac >> fsrw_tac[][] >>
    rveq >> qexists_tac`0`>>
    simp[] >>
    fsrw_tac[][Abbr`t6`,state_rel_def]) >>
  fsrw_tac[][] >>
  rpt $ (qpat_x_assum `!_. evaluate (_,_ with clock := _) = _` kall_tac)
    >>
  strip_tac >>
  simp[stackSemTheory.evaluate_def]>>
  `t6.use_stack` by fs[state_rel_def,Abbr`t6`] >>
  `stack_arg_count' <= f''`
    by  (`stack_arg_count' <= stack_var_count`
              by (simp[Abbr `stack_var_count`]) \\
         `stack_var_count <= f''`
              by(simp[Abbr`f''`]) \\
         simp[]) >>
  fs[SF CONJ_ss,Abbr`t6`] >>
  simp[uncurry_case_rand ``:bool``] >>
*)
  (*space for the function local var*)
(* HOL4 ML code, not ported:
  PURE_TOP_CASE_TAC
  >- ( (* Hit stack limit case *)
    `!x. compile_result x ≠ Halt (Word 2w)`
       by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
    fsrw_tac[][] >>
    `t'.ffi = s.ffi` by fsrw_tac[][state_rel_def] >>
    `stack_arg_count' = LENGTH args1 − k` by
    fsrw_tac[][Abbr`stack_arg_count'`] >>
    `the (s.stack_limit + 1)
      (call_env args1 ss (push_env envs (SOME
        (handle_var,handle_code,h1,h2))
      s)).stack_max >
    s.stack_limit`
      by (simp[call_env_def,the_eqn] >>
      PURE_TOP_CASE_TAC >- simp[] >>
      fsrw_tac[][state_rel_def,stack_size_rel_def,GREATER_DEF] >>
      rveq >>
      fsrw_tac[][push_env_def,ELIM_UNCURRY,LET_DEF,stack_size_eq] >>
      rveq >> fsrw_tac[][the_eqn] >>
      rveq >> fsrw_tac[][] >>
      rfs[]) >>
    qpat_x_assum `_ = (res,s1)` mp_tac >>
    simp[Once $ AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    CONJ_TAC >-(
        pop_assum mp_tac >>
        simp[AllCaseEqs()] >>
        strip_tac >> rveq >> fs[] >>
        imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
        imp_res_tac wordPropsTheory.pop_env_const >>
        fsrw_tac[][] >>
        rpt (qpat_x_assum `_ ≼ _` mp_tac) >>
        rpt (pop_assum kall_tac) >>
        METIS_TAC[IS_PREFIX_TRANS]) >>
    pop_assum mp_tac >>
    simp[AllCaseEqs()] >>
    strip_tac >> rveq >> fs[] >>
    imp_res_tac wordPropsTheory.pop_env_const >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def] >>
    drule_then match_mp_tac evaluate_stack_limit_stack_max >>
    simp[dec_clock_def])  >>
  fsrw_tac[][] >>
  simp[]>>
  qpat_x_assum `_ = (res,s1)` mp_tac >>
  qpat_abbrev_tac`word_state = call_env args1 ss st`>>
  strip_tac >>
*)
  (*This looks hacky but it works*)
(* HOL4 ML code, not ported:
  (fn g =>
       qabbrev_tac `stack_state = ^((qexists_tac`0`
       \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t7)`) g
       |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g) >>
  `state_rel ac k f'' stack_var_count word_state stack_state (f'::lens)
    0` by (
    `stack_arg_count' = (LENGTH args1 -k)` by
       (simp[Abbr`stack_arg_count'`]) >>
    `stack_arg_count' <= stack_var_count` by
      fsrw_tac[][Abbr`stack_var_count`] >>
    ntac 2 $ qpat_x_assum `state_rel _ _ _ _ _ t5 _ _` mp_tac >>
    qpat_x_assum `state_rel _ _ _ _ _ t' _ _` mp_tac >>
    qmatch_goalsub_abbrev_tac `P` >>
    rpt $ qhdtm_x_assum `state_rel` mp_tac >>
    simp[AND_IMP_INTRO] >>
      disch_then (ASSUME_NAMED_TAC "old_state_rels") >>
    Q.UNABBREV_TAC `P` >>
    ntac 3 strip_tac >>
    qpat_x_assum `t' = _` mp_tac >>
    qmatch_goalsub_abbrev_tac `t' = _ with <|regs := t'__regs;
       store := t'__store; stack := t'__stack;
       stack_space := t'__stack_space|> ` >>
    disch_tac >> rveq >>
    fs[] >>
    fsrw_tac[][state_rel_def,Abbr`word_state`,Abbr`stack_state`]>>
    PURE_ONCE_REWRITE_TAC [dec_clock_def, stackSemTheory.dec_clock_def,
      call_env_def, push_env_def, env_to_list_def] >>
    fsrw_tac[][EVAL ``(stackSem$set_var v x s).clock``] >>
    conj_tac >- (simp[push_env_def,env_to_list_def] >> simp[FUN_EQ_THM])
      >>
    conj_tac >- metis_tac [] >>
    conj_tac >- (`t'__stack_space = t.stack_space - 3` by simp[] >>
                 rveq >>cruft_tac >> rveq >>
                 `f'' <= LENGTH t.stack` by intLib.COOPER_TAC >>
                  simp[]) >>
    conj_tac >- (rev_full_simp_tac(srw_ss())[]) >>
    conj_tac >- (fsrw_tac[][Abbr`f''`]) >>
    conj_tac >- simp[wf_fromList2] >>
    conj_tac >- (
                `t'__stack_space = t.stack_space - 3` by simp[] >>
                 rveq >> cruft_tac >>
                qhdtm_x_assum `stack_size_rel` mp_tac >>
                fsrw_tac[][stack_size_rel_def,LET_THM] >>
                simp[env_to_list_def,stack_size_eq,push_env_def] >>
                strip_tac >> gvs[the_eqn] >>
                strip_tac >> gvs[the_eqn] >>
                strip_tac >> gvs[the_eqn] >>
                simp[MAX_DEF]) >>
    fsrw_tac[][LET_THM]>>
    conj_tac >- (
       `t'__stack_space = t.stack_space - 3` by simp[] >>
       rveq >>
       qpat_x_assum`stack_rel A B C D E G H (f'::lens)` kall_tac >>
       qpat_x_assum`stack_rel A B C D E G H (f'::lens)` mp_tac>>
       qpat_x_assum `DROP _ _ = DROP _ _` mp_tac >>
       fsrw_tac[][push_env_def,env_to_list_def,dec_clock_def]>>
       fsrw_tac[][DROP_DROP_EQ,LET_THM,ELIM_UNCURRY]>>
       simp[]) >>
    ntac 3 strip_tac>>
    rpt(WEAKEN_TAC (can (find_term (same_const ``the``)))) >>
    rpt(qpat_x_assum`!a b c. A ⇒ B` kall_tac)>>
    imp_res_tac (GSYM domain_lookup)>>
    imp_res_tac EVEN_fromList2>>fsrw_tac[][]>>
    fsrw_tac[][wordConvsTheory.post_alloc_conventions_def
      ,wordConvsTheory.call_arg_convention_def]>>
    `isPREFIX args1 (Loc l1 l2::xs)` by (
      qpat_x_assum`A=SOME(args1,_)` mp_tac>>
      Cases_on`dest`>>fsrw_tac[][find_code_def,add_ret_loc_def]>>
      simp[AllCaseEqs()] >> strip_tac >>
      rveq >> fsrw_tac[][IS_PREFIX_BUTLAST]) >>
    drule_all_then assume_tac lookup_fromList2_prefix>>
    rename1`nn DIV 2 < k`>>
    Cases_on`nn=0`>- (
      fsrw_tac[][lookup_fromList2,lookup_fromList]>>
      simp[FLOOKUP_UPDATE,stackSemTheory.set_var_def]) >>
    `lookup nn s.locals = SOME v` by (
      qpat_x_assum`args=A` SUBST_ALL_TAC>>
      imp_res_tac get_vars_fromList2_eq_cons)>>
    IF_CASES_TAC>- (
      `nn DIV 2 ≠ 0 ∧ nn DIV 2 ≠ k` by (
        fsrw_tac[][lookup_fromList2,lookup_fromList]>>
        full_simp_tac(srw_ss())[EVEN_EXISTS] >>
        rev_full_simp_tac(srw_ss())[] >>
        DECIDE_TAC) >>
      fsrw_tac[][FLOOKUP_UPDATE,stackSemTheory.set_var_def,
      stackSemTheory.get_var_def]>>
      metis_tac[])>>
    `f'' = stack_var_count + 1` by (
      `k ≤ LENGTH args1` by (
       fsrw_tac[][lookup_fromList2,lookup_fromList]
       \\ rpt(qpat_x_assum`nn DIV 2 < _`mp_tac)
       \\ qpat_x_assum`¬(nn DIV 2 < _)`mp_tac
       \\ rpt(pop_assum kall_tac)
       \\ decide_tac) >>
       fsrw_tac[] [lookup_fromList2,lookup_fromList,Abbr`f''`]>>
       Cases_on `stack_var_count = 0` >> fsrw_tac[][] >> simp[]) >>
    pop_assum SUBST_ALL_TAC >>
    DEP_REWRITE_TAC[LLOOKUP_TAKE] >> CONJ_TAC >- simp[] >>
    simp_tac(srw_ss()++ARITH_ss)[] >>
    simp[LLOOKUP_DROP] >>
    fsrw_tac[][LLOOKUP_THM,lookup_fromList2,lookup_fromList]>>
    simp_tac(srw_ss()++ARITH_ss)[] >>
    TIDY_ABBREVS >> fsrw_tac[][] >>
    `t'__stack_space = t.stack_space - 3` by simp[]  >>
    rveq  >> fsrw_tac[][] >>
    simp[] >>
    first_x_assum(drule)>>
    simp[EL_TAKE,EL_DROP] >>
    qpat_x_assum`!x. A ⇒  EL _ _  = EL _ _` (mp_tac o GSYM) >>
    disch_then (qspec_then `LENGTH args1- (nn DIV 2 + 1)` mp_tac) >>
    qpat_x_assum`!x. A ⇒  EL _ _  = EL _ _` (mp_tac) >>
    disch_then (qspec_then `f + k - (nn DIV 2 + 1)` mp_tac) >>
    simp[EL_DROP] >>
    rpt strip_tac >>
    Cases_on `f=0` >> fsrw_tac[][] >>
    rveq >> fsrw_tac[][] >>
    simp[] >>
    rpt $ qpat_x_assum `EL _ _ = EL _ _` mp_tac >>
    simp[]) >>
  Cases_on`evaluate(prog,word_state)`>>fsrw_tac[][]>>
  LABEL_X_ASSUM "IND" (fn x => (case CONJUNCTS x of [x1,x2,x3,x4] =>
                      mp_tac x3 >>
                      ASSUME_NAMED_TAC "Result_IND" x1 >>
                      ASSUME_NAMED_TAC "Exception_IND" x2)) >>
  simp[] >>
  disch_then (drule_at (Pos (el 2))) >>
  disch_then (drule_at Any)>>
  disch_then (drule_at Any)>>
  rename1`qres ≠ SOME Error ∧ _`>>
  Cases_on`qres = SOME Error`>>fsrw_tac[][]>>
  impl_tac>- (
    CONJ_ASM1_TAC>- (
      qpat_x_assum`A=SOME(args1,prog,ss)`mp_tac>>
      Cases_on`dest`>>
      fsrw_tac[][state_rel_def,find_code_def]>>
      rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
    CONJ_TAC>- (
      qpat_x_assum`A=SOME(args1,prog,ss)`mp_tac>>
      Cases_on`dest`>>
      fsrw_tac[][state_rel_def,find_code_def]>>
      rpt TOP_CASE_TAC>>rw[]>>metis_tac[])>>
    simp[CONJ_ASSOC] >>
    reverse CONJ_TAC >-
      (`EVEN (max_var prog)` by
          (ho_match_mp_tac max_var_intro>>
          fsrw_tac[][convs_def]>>
          match_mp_tac every_var_mono>>
          HINT_EXISTS_TAC>>fsrw_tac[][reg_allocTheory.is_phy_var_def
            ,EVEN_MOD2])>>
      unabbrev_all_tac>>fsrw_tac[][EVEN_EXISTS]>>
      rpt (pop_assum kall_tac)>>
      `m * 2 DIV 2 = m` by
        (Q.ISPECL_THEN[`2n`,`m`]assume_tac MULT_DIV>>fsrw_tac[][])>>
      fsrw_tac[][MULT_COMM,MAX_DEF]>>rw[]>>
      DECIDE_TAC)>>
    unabbrev_all_tac>>fsrw_tac[][]>>
    imp_res_tac evaluate_mono>>
    rpt (qpat_x_assum`!x. _` kall_tac)>>
    fsrw_tac[][]>>rw[]
    >- (imp_res_tac IS_PREFIX_LENGTH>>
      simp[])
    >- (imp_res_tac comp_IMP_isPREFIX>>
      fsrw_tac[][]>>
      metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP])
    >>
      old_drule find_code_IMP_get_labels
      \\ simp[get_labels_def]
      \\ metis_tac[loc_check_SUBSET,subspt_trans,SUBSET_TRANS])>>
  strip_tac>>
*)
  (*hit stack limit during function call*)
(* HOL4 ML code, not ported:
  Cases_on `OPTION_MAP compile_result qres ≠ res1` >> fsrw_tac[][]
  >- (
    rveq >> fsrw_tac[][] >>
    `!x. compile_result x ≠ Halt (Word 2w)`
       by fsrw_tac[][compile_result_NOT_2,state_rel_def] >>
     fsrw_tac[][] >>
     fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
     fsrw_tac[][stackSemTheory.set_var_def] >>
     qexists_tac `ck` >> full_simp_tac(srw_ss()++ARITH_ss)[] >>
     qpat_x_assum `_ = (res1,t1)` mp_tac >>
     simp[AC ADD_COMM ADD_ASSOC] >>
     disch_tac >>
     imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
     imp_res_tac stackPropsTheory.evaluate_io_events_mono >>
     fs[] >>
     CONJ_TAC >-
         (qpat_x_assum `_ = (res,s1)` mp_tac >>
         simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
         imp_res_tac wordPropsTheory.evaluate_io_events_mono >>
         imp_res_tac wordPropsTheory.pop_env_const>>
         fs[] >>
         metis_tac[IS_PREFIX_TRANS]) >>
     qpat_x_assum `_ = (res,s1)` mp_tac >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
     dxrule_then match_mp_tac evaluate_stack_limit_stack_max >>
     fs[] >>
     imp_res_tac wordPropsTheory.pop_env_const>>
     fs[]) >>
  fsrw_tac[][] >>
  Cases_on `res1 = SOME TimeOut` >> fs[]
  >- (
    `z = TimeOut` by (Cases_on `z` >> fsrw_tac[][]) >>
    fsrw_tac[][] >> rveq >>
    fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
    fsrw_tac[][stackSemTheory.set_var_def] >>
    qexists_tac `ck` >> full_simp_tac(srw_ss()++ARITH_ss)[] >>
    qpat_x_assum `_ = (res1,t1)` mp_tac >>
    simp[AC ADD_COMM ADD_ASSOC] >>
    rveq >> fs[]) >>
  qrefine `ck + clk'` >>
  drule_all $ GEN_ALL evaluate_add_clock >>
  fsrw_tac[][Abbr`stack_state`,stackSemTheory.dec_clock_def] >>
  fsrw_tac[][stackSemTheory.set_var_def] >>
  simp[AC ADD_COMM ADD_ASSOC] >>
  disch_then kall_tac >> fs[] >>
  fs[] >> gvs[] >>
  Cases_on `qres` >> fs[] >>
  (Cases_on `x`) >> fs[] >> rveq >> fs[]
  >> fs[DECIDE ``!a b.  (a :num) = b + a <=> b = 0``]
*)
  (*2 subgoals*)
(* HOL4 ML code, not ported:
  >- ((* Call_returning_handler_normal *)
  note_tac "Handler case, normal return">>
  qpat_x_assum `_ = (res,s1)` mp_tac >>
  ntac 3 (PURE_TOP_CASE_TAC >> fsrw_tac[][]) >>
  rveq >> fsrw_tac[][] >> strip_tac >>
  Q.ISPECL_THEN [`prog`,`word_state`] mp_tac evaluate_stack_swap>>
  simp[] >> simp[Abbr`word_state`] >>
  simp[push_env_def,ELIM_UNCURRY,s_key_eq_def2] >>
  strip_tac >>
  qpat_x_assum `!_. s_val_eq _ _ ==> _` kall_tac >>
  qpat_x_assum `s_frame_key_eq (StackFrame _ _ _ _) _` mp_tac >>
  simp[oneline s_frame_key_eq_def2] >> TOP_CASE_TAC >> fs[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `state_rel _ _ 0 0 _ _ _ _`
     (fn x => assume_tac x >> (strip_assume_tac o SRULE[state_rel_def])
       x) >>
  rfs[] >>
  drule_then assume_tac stack_rel_cons_LEN_SOME >>
  fs[] >>
  simp[evaluate_copy_ret_Seq'] >>
  simp[num_stack_ret_def] >>
  qmatch_goalsub_abbrev_tac `copy_ret_aux k (f+ 3) num_stack_ret'` >>
  Q.ISPECL_THEN [`k`,`f + 3`,`num_stack_ret'`,`t1`] mp_tac
    evaluate_copy_ret_aux >>
  impl_tac >- (
    fs[Abbr`num_stack_ret'`] >>
    Cases_on `f' = 0` >>
    fsrw_tac[][state_rel_def] >>
    simp[]) >>
  strip_tac >>
  simp[Once stackSemTheory.evaluate_def,evaluate_copy_ret_aux_clock] >>
  `!n p ck. evaluate (SeqStackFree n p,t'' with clock := ck) =
             evaluate (Seq (StackFree n) p,t'' with clock := ck)` by
        (rw [] \\ match_mp_tac evaluate_SeqStackFree
  \\ fsrw_tac[] [state_rel_def] \\ decide_tac) \\
  rev_full_simp_tac(srw_ss())[] \\
  pop_assum kall_tac \\
  fsrw_tac[LET_ss][stackSemTheory.evaluate_def] \\
  `LENGTH t'_stack' >= t1.stack_space + num_stack_ret'`
    by (fsrw_tac[][Abbr`num_stack_ret'`,state_rel_def] >>
        qpat_abbrev_tac `FREE = (LENGTH vs + 1 - k)` >>
        fs[]) \\
  fs[] \\ gvs[] \\
  simp[PopHandler_F,stackSemTheory.evaluate_def] \\
  simp_tac(pure_ss)[GSYM stackSemTheory.state_fupdcanon] \\
  simp[stackSemTheory.set_store_def] \\
  (fn g =>
     qabbrev_tac `stack_state2 = ^((qexists_tac`0`
     \\ qmatch_goalsub_abbrev_tac `stackSem$evaluate (_,t7)`) g
     |> #1 |> hd |> #1 |> hd |> rand |> rhs)` g) >>
  `state_rel ac k f f' (set_vars vs l x) stack_state2 lens 0` by (
    ntac 2 $ qpat_x_assum `state_rel ac k _ _ _ t5 _ _` mp_tac >>
    qmatch_goalsub_abbrev_tac `P` >>
    rpt $ qhdtm_x_assum `state_rel` mp_tac >>
    rewrite_tac[AND_IMP_INTRO] >>
    disch_then (ASSUME_NAMED_TAC "old_state_rels") >>
    rpt $ qhdtm_x_assum `wordSem$evaluate` mp_tac >>
    rpt $ qhdtm_x_assum `stackSem$evaluate` mp_tac >>
    rewrite_tac[AND_IMP_INTRO] >>
    disch_then (ASSUME_NAMED_TAC "evaluate_stuff") >>
    Q.UNABBREV_TAC `P` >>
    rpt strip_tac >>
    fsrw_tac[][state_rel_def,set_vars_def,Abbr`stack_state2`]>>
    qhdtm_x_assum `pop_env` mp_tac >>
    simp[pop_env_def] >> strip_tac >> rveq >>
    simp[] >>
    CONJ_TAC>-
      metis_tac[evaluate_consts]>>
    CONJ_TAC >- (Cases_on `f' = 0` >> fs[]) >>
    CONJ_TAC >-
      simp[wf_alist_insert,wf_fromAList,wf_union]>>
    CONJ_TAC >- (
      rpt (qhdtm_x_assum `stack_size_rel` mp_tac) >>
      simp[stack_size_rel_def] >>
      rpt (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) >>
      first_x_assum old_drule >>
      simp[stack_size_eq] >>
      strip_tac >>
      CONJ_TAC >- (simp[]) >>
      full_simp_tac(srw_ss())[the_eqn] >>
      simp[]) >>
    CONJ_ASM1_TAC >- (
      simp[FLOOKUP_UPDATE] >>
      old_drule stack_rel_DROP_SOME>>
      `f' = f - 1 ` by (Cases_on `f' = 0` >> fsrw_tac[][]) >>
      POP_ASSUM (SUBST_TAC o single) >>
      simp[DROP_DROP_T] >>
      qpat_x_assum `!_. _ ==> EL _ _ = EL _ _` kall_tac >>
      qpat_x_assum `!_. _ ==> EL _ _ = EL _ _` mp_tac>>
      disch_then (qspec_then `2` mp_tac) >>
      impl_tac >-(
        simp[Abbr`num_stack_ret'`] >>
        fsrw_tac[][convs_def] >>
        qpat_x_assum `vs = _` SUBST_ALL_TAC >>
        qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
        full_simp_tac(srw_ss())[wordLangTheory.max_var_def] >>
        `!a b c. max3 a b c = MAX a (MAX b c)`
          by simp[max3_def,MAX_DEF] >>
        fsrw_tac[][MAX_LIST_GENLIST_evens2,GSYM LEFT_ADD_DISTRIB] >>
        simp[] >>
        Cases_on `f = 0` >> fsrw_tac[][] >>
        simp[]) >>
      simp[EL_DROP]) >>
    rpt gen_tac >>
    simp[lookup_alist_insert] >>
    reverse TOP_CASE_TAC
    >- ( (*Arg from return*)
      strip_tac >> rveq >>
      `MEM (n'',v) (ZIP (vs,l))`
         by (DEP_REWRITE_TAC[ MEM_ALOOKUP ] >>
             simp[MAP_ZIP] >>
             fsrw_tac[][convs_def] >>
             qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac
               x) >>
             simp[ALL_DISTINCT_GENLIST]) >>
      drule_then strip_assume_tac MEM_ZIP2 >>
      full_simp_tac(srw_ss())[] >>
      fsrw_tac[][convs_def] >>
      qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
      DEP_REWRITE_TAC[EL_GENLIST] >>
      fsrw_tac[][] >>
      simp[EVEN_DOUBLE] >>
      qpat_x_assum `!i. _ < LENGTH vs ==> _` old_drule >>
      strip_tac >> IF_CASES_TAC >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[stackSemTheory.get_var_def
        ,stackSemTheory.set_var_def]
      >- (
        simp[FLOOKUP_UPDATE] >>
        `n''' + 1 <> k` by DECIDE_TAC >>
        res_tac >> full_simp_tac(srw_ss())[]) >>
      DEP_REWRITE_TAC[LLOOKUP_TAKE] >>
      CONJ_ASM1_TAC >-
      (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
      simp[LLOOKUP_DROP] >>
      fsrw_tac[][Abbr`num_stack_ret'`] >>
      `LENGTH vs + 1 >= k` by
      (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
      simp[] >>
      `LENGTH vs + (t1.stack_space + 1) >= k` by
      (full_simp_tac(srw_ss())[] >>DECIDE_TAC) >>
      reverse CONJ_ASM2_TAC >-
        (qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
        full_simp_tac(srw_ss())[wordLangTheory.max_var_def] >>
        `!a b c. max3 a b c = MAX a (MAX b c)`
          by simp[max3_def,MAX_DEF] >>
        fsrw_tac[][MAX_LIST_GENLIST_evens2,GSYM LEFT_ADD_DISTRIB] >>
        simp_tac(srw_ss())[LET_THM] >>
        strip_tac >> DECIDE_TAC) >>
      `f + k >= n''' + 2`
          by (
          Cases_on `f' = 0` >> full_simp_tac(srw_ss())[] >> simp[]) >>
      `f = f' + 1` by (Cases_on `f' = 0` >> full_simp_tac(srw_ss())[])
        >>
      full_simp_tac(srw_ss())[] >>
      qpat_x_assum `!_. _ ==> _ = _` mp_tac >>
      disch_then (qspec_then `LENGTH vs - (n''' + 1)` mp_tac) >>
      qpat_x_assum `LLOOKUP _ _ = SOME (EL _ _)` mp_tac >>
      disch_tac >>
      simp[EL_DROP] >>
      qpat_x_assum `LLOOKUP _ _ = SOME (EL _ _)` mp_tac >>
      full_simp_tac(srw_ss())[LLOOKUP_THM] >>
      simp[EL_DROP]) >>
    `~ MEM (n'') (vs)` by (
      imp_res_tac ALOOKUP_NONE >>
      pop_assum mp_tac >>
      simp[MAP_ZIP]) >>
    `n'' > 0 /\ EVEN n'' ==> (n'' DIV 2 >= LENGTH vs + 1)` by (
      fsrw_tac[][convs_def] >>
      qpat_assum `vs = _` (fn x => SUBST_ALL_TAC x >> assume_tac x) >>
      fs[MEM_GENLIST] >>
      qpat_x_assum `_ < 2 * f' + 2 * k` mp_tac >>
      full_simp_tac(srw_ss())[wordLangTheory.max_var_def] >>
      `!a b c. max3 a b c = MAX a (MAX b c)`
       by simp[max3_def,MAX_DEF] >>
      pop_assum (full_simp_tac(srw_ss()) o single)>>
      fsrw_tac[][MAX_LIST_GENLIST_evens2,GSYM LEFT_ADD_DISTRIB] >>
      simp[] >>
      strip_tac >>
      simp[EVEN_EXISTS] >> strip_tac  >>
      first_x_assum (qspec_then `n'' DIV 2 - 1` mp_tac) >>
      impl_tac >- simp[DECIDE ``m = m - 1 + 1 <=> (m :num) > 0``] >>
      fs[GSYM GREATER_DEF,GSYM GREATER_EQ,SF DISJ_ss]) >>
    simp[lookup_union,lookup_fromAList,ALOOKUP_toAList] >>
*)
    (*GC cutset*)
(* HOL4 ML code, not ported:
    reverse TOP_CASE_TAC >- (
      strip_tac>> rveq >>
      rename1`EVEN nn`>>
      full_simp_tac(srw_ss())[] >>
      `MEM (nn,v) l0` by metis_tac[ALOOKUP_MEM]>>
      `MEM nn (MAP FST l0)`
        by (
         (pop_assum mp_tac) >>
         rpt (pop_assum $ K ALL_TAC) >>
         simp[MEM_MAP,EXISTS_PROD] >>
         metis_tac[]) >>
      `MEM nn (MAP FST (FST (env_to_list (SND envs) s.permute)))`
       by simp[] >>
      `MEM nn (MAP FST (toAList (SND envs)))`
        by (pop_assum mp_tac >>
          rpt (pop_assum $ K ALL_TAC) >>
          simp[MEM_MAP,env_to_list_def,PULL_EXISTS,
               mem_list_rearrange,sort_MEM] >>
          METIS_TAC[]) >>
      `nn ∈ domain (SND envs)`
         by (fs[toAList_domain]) >>
      qhdtm_x_assum  `cut_envs`
        (strip_assume_tac o
          SRULE[AllCaseEqs(),cut_envs_def,cut_names_def]) >>
      rveq >> full_simp_tac(srw_ss())[domain_inter]  >>
      first_x_assum old_drule >>
      simp[] >> strip_tac >>
      fsrw_tac[][domain_lookup]>>
      full_simp_tac(srw_ss()++LET_ss)[] >>
      first_x_assum (qspecl_then [`nn`,`v'`]mp_tac)>>
      simp[] >> strip_tac >>
      fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
      qpat_abbrev_tac`ls = DROP A B`>>
      Cases_on`ls`>>simp[abs_stack_def]>>
      POP_ASSUM (ASSUME_NAMED_TAC "DROP_NOT_NIL") >>
      DISCH_THEN (strip_assume_tac o SRULE[AllCaseEqs()]) >>
      rveq >> fs[] >>
      ntac 4 $ qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
      rveq>>simp[stack_rel_aux_def]>>
      ntac 4 strip_tac>>
      old_drule filter_bitmap_MEM>>
      disch_then (qspecl_then [`nn DIV 2,v`] mp_tac) >>
      impl_tac >- (
       simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
       METIS_TAC[]) >>
      disch_then (mp_tac o (MATCH_MP MEM_index_list_EL))>>
      strip_tac >> rveq >>
      `stack'''' = DROP 4 (DROP (num_stack_ret' + t1.stack_space)
        t1.stack)`
      by (LABEL_X_ASSUM "DROP_NOT_NIL" assume_tac >> TIDY_ABBREVS >>
        simp[]) >>
      LABEL_X_ASSUM "DROP_NOT_NIL" (assume_tac o
        SRULE[markerTheory.Abbrev_def]) >>
      simp[LLOOKUP_THM,Excl"SUB_RIGHT_LESS"] >>
      DEP_REWRITE_TAC[EL_TAKE,EL_DROP,GSYM EL] >>
      rewrite_tac[CONJ_ASSOC] >>
      CONJ_ASM1_TAC >- (
         full_simp_tac(srw_ss())[LLOOKUP_THM,Excl "SUB_RIGHT_LESS",
         LENGTH_TAKE_EQ_MIN] >>
         fs[MIN_DEF,Excl "SUB_RIGHT_LESS"]) >>
      qmatch_goalsub_abbrev_tac `EL A _ = EL B _` >>
      `B = A` by
        (cruft_tac >>
        full_simp_tac(srw_ss())[Abbr`A`,Abbr`B`,Abbr`num_stack_ret'`] >>
        Cases_on `f = 0` >> full_simp_tac(srw_ss())[] >>
        simp[]) >>
      pop_assum (SUBST_TAC o single) >>
      simp[Abbr`A`] >>
      qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` kall_tac >>
      qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` mp_tac >>
      disch_then (qspec_then `f  +  k - (nn DIV 2 + 1) + 3` mp_tac) >>
      impl_tac >- (
        `nn > 0`
           by (fs[EVEN_EXISTS] >>
           rveq >>
           fs[]) >>
        fs[Abbr`num_stack_ret'`]) >>
      simp[EL_DROP] >>
      qmatch_goalsub_abbrev_tac `N1 + 3 + (N2 + N3)` >>
      simp[]) >>
*)
    (*NON-GC cutset*)
(* HOL4 ML code, not ported:
    strip_tac >>
    qhdtm_x_assum  `cut_envs`
    (strip_assume_tac o SRULE[AllCaseEqs(),cut_envs_def,cut_names_def])
      >>
    rveq >> full_simp_tac(srw_ss())[domain_inter]  >>
    strip_tac >>
    rename [`EVEN nn`] >>
    `nn ∈ domain (inter s.locals (FST live))`
       by (fs[domain_lookup]) >>
    `nn ∈ domain (FST live) ∧ nn ∈ domain s.locals` by (
        full_simp_tac(srw_ss())[domain_inter]) >>
    fsrw_tac[][domain_lookup]>>
    first_x_assum (qspecl_then [`nn`,`v''`]mp_tac)>>
    simp[]>>
    strip_tac>>
    rveq >> fs[] >>
    fsrw_tac[][stack_rel_def]>>qpat_x_assum`A=SOME stack` mp_tac>>
    qpat_abbrev_tac`ls = DROP A B`>>
    Cases_on`ls`>>simp[abs_stack_def]>>
    POP_ASSUM (ASSUME_NAMED_TAC "DROP_NOT_NIL") >>
    DISCH_THEN (strip_assume_tac o SRULE[AllCaseEqs()]) >>
    rveq >> fs[] >>
    ntac 4 $ qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
    rveq>>simp[stack_rel_aux_def]>>
    ntac 4 strip_tac>>
    PRED_ASSUM is_forall mp_tac >>
    simp[ALOOKUP_toAList] >>
    disch_then (qspec_then `nn` mp_tac) >>
    simp[] >>
    res_tac >> fs[] >>
    simp[ALOOKUP_index_list] >>
    `stack'''' = DROP 4 (DROP (num_stack_ret' + t1.stack_space)
      t1.stack)`
       by (LABEL_X_ASSUM "DROP_NOT_NIL" assume_tac >> TIDY_ABBREVS >>
         simp[]) >>
    LABEL_X_ASSUM "DROP_NOT_NIL" (assume_tac o
      SRULE[markerTheory.Abbrev_def]) >>
    fs[] >>
    ONCE_REWRITE_TAC[ADD_ASSOC] >>
    qpat_abbrev_tac `num_and_ss = num_stack_ret' + t1.stack_space` >>
    ONCE_REWRITE_TAC[ADD_COMM] >>
    simp[GSYM DROP_DROP_T] >>
    qpat_abbrev_tac `DROP_num_and_ss = DROP num_and_ss` >>
    simp[LLOOKUP_DROP,LLOOKUP_TAKE] >>
    Q.UNABBREV_TAC `DROP_num_and_ss` >>
    Q.UNABBREV_TAC `num_and_ss` >>
    strip_tac>> pop_assum mp_tac>>
    ntac 2 (pop_assum kall_tac)>>
    qmatch_goalsub_abbrev_tac `LLOOKUP (DROP _ _) A = _ ==> LLOOKUP
      (DROP _ _) B = _` >>
    `A = B` by (
      fsrw_tac[][Abbr`A`,Abbr`B`] >>
      `LENGTH bits = f - 1` by (Cases_on `f = 0` >> fs[]) >>
      fs[]) >>
    simp[Abbr`A`,Abbr`B`] >>
    simp[LLOOKUP_THM] >>
    disch_then sym_sub_tac >>
    qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` kall_tac >>
    qpat_x_assum `!m. _ _ ==> EL _ _ = EL _ _` mp_tac >>
    qmatch_goalsub_abbrev_tac `EL M _` >>
    disch_then (qspec_then `M` mp_tac) >>
    impl_tac >- (
      simp[Abbr`M`,Abbr`num_stack_ret'`] >>
      Cases_on `f = 0` >> fsrw_tac[][] >>
      rveq >>
      fsrw_tac[][EVEN_EXISTS] >>
      rveq >>
      intLib.ARITH_TAC)>>
    rev_full_simp_tac(srw_ss())[])>>
  rpt $ qhdtm_x_assum `comp` mp_tac >>
  Cases_on `bs'''` >> rpt strip_tac >>
  LABEL_X_ASSUM "Result_IND" mp_tac \\ simp[] \\
  disch_then old_drule \\
  disch_then (drule_at (Pos (el 3))) \\
  impl_tac >- (
    fsrw_tac[][convs_def,Abbr`stack_state2`]>>
    simp[CONJ_ASSOC]>>
    REVERSE CONJ_TAC
    >- (
      qpat_x_assum`A<2 * _ + 2 * _:num` mp_tac>>
      `!a b c. max3 a b c = MAX a (MAX b c)` by simp[MAX_DEF,max3_def]
        >>
      simp[wordLangTheory.max_var_def])>>
    REVERSE CONJ_TAC
    >- (
      fs [comp_def,get_labels_def,get_labels_copy_ret,PopHandler_F] \\
      imp_res_tac evaluate_mono \\ fs[] \\
      rpt (qpat_x_assum `subspt _ _` mp_tac) \\
      rpt (qpat_x_assum `get_labels _  ⊆ _` mp_tac) \\
      rpt (pop_assum kall_tac) \\
      metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans]) >>
    rw[]
    >- (
      imp_res_tac wLive_LENGTH>>
      fs[])
    >- (
      imp_res_tac wLive_LENGTH>>
      rfs[]>>
      imp_res_tac evaluate_mono >>
      fs[]>>
      imp_res_tac IS_PREFIX_LENGTH>>
      fs[])
    >> (
      imp_res_tac wLive_LENGTH>>
      rfs[]>>
      imp_res_tac evaluate_mono >>
      fs[]>>
      imp_res_tac comp_IMP_isPREFIX>>
      rfs[] >>
      rpt (qpat_x_assum `_ ≼ _` mp_tac) \\
      rpt (pop_assum kall_tac) \\
      metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]))>>
  rw[]>>
  `x.handler = s.handler`
    by (qhdtm_x_assum `pop_env` mp_tac >>
        rw[pop_env_def] >> simp[]) >>
  fs[] >>
  qexists_tac`ck'`>>
  fsrw_tac[][Abbr`stack_state2`])
  >> note_tac "Handler case, exception">>
  qpat_x_assum `_ = (res,s1)` mp_tac >>
  disch_then (mp_tac o SRULE[AllCaseEqs()]) >>
  simp[] >> strip_tac >>
  `state_rel ac k f f' (set_var handle_var w0 r') t1 lens 0 /\
    r'.handler = s.handler` by (
    Q.ISPECL_THEN [`prog`,`word_state`] assume_tac evaluate_stack_swap>>
    rfs[Abbr`word_state`]>>
    Cases_on`n''`>>
    qpat_x_assum`!a b c.P` kall_tac>>
    fsrw_tac[][call_env_def,push_env_def,dec_clock_def,LET_THM
      ,env_to_list_def,s_key_eq_def]>>
    rveq>>fsrw_tac[][state_rel_def,set_var_def,LET_THM]>>
    `LENGTH lens = LENGTH s.stack` by
       (fsrw_tac[][stack_rel_def,LET_THM]>>
       imp_res_tac abs_stack_IMP_LENGTH)>>
    qpat_x_assum`LASTN A B = C` mp_tac>>
    fsrw_tac[][push_locals_def] >>
    qpat_x_assum`stack_rel k r'.handler A B C D E (LASTN _ (f'::lens))`
      mp_tac>>
    PURE_ONCE_REWRITE_TAC[GSYM ADD1] >>
    fsrw_tac [] [LASTN_CONS_ID]>>
    ntac 2 strip_tac>>
    CONJ_TAC>-
      metis_tac[evaluate_consts]>>
    CONJ_ASM1_TAC>-
      (imp_res_tac stack_rel_cons_LEN_NONE>>
      fsrw_tac[][LENGTH_DROP]>>
      Cases_on`f'`>>fsrw_tac[][]>>
      ntac 2 (pop_assum mp_tac) >>
      rpt(WEAKEN_TAC (K true)) >>
      simp[])>>
    CONJ_TAC>-
      fsrw_tac[][wf_insert,wf_union,wf_fromAList]>>
    CONJ_TAC >- (
      qhdtm_x_assum `stack_size_rel` mp_tac >>
      simp[stack_size_rel_def,stack_size_eq] >>
      strip_tac >>
      imp_res_tac stack_rel_cons_locals_size >>
      CONJ_TAC >- (Cases_on `f = 0` >> fsrw_tac[][]) >>
      rpt (GEN_TAC ORELSE DISCH_TAC) >>
      full_simp_tac(srw_ss())[] >>
      rveq >> full_simp_tac(srw_ss())[miscTheory.the_def] >>
      rveq >> full_simp_tac(srw_ss())[miscTheory.the_def] >>
      CONJ_TAC >- (Cases_on `f = 0` >> fsrw_tac[][] >> simp[]) >>
      (Cases_on `f = 0` >> fsrw_tac[][] >> simp[])) >>
    CONJ_TAC>-
      (`f = f'+1` by (Cases_on`f'`>>fsrw_tac[][])>>
      metis_tac[stack_rel_DROP_NONE])>>
    rpt(qpat_x_assum `IS_SOME _ ==> _` kall_tac) >>
    rpt(PRED_ASSUM (exists (curry op = "the") o map (fst o dest_const)
                    o find_terms is_const)
                   kall_tac) >>
    ntac 2 strip_tac>>
    fsrw_tac[][lookup_insert,convs_def]>>
    IF_CASES_TAC>- simp[]>>
    qpat_x_assum`union _ _ = union _ _` sym_sub_tac>>
    simp[lookup_union] >>
    REVERSE TOP_CASE_TAC >-(
*)
      (*GC cutset *)
(* HOL4 ML code, not ported:
      strip_tac>>
      rename1`EVEN nn`>>
      `nn ∈ domain (fromAList l)` by metis_tac[domain_lookup]>>
      `EVEN nn ∧ k ≤ nn DIV 2` by (
        `nn ∈ domain (FST envs) ∪ domain (SND envs)` by
          metis_tac[IN_UNION,domain_union]>>
        qpat_x_assum`cut_envs _ _ = _` mp_tac>>
        simp[cut_envs_def,cut_names_def,AllCaseEqs()]>>
        strip_tac>>rveq>>
        fsrw_tac[][domain_inter])>>
      simp[]>>
      fsrw_tac[][stack_rel_def]>>
      qpat_x_assum`abs_stack _ _ _ _ =SOME _` mp_tac>>
      qpat_abbrev_tac`L = DROP A B`>>
      Cases_on`L`>>simp[abs_stack_def]>>
      cruft_tac>>
      simp[AllCaseEqs()]>>
      strip_tac>>
      qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
      rveq>>simp[stack_rel_aux_def]>>
      strip_tac>>
      fsrw_tac[][lookup_fromAList]>>
      `MEM (nn,v) l` by metis_tac[ALOOKUP_MEM]>>
      `MEM (nn DIV 2,v) (MAP_FST adjust_names l)` by
        (simp[MAP_FST_def,MEM_MAP,adjust_names_def,EXISTS_PROD]>>
        metis_tac[])>>
      simp[LLOOKUP_THM]>>
      old_drule filter_bitmap_MEM>>
      disch_then drule>>
      strip_tac >>
      old_drule MEM_index_list_EL>>
      old_drule MEM_index_list_LIM>>
      simp[LENGTH_TAKE,EL_TAKE]>>
      strip_tac>>
      fs[]>>
      qpat_x_assum`COND (_ = []) _ _`mp_tac >>
      rename1`ls = []` >> Cases_on`ls` \\ fs[] >>
      rename1`SUC nnn`>>
      strip_tac>>
      `k + (SUC nnn)- nn DIV 2 = SUC (k + SUC nnn - (nn DIV 2 + 1))` by
        intLib.ARITH_TAC >>
      pop_assum SUBST1_TAC>>
      simp[ADD1,EL_TAKE])
    >- (
      strip_tac>>
      rename1`EVEN nn`>>
      `nn ∈ domain (fromAList l0)` by metis_tac[domain_lookup]>>
      `EVEN nn ∧ k ≤ nn DIV 2` by (
        `nn ∈ domain (FST envs) ∪ domain (SND envs)` by
          metis_tac[IN_UNION,domain_union]>>
        qpat_x_assum`cut_envs _ _ = _` mp_tac>>
        simp[cut_envs_def,cut_names_def,AllCaseEqs()]>>
        strip_tac>>rveq>>
        fsrw_tac[][domain_inter])>>
      simp[]>>
      fsrw_tac[][stack_rel_def]>>
      qpat_x_assum`abs_stack _ _ _ _ =SOME _` mp_tac>>
      qpat_abbrev_tac`L = DROP A B`>>
      Cases_on`L`>>simp[abs_stack_def]>>
      cruft_tac>>
      simp[AllCaseEqs()]>>
      strip_tac>>
      qpat_x_assum`stack_rel_aux A B C D` mp_tac>>
      rveq>>simp[stack_rel_aux_def]>>
      strip_tac>>
      fsrw_tac[][lookup_fromAList]>>
      first_x_assum drule_all>>
      strip_tac>> pop_assum mp_tac>>
      DEP_REWRITE_TAC[ALOOKUP_index_list] >>
      fs[adjust_names_def]>>
      qpat_x_assum`COND (_ = []) _ _`mp_tac >>
      rename1`ls = []` >> Cases_on`ls` \\ fs[] >>
      rename1`SUC nnn`>>
      strip_tac>>
      `k + (SUC nnn)- nn DIV 2 = SUC (k + SUC nnn - (nn DIV 2 + 1))` by
        intLib.ARITH_TAC >>
      pop_assum SUBST1_TAC>>
      simp[LLOOKUP_def])) >>
  rpt $ qhdtm_x_assum `comp` mp_tac >>
  Cases_on `bs'''` >> rpt strip_tac >>
  LABEL_X_ASSUM "Exception_IND" mp_tac \\ simp[] \\
  disch_then old_drule \\
  disch_then (drule_at (Pos (el 3))) \\
  impl_tac >- (
    fsrw_tac[][convs_def]>>
    simp[CONJ_ASSOC]>>
    REVERSE CONJ_TAC
    >- (
      qpat_x_assum`A<2 * _ + 2 * _:num` mp_tac>>
      `!a b c. max3 a b c = MAX a (MAX b c)` by simp[MAX_DEF,max3_def]
        >>
      simp[wordLangTheory.max_var_def])>>
    REVERSE CONJ_TAC
    >- (
      fs [comp_def,get_labels_def] \\
      imp_res_tac evaluate_mono \\ fs[] \\
      rpt (qpat_x_assum `subspt _ _` mp_tac) \\
      rpt (qpat_x_assum `get_labels _  ⊆ _` mp_tac) \\
      rpt (pop_assum kall_tac) \\
      metis_tac[loc_check_SUBSET,SUBSET_TRANS,subspt_trans]) >>
    rw[]
    >- (
      imp_res_tac wLive_LENGTH>>
      imp_res_tac comp_IMP_LENGTH>>
      fs[])
    >- (
      imp_res_tac wLive_LENGTH>>
      imp_res_tac comp_IMP_LENGTH>>
      rfs[]>>
      imp_res_tac evaluate_mono >>
      fs[]>>
      imp_res_tac IS_PREFIX_LENGTH>>
      fs[])
    >> (
      imp_res_tac wLive_LENGTH>>
      imp_res_tac comp_IMP_LENGTH>>
      rfs[]>>
      imp_res_tac evaluate_mono >>
      fs[]>>
      imp_res_tac comp_IMP_isPREFIX>>
      rfs[] >>
      rpt (qpat_x_assum `_ ≼ _` mp_tac) \\
      rpt (pop_assum kall_tac) \\
      metis_tac[IS_PREFIX_TRANS,isPREFIX_DROP]))>>
  strip_tac >>
  Q.EXISTS_TAC `ck'` >> fs[]
)
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Break]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,comp_def] \\ rveq \\
  qexists_tac `0` \\
  simp [stackSemTheory.evaluate_def]
QED
*)

(* HOL4 ML code, not ported:
Resume comp_correct[Continue]:
  REPEAT STRIP_TAC \\ fs[get_labels_def] \\
  fs [wordSemTheory.evaluate_def,comp_def] \\ rveq \\
  qexists_tac `0` \\
  simp [stackSemTheory.evaluate_def]
QED
*)

(* HOL4 ML code, not ported:
Finalise comp_correct;
*)

(* match original comp_correct shape: n, sprog, bs', n' are free *)
(* HOL4 ML code, not ported:
val comp_correct = let
  val th = REWRITE_RULE [FORALL_PROD] comp_correct
  val vs = th |> concl |> strip_forall |> #1
  val drops = List.filter (fn v => let val n = #1 (dest_var v) in
    n = "n" orelse n = "sprog" orelse n = "bs'" orelse n = "n'" end) vs
  val keeps = List.filter (fn v => not (List.exists (fn d =>
    Term.compare(v,d) = EQUAL) drops)) vs
  in GENL keeps (SPECL vs th) end;
*)

(* HOL4 ML code, not ported:
val comp_Call_lemma = comp_correct
  |> Q.SPEC `Call NONE (SOME start) [0] NONE`
  |> SIMP_RULE std_ss [comp_def,stack_free_def,call_dest_def,LET_THM]
  |> Q.SPECL [`s`,`k`,`0`,`0`]
  |> SIMP_RULE std_ss [stack_arg_count_def,SeqStackFree_def,
       evaluate_Seq_Skip,
       EVAL  ``post_alloc_conventions k (Call NONE (SOME start) [0]
         NONE)``,
       EVAL  ``flat_exp_conventions (Call NONE (SOME start) [0] NONE)``,
       wordLangTheory.max_var_def,LET_DEF,MAX_DEF] |> GEN_ALL
*)

(* HOL4 ML code, not ported:
val s = ``(s:(α,num # γ,'ffi)wordSem$state)``;
val s' = ``(s:(α,'c,'ffi)stackSem$state)``;
val t = ``(t:(α,'c,'ffi)stackSem$state)``;
val clock_simps =
  LIST_CONJ [
    EVAL``(^s with clock := c).clock``,
    EVAL``(^s with clock := c) with clock := d``,
    EVAL``(^s' with clock := c).clock``,
    EVAL``(^s' with clock := c) with clock := d``];
*)

(* HOL4 ML code, not ported:
fun drule0 th =
  first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
    th))
*)

let init_state_ok_def = cake_define
  `(\x y. strcat x y)
     (init_state_ok ac k) (t coracle) <=>
       4 < k /\ good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
         stackSem_state_use_stack
       t /\ stackSem_state_use_store t /\ stackSem_state_use_alloc t
         /\ gc_fun_ok (?_gc_fun t) /\ stackSem_state_stack_space
       t <= LENGTH (?_stack t) /\
       FLOOKUP (stackSem_state_regs t) 0 = SOME (Loc 1 0) /\
       LENGTH (stackSem_state_bitmaps t) + 1 < dimword (:'a) /\
       [(n2w 4)] <<= stackSem_state_bitmaps t /\
       LENGTH (?_stack t) < dimword (:'a) /\
       DROP (stackSem_state_stack_space t) (?_stack t) =
         [wordLang_Word (n2w 0)] /\
       Handler IN FDOM (?_store t) /\
       LENGTH (stackSem_state_bitmaps t) + LENGTH (buffer_buffer
         (?_data_buffer t)) + buffer_space_left (?_data_buffer
          t) + 1 < dimword (:'a) /\ ?_compile_oracle
       t = (\n.
         let ((bm0,cfg),progs) = coracle n in
         let (progs,fs,bm) = compile_word_to_stack ac F k progs
           (misc_Nil,bm0) in
           (cfg,progs,append (FST bm))) /\
       (!n. let ((bm0,cfg),progs) = coracle n in
           EVERY (post_alloc_conventions k o SND o SND) progs /\
           EVERY (flat_exp_conventions o SND o SND) progs /\
           EVERY ((<>) raise_stub_location o FST) progs /\
           EVERY ((<>) store_consts_stub_location o FST) progs /\
           (n = 0 ==> bm0 = LENGTH (stackSem_state_bitmaps t)))`;;

let make_init_def = cake_define
  `(\x y. strcat x y)
     (make_init ac k) (t code coracle) =
       mk_wordSem_state (sptree_insert 0 (Loc 1 0) LN) (SOME 0)
         (?_fp_regs t) (?_store t \\ Handler) [] (LENGTH (?_stack t))
         (stack_size ([]:('a stack_frame) list)) (mapi (\n
         (arg_count,prog). FST (SND (word_to_stack_compile_prog ac F
         prog arg_count k (misc_Nil,0)))) code) (?_memory t) (?_mdomain
         t) (?_sh_mdomain t) (K I) (\(bm0,cfg) progs.
         let (progs,fs,bm) = compile_word_to_stack ac F k progs
           (misc_Nil,bm0) in
         OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND
           bm,cfg)))
           (?_compile t cfg progs)) coracle (?_code_buffer t)
             (?_data_buffer t) (?_gc_fun t) 0 (?_clock t) 0 code
             (?_be t) (?_ffi t)`;;

(* HOL4 ML code, not ported:
val init_state_ok_semantics =
  state_rel_IMP_semantics |> Q.INST [`s`|->`make_init ac k t code
    coracle`]
  |> SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO]
  |> (fn th => (MATCH_MP th (UNDISCH init_state_ok_IMP_state_rel)))
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
*)

(* HOL4 ML code, not ported:
val init_state_ok_semantics' =
  state_rel_IMP_semantics' |> Q.INST [`s`|->`make_init ac k t code
    coracle`]
  |> SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO]
  |> (fn th => (MATCH_MP th (UNDISCH init_state_ok_IMP_state_rel)))
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
*)

(* HOL4 ML code, not ported:
val wconvs =
  [post_alloc_conventions_def,wordConvsTheory.full_inst_ok_less_def
  ,call_arg_convention_def,wordLangTheory.every_var_def
  ,wordLangTheory.every_stack_var_def]
*)

(* HOL4 ML code, not ported:
val reg_bound_ind = stackPropsTheory.reg_bound_ind
val reg_bound_def = stackPropsTheory.reg_bound_def
val reg_bound_inst_def = stackPropsTheory.reg_bound_inst_def
*)

(* Gluing all the conventions together *)

(* this is the only property needed of the wRegs  *)
(* HOL4 ML code, not ported:
val get_code_labels_wReg = Q.prove(`
  (∀n. get_code_labels (f n) = {}) ⇒
  get_code_labels (wRegWrite1 f n kf) = {} ∧
  get_code_labels (wRegWrite2 f n kf) = {}
  `,
  PairCases_on`kf`>>rw[wRegWrite1_def,wRegWrite2_def]) |> SIMP_RULE
    std_ss [IMP_CONJ_THM];
*)

(* no_install is preserved *)

(* no_share_mem is preserved *)
