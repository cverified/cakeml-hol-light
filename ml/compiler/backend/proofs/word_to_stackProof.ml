(* ======================================================== *)
(*  word_to_stackProof: ported from HOL4's
    compiler/backend/proofs/word_to_stackProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_to_stack
*)

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
(* HOL4 ancestors outside the port: (* for extend_with_resource_limit
   *) (* for list_Seq *) (* for extract_labels *) (* for
   word_add_carry_def *) *)

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

(* Set up ML bindings *)
(* HOL4 word_to_stackProofScript.sml:18-20: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:31-32: ML code, not ported *)
(* HOL4 word_to_stackProofScript.sml:33: the type abbreviation state,
   which the port expands *)
(* HOL4 word_to_stackProofScript.sml:34-35: the overload word_cmp,
   which the port expands *)

(* HOL4 word_to_stackProofScript.sml:37: the ML values that the
   definitions below antiquote *)

(* HOL4 word_to_stackProofScript.sml:39-40: the ML values that the
   definitions below antiquote *)

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

(* HOL4 word_to_stackProofScript.sml:317: ML code, not ported *)

let index_list_def = cake_define_list
  [`index_list [] n = []`;
   `index_list (x :: xs) n = (n + LENGTH xs,x) :: index_list xs n`];;

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)

(*TODO This should use GENLIST instead of MAP _ (COUNT_LIST _)*)

(*MEM to an EL characterization for index lists*)

let list_LUPDATE_def = cake_define_list
  [`list_LUPDATE [] n ys = ys`;
   `list_LUPDATE (x :: xs) n ys = list_LUPDATE xs (n + 1) (LUPDATE
  x n ys)`];;

(* move to stackProps? *)

(* move to wordProps? *)

(* state relation *)

(*Abstracts a stackLang stack w.r.t. wordLang's
  Note: requires assumption on dimindex(:'a) stated in state_rel *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let abs_stack_def = cake_define_cheat CHEAT_TAC
  `abs_stack bitmaps x2 stack' x4 =
        match (bitmaps,x2,stack',x4) with
          ((bitmaps:('a word) list),[],stack',[]) ->
       (if stack' = [wordLang_Word ((n2w 0):'a word)] then SOME []
         else NONE)
        | (bitmaps,(StackFrame n l0 l NONE :: xs),(w :: stack'),(len
          :: lens)) ->
       (match full_read_bitmap bitmaps w with NONE -> NONE | SOME
         bits ->
           (if ~(LENGTH bits = len) then NONE else
           if LENGTH stack' < len then NONE else
             let frame = TAKE len stack' in
             let rest = DROP len stack' in
               match abs_stack bitmaps xs rest lens with NONE -> NONE
                 | SOME ys -> SOME ((NONE,bits,frame) :: ys)))
        | (bitmaps,((StackFrame n l0 l (SOME _1)) :: xs),(w ::
          stack'),(len :: lens)) ->
       (if ~(w = wordLang_Word (n2w 1)) then NONE else
         (match stack' with loc :: hv :: w :: stack' ->
            (match full_read_bitmap bitmaps w with NONE -> NONE |
              SOME bits ->
                 (if ~(LENGTH bits = len) then NONE else
                 if LENGTH stack' < len then NONE else
                   let frame = TAKE len stack' in
                   let rest = DROP len stack' in
                     match abs_stack bitmaps xs rest lens with NONE
                       -> NONE | SOME ys -> SOME ((SOME
                       (loc,hv),bits,frame) :: ys))) | _2 -> NONE))
        | (bitmaps,_3,_4,_5) -> NONE`;;

(* HOL4 word_to_stackProofScript.sml:742: ML code, not ported *)

(*TODO this should probably be an Overload*)
let MAP_FST_def = cake_define
  `MAP_FST f xs = MAP (\(x,y). (f x,y)) xs`;;

let adjust_names_def = cake_define
  `adjust_names n = n DIV 2`;;

(*handler_val counts the total number of words in the list of frames*)
let handler_val_def = cake_define_list
  [`handler_val [] = 1`;
   `handler_val ((NONE,_6,frame) :: stack') =
        1 + LENGTH frame + handler_val stack'`;
   `handler_val ((SOME _7,_8,frame) :: stack') =
        4 + LENGTH frame + handler_val stack'`];;

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
        | ((StackFrame n l0 l NONE :: xs),((NONE,bits,frame) ::
          stack')) ->
       (!n v.
         ALOOKUP l0 n = SOME v /\ ALOOKUP l n = NONE ==>
         adjust_names n < k + LENGTH bits /\
         oEL ((k + LENGTH bits) - (adjust_names n + 1)) bits = SOME F
           /\
         ALOOKUP (index_list frame k) (n DIV 2) = SOME v) /\
       filter_bitmap bits (index_list frame k) = SOME (MAP_FST
         adjust_names l,[]) /\
       the (LENGTH frame + 1) n = LENGTH frame + 1 /\
       stack_rel_aux k len xs stack'
        | (((StackFrame n l0 l (SOME (h1,l1,l2))) :: xs),((SOME
          (loc,hv),bits,frame) :: stack')) ->
       (h1 < LENGTH stack' /\
       is_handler_frame (EL (LENGTH stack' - (h1 + 1)) xs) ==>
       hv = wordLang_Word (n2w (len - handler_val (LASTN (h1 + 1)
         stack')))) /\
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
       stack_rel_aux k len xs stack'
        | (_10,_11) -> F`;;

let sorted_env_def = cake_define
  `sorted_env (StackFrame n l0 l _12) = SORTED (\x y. FST x > FST y)
  l`;;

let stack_rel_def = cake_define
  `word_to_stackProof_stack_rel k s_handler s_stack t_handler
  t_rest_of_stack t_stack_length t_bitmaps lens <=>
     EVERY sorted_env s_stack /\
     (?stack'.
       abs_stack t_bitmaps s_stack t_rest_of_stack lens = SOME stack'
         /\
       (
       s_handler < LENGTH s_stack /\
       is_handler_frame (EL (LENGTH s_stack - (s_handler + 1))
         s_stack) ==>
       t_handler = SOME (wordLang_Word (n2w (t_stack_length -
         handler_val (LASTN (s_handler + 1) stack'))))) /\
       stack_rel_aux k t_stack_length s_stack stack')`;;
hol4_overload "stack_rel" "word_to_stackProof_stack_rel";;

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
     (state_clock s = state_clock t) /\ (state_gc_fun s =
       state_gc_fun t) /\ (wordSem_state_permute s = K I) /\
     (state_ffi t = state_ffi s) /\ stackSem_state_use_stack t /\
       stackSem_state_use_store t /\ stackSem_state_use_alloc t /\
     (state_memory t = state_memory s) /\ (state_mdomain t =
       state_mdomain s) /\ 4 < k /\
     (state_sh_mdomain t = state_sh_mdomain s) /\
     (state_store s = state_store t \\ Handler) /\ gc_fun_ok
       (state_gc_fun t) /\ wordSem_state_termdep s = 0 /\ be
     t = be s /\ state_ffi t = state_ffi s /\ Handler IN FDOM
       (state_store t) /\ fp_regs
     t = fp_regs s /\ state_data_buffer
     t = state_data_buffer s /\ state_code_buffer
     t = state_code_buffer s /\ compile
     s = (\(bm0,cfg) progs.
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
       OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND
         bm,cfg)))
         (compile t cfg progs)) /\ compile_oracle
     t = (\n.
       let ((bm0,cfg),progs) = compile_oracle s n in
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
         (cfg,progs,append (FST bm))) /\
     (!n. let ((bm0,cfg),progs) = compile_oracle s n in
         EVERY (post_alloc_conventions k o SND o SND) progs /\
         EVERY (flat_exp_conventions o SND o SND) progs /\
         EVERY ((\x y. ~(x = y)) raise_stub_location o FST) progs /\
         EVERY ((\x y. ~(x = y)) store_consts_stub_location o FST)
           progs /\
         (n = 0 ==> bm0 = LENGTH (stackSem_state_bitmaps t))) /\
     domain (state_code t) = raise_stub_location INSERT
                       store_consts_stub_location INSERT domain
                         (state_code s) /\
     (!n word_prog arg_count.
        (sptree_lookup n (state_code s) = SOME (arg_count,word_prog))
          ==>
        post_alloc_conventions k word_prog /\
        flat_exp_conventions word_prog /\
        (?bs i bs2 i2 f stack_prog.
          word_to_stack_compile_prog ac F word_prog arg_count k
            (bs,i) = (stack_prog,f,(bs2,i2)) /\
          LENGTH (append bs) <= i /\ i - LENGTH (append bs) <= LENGTH
            (stackSem_state_bitmaps t) /\
          isPREFIX (append bs2) (DROP (i - LENGTH (append bs))
            (stackSem_state_bitmaps t)) /\
          (sptree_lookup n (state_code t) = SOME stack_prog) /\
          the f (sptree_lookup n (wordSem_state_stack_size s)) = f))
            /\
     (sptree_lookup raise_stub_location (state_code t) = SOME
       (raise_stub F k)) /\
     (sptree_lookup store_consts_stub_location (state_code t) = SOME
       (store_consts_stub k)) /\
     good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
     LENGTH (stackSem_state_bitmaps t) + LENGTH (buffer_buffer
       (state_data_buffer s)) + buffer_space_left (state_data_buffer s)
       + 1 < dimword (:'a) /\
     1 <= LENGTH (stackSem_state_bitmaps t) /\ HD
       (stackSem_state_bitmaps t) = (n2w 4) /\
       stackSem_state_stack_space
     t + f <= LENGTH (stack t) /\ LENGTH (stack t) < dimword (:'a) /\
     (if f' = 0 then f = 0 else (f = f' + 1)) /\
     wf (wordSem_state_locals s) /\
     stack_size_rel f (wordSem_state_locals_size s)
       (wordSem_state_stack_limit s) (wordSem_state_stack_max s) (stack
       s) (stack
       t) (stackSem_state_stack_space t) (extra:num) /\
     (let stack' = DROP (stackSem_state_stack_space t + extra) (stack
       t) in
     let current_frame = TAKE f stack' in
     let rest_of_stack = DROP f stack' in
       word_to_stackProof_stack_rel k (wordSem_state_handler s)
         (stack s) (FLOOKUP (state_store t) Handler)
         rest_of_stack (LENGTH (stack t)) (stackSem_state_bitmaps t)
           lens /\
       (!n v.
         (sptree_lookup n (wordSem_state_locals s) = SOME v) ==>
         EVEN n /\
         (if n DIV 2 < k then (FLOOKUP (stackSem_state_regs t) (n DIV
           2) = SOME v) else ((\l n. oEL n l) current_frame (f - 1 - (n
           DIV 2 - k)) = SOME v) /\
              n DIV 2 < k + f')))`;;
hol4_overload "state_rel" "word_to_stackProof_state_rel";;

(* correctness proof *)

(* HOL4 word_to_stackProofScript.sml:974-981: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:983-993: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:1259-1262: ML code, not ported *)

(*Might need to extend c as well*)

(*These two are actually implied by s_key_eq*)

let abs_frame_eq_def = cake_define
  `abs_frame_eq p q <=>
   FST p = FST q /\
   FST (SND p) = FST (SND q) /\
   LENGTH (SND (SND p)) = LENGTH (SND (SND q))`;;

(*Prove the inductive bits first...*)


(* HOL4 word_to_stackProofScript.sml:2105: the type abbreviation
   result, which the port expands *)

let compile_result_def = cake_define_list
  [`compile_result (wordSem_Result w1 w2) = stackSem_Result w1`;
   `compile_result (wordSem_Exception w1 w2) = stackSem_Exception w1`;
   `compile_result wordSem_TimeOut = stackSem_TimeOut`;
   `compile_result wordSem_NotEnoughSpace = stackSem_Halt
  (wordLang_Word (n2w 1))`;
   `compile_result (wordSem_FinalFFI f) = stackSem_FinalFFI f`;
   `compile_result (wordSem_Break k) = stackSem_Break k`;
   `compile_result (wordSem_Continue k) = stackSem_Continue k`;
   `compile_result wordSem_Error = stackSem_Error`];;

(* HOL4 word_to_stackProofScript.sml:2429-2431: ML code, not ported *)

let push_locals_def = cake_define
  `push_locals l0 l s = stack_fupd (K (StackFrame
  (wordSem_state_locals_size s) l0 l NONE :: stack s))
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

(* HOL4 word_to_stackProofScript.sml:3847-3890: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:3892-3937: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:3938-3970: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:3971-3995: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:3996-4023: code that the source
   has in a comment *)
(* HOL4 word_to_stackProofScript.sml:4024-4047: code that the source
   has in a comment *)
(*
Theorem wStackLoad_thm3 =
 wStackLoad_thm2
 |> Q.INST [`t`|->`set_var v1 v2 t`]
 |> PURE_REWRITE_RULE[wordPropsTheory.set_var_const,set_var_const]
*)
let _ = size_thms "wordLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 word_to_stackProofScript.sml:4061-4066: the tactic that
   proves the termination *)
let map_var_def = cake_define_list_try (fun () ->
  `MEASURE (wordLang_exp_size ARB o SND)`)
  [`map_var f (wordLang_Var num') = Var (f num')`;
   `map_var f (wordLang_Load exp) = Load (map_var f exp)`;
   `map_var f (wordLang_Op wop ls) = wordLang_Op wop (MAP (map_var f)
  ls)`;
   `map_var f (wordLang_Shift sh e1 e2) = Shift sh (map_var f e1)
  (map_var f e2)`;
   `map_var f (wordLang_Const c) = (Const c:'a wordLang_exp)`;
   `map_var f (wordLang_Lookup v) = wordLang_Lookup v`];;
(* HOL4 word_to_stackProofScript.sml:4089-4385: code that the source
   has in a comment *)

(*The last two are weakened to allow easy irule
*)

(*For calls*)

(*For returning calls*)


(* HOL4 word_to_stackProofScript.sml:5203-5232: code that the source
   has in a comment *)

(*NB this lemma can be slightly simpler with
EL (x + offset) stack' = EL (x) stack'*)

(* HOL4 word_to_stackProofScript.sml:5349-5357: ML code, not ported *)
  (*get_var_set_var?*)
(* HOL4 word_to_stackProofScript.sml:5359: ML code, not ported *)

(* Used in backendProof *)

(* HOL4 word_to_stackProofScript.sml:5719-5752: the ML values that
   the definitions below antiquote *)

(* HOL4 word_to_stackProofScript.sml:5754: ML code, not ported *)


(* HOL4 word_to_stackProofScript.sml:5790-5796: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:5798-5853: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6040-6051: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:6053-6117: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6119-6130: code that the source
   has in a comment *)

(* HOL4 word_to_stackProofScript.sml:6315-6326: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6328-6331: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6333-6354: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6356-6374: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6376-6392: ML code, not ported *)
  (*TODO remove by changing word_exp_def*)
(* HOL4 word_to_stackProofScript.sml:6394: ML code, not ported *)
  (*TODO remove by changing get_store_def*)
(* HOL4 word_to_stackProofScript.sml:6396-6403: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6405-6408: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6410-6420: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6422-6427: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6429-6492: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6494-6579: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6626-6741: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6767-6773: ML code, not ported *)
  (* prevent splitting *)
(* HOL4 word_to_stackProofScript.sml:6775-6903: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6905-6923: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:6943-7070: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7072-7096: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7098-7123: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7125-7164: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7528-7544: ML code, not ported *)

(* TODO: clean up *)
(* HOL4 word_to_stackProofScript.sml:7554-7587: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7717-7720: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7722: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7767-7798: ML code, not ported *)
    (* stack-overflow sub-case *)
(* HOL4 word_to_stackProofScript.sml:7800-7828: ML code, not ported *)
  (* non-stack-overflow: res_b = OPTION_MAP compile_result q, so IH's
     "else"
     branch gives us state_rel-like facts about r and t1_b per q. *)
(* HOL4 word_to_stackProofScript.sml:7831-7832: ML code, not ported *)
    (* cont_loop q: either q = NONE or q = SOME (Continue 0) *)
(* HOL4 word_to_stackProofScript.sml:7834-7835: ML code, not ported *)
      (* TimeOut: s1 = flush_state T r, res = SOME TimeOut *)
(* HOL4 word_to_stackProofScript.sml:7837-7846: ML code, not ported *)
    (* recursive case: clock ≠ 0, recurse with dec_clock *)
(* HOL4 word_to_stackProofScript.sml:7848-7908: ML code, not ported *)
    (* passthrough: s1 = r, stack exit_loop matches *)
(* HOL4 word_to_stackProofScript.sml:7910-7916: ML code, not ported *)
  (* Break 0: s1 = cut_state (exit_names,LN) r *)
(* HOL4 word_to_stackProofScript.sml:7918-7921: ML code, not ported *)


(* HOL4 word_to_stackProofScript.sml:7924-7933: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:7935-8010: ML code, not ported *)
    (*preconditions for negation rules*)
(* HOL4 word_to_stackProofScript.sml:8012-8164: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:8166-8202: ML code, not ported *)
    (* Two subgoals *)
(* HOL4 word_to_stackProofScript.sml:8204-8247: ML code, not ported *)
    (*TODO shouldn't be unfolding here*)
(* HOL4 word_to_stackProofScript.sml:8249-8251: ML code, not ported *)
    (*Get through the eval of stack_move*)
(* HOL4 word_to_stackProofScript.sml:8253-8335: ML code, not ported *)
      (*TODO this is very slow*)
(* HOL4 word_to_stackProofScript.sml:8337-8449: ML code, not ported *)
    (*This looks hacky but it works*)
(* HOL4 word_to_stackProofScript.sml:8451-8615: ML code, not ported *)
    (*hit stack limit during function call*)
(* HOL4 word_to_stackProofScript.sml:8617-8665: ML code, not ported *)
    (*2 subgoals*)
(* HOL4 word_to_stackProofScript.sml:8667-8823: ML code, not ported *)
      (* GC cutset *)
(* HOL4 word_to_stackProofScript.sml:8825-8901: ML code, not ported *)
      (* NON-GC cutset *)
(* HOL4 word_to_stackProofScript.sml:8903-9010: ML code, not ported *)
      (*because it can't be the top frame of word_state, which is NONE*)
(* HOL4 word_to_stackProofScript.sml:9012-9027: ML code, not ported *)
  (*Space to store handler case*)
(* HOL4 word_to_stackProofScript.sml:9029-9070: ML code, not ported *)
  (* Needs to go in wordSem?*)
(* HOL4 word_to_stackProofScript.sml:9072-9104: ML code, not ported *)
  (*Space to store args*)
(* HOL4 word_to_stackProofScript.sml:9106-9169: ML code, not ported *)
    (*TODO this is very slow*)
(* HOL4 word_to_stackProofScript.sml:9171-9232: ML code, not ported *)
  (*space for the function local var*)
(* HOL4 word_to_stackProofScript.sml:9234-9279: ML code, not ported *)
  (*This looks hacky but it works*)
(* HOL4 word_to_stackProofScript.sml:9281-9444: ML code, not ported *)
  (*hit stack limit during function call*)
(* HOL4 word_to_stackProofScript.sml:9446-9494: ML code, not ported *)
  (*2 subgoals*)
(* HOL4 word_to_stackProofScript.sml:9496-9674: ML code, not ported *)
    (*GC cutset*)
(* HOL4 word_to_stackProofScript.sml:9676-9751: ML code, not ported *)
    (*NON-GC cutset*)
(* HOL4 word_to_stackProofScript.sml:9753-9921: ML code, not ported *)
      (*GC cutset *)
(* HOL4 word_to_stackProofScript.sml:9923-10047: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10049-10054: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10056-10061: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10063: ML code, not ported *)

(* match original comp_correct shape: n, sprog, bs', n' are free *)
(* HOL4 word_to_stackProofScript.sml:10066-10072: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10080-10088: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10123-10131: the ML values that
   the definitions below antiquote *)

(* HOL4 word_to_stackProofScript.sml:10133-10134: ML code, not ported *)

let init_state_ok_def = cake_define
  `init_state_ok ac k (t:('a,'c,'ffi)stackSem_state) coracle <=>
     4 < k /\ good_dimindex (:'a) /\ 8 <= dimindex (:'a) /\
       stackSem_state_use_stack
     t /\ stackSem_state_use_store t /\ stackSem_state_use_alloc t /\
       gc_fun_ok (state_gc_fun t) /\ stackSem_state_stack_space
     t <= LENGTH (stack t) /\
     FLOOKUP (stackSem_state_regs t) 0 = SOME (Loc 1 0) /\
     LENGTH (stackSem_state_bitmaps t) + 1 < dimword (:'a) /\
     [(n2w 4)] <<= stackSem_state_bitmaps t /\
     LENGTH (stack t) < dimword (:'a) /\
     DROP (stackSem_state_stack_space t) (stack t) = [wordLang_Word
       (n2w 0)] /\
     Handler IN FDOM (state_store t) /\
     LENGTH (stackSem_state_bitmaps t) + LENGTH (buffer_buffer
       (state_data_buffer t)) + buffer_space_left (state_data_buffer
        t) + 1 < dimword (:'a) /\ compile_oracle
     t = (\n.
       let ((bm0,cfg),progs) = coracle n in
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
         (cfg,progs,append (FST bm))) /\
     (!n. let ((bm0,cfg),progs) = coracle n in
         EVERY (post_alloc_conventions k o SND o SND) progs /\
         EVERY (flat_exp_conventions o SND o SND) progs /\
         EVERY ((\x y. ~(x = y)) raise_stub_location o FST) progs /\
         EVERY ((\x y. ~(x = y)) store_consts_stub_location o FST)
           progs /\
         (n = 0 ==> bm0 = LENGTH (stackSem_state_bitmaps t)))`;;

let make_init_def = cake_define
  `word_to_stackProof_make_init ac k (t:('a,'c,'ffi)stackSem_state) code
  coracle =
     mk_wordSem_state (sptree_insert 0 (Loc 1 0) LN) (SOME 0)
       (fp_regs t) (state_store t \\ Handler) [] (LENGTH (stack t))
       (stack_size ([]:('a stack_frame) list)) (mapi (\n
       (arg_count,prog). FST (SND (word_to_stack_compile_prog ac F prog
       arg_count k (misc_Nil,0)))) code) (state_memory t) (state_mdomain
       t) (state_sh_mdomain t) (K I) (\(bm0,cfg) progs.
       let (progs,fs,bm) = compile_word_to_stack ac F k progs
         (misc_Nil,bm0) in
       OPTION_MAP (\(bytes,cfg). (bytes,append (FST bm),(SND
         bm,cfg)))
         (compile t cfg progs)) coracle (state_code_buffer t)
           (state_data_buffer t) (state_gc_fun t) 0 (state_clock t) 0
           code (be t) (state_ffi t)`;;
hol4_overload "make_init" "word_to_stackProof_make_init";;

(* HOL4 word_to_stackProofScript.sml:10467-10471: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10703-10707: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:10956: ML code, not ported *)

(* HOL4 word_to_stackProofScript.sml:11585-11587: ML code, not ported *)

(* Gluing all the conventions together *)

(* this is the only property needed of the wRegs  *)
(* HOL4 word_to_stackProofScript.sml:11698-11703: ML code, not ported *)

(* no_install is preserved *)

(* no_share_mem is preserved *)
