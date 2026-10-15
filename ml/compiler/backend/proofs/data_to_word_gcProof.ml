(* ======================================================== *)
(*  data_to_word_gcProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_gcProofScript.sml  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/location.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: int_bitwise finite_map While *)

(* HOL4 ML code, not ported:
val shift_def = backend_commonTheory.word_shift_def
val upper_w2w_def = backend_commonTheory.upper_w2w_def
val isWord_def = wordSemTheory.isWord_def
val theWord_def = wordSemTheory.theWord_def
val is_fwd_ptr_def = wordSemTheory.is_fwd_ptr_def
*)

(* HOL4 overload (expanded in the port):
     lookup = sptree$lookup *)

(* TODO: move *)
(* HOL4 type abbreviation (expanded in the port):
     state = ('a,'c,'ffi)wordSem$state *)

(* HOL4 ML code, not ported:
fun op by1 (q,tac) = q by (tac \\ NO_TAC)
infix 8 by1
*)

(* HOL4 ML code, not ported:
val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = old_drule (th |> GEN_ALL) \\ rpt (disch_then
  old_drule \\ fs [])
*)

(* -- *)

(* -------------------------------------------------------
    word_ml_inv: definition and lemmas
   ------------------------------------------------------- *)

let join_env_def = cake_define
  `join_env env vs =
     MAP (\(n,v). (THE ((sptree_lookup) ((n - 2) DIV 2) env),v))
       (FILTER (\(n,v). ~(n = 0) /\ EVEN n) vs)`;;

let flat_def = cake_define
  `flat x1 x2 =
        match (x1,x2) with
          (((Env _1 env:stack) :: xs),(StackFrame _2 _3 vs _4 :: ys))
            ->
        join_env env vs ++ flat xs ys
        | ((Exc _5 env _6 :: xs),(StackFrame _7 _8 vs _9 :: ys)) ->
        join_env env vs ++ flat xs ys
        | (_10,_11) -> []`;;

(* HOL4 ML code, not ported:
val DISJ_EQ_IMP = METIS_PROVE [] ``(~b \/ c) <=> (b ==> c)``
*)

let can_select_def = cake_define
  `can_select k n w <=> ((word_bits (k - 1) n) (w << n) = w)`;;

let is_Ref_def = cake_define
  `is_Ref is_ref_tag x2 =
      match x2 with
        DataElement xs l r -> is_ref_tag r
      | _12 -> F`;;

let len_inv_def = cake_define
  `len_inv s <=>
     heap_length (gc_state_heap s) =
     heap_length (gc_state_h1 s ++ gc_state_h2 s) + gc_state_n s +
       heap_length (gc_state_r4 s ++ gc_state_r3 s ++ gc_state_r2 s
       ++ gc_state_r1 s)`;;

let word_heap_parts_def = cake_define
  `word_heap_parts conf p s xs =
     word_heap p (gc_state_h1 s ++ gc_state_h2 s) conf *
     word_list (p + bytes_in_word * n2w (heap_length (gc_state_h1 s
       ++ gc_state_h2 s))) xs *
     word_heap (p + bytes_in_word * n2w (heap_length (gc_state_h1 s
       ++ gc_state_h2 s) + LENGTH xs))
       (gc_state_r4 s ++ gc_state_r3 s ++ gc_state_r2 s ++
         gc_state_r1 s) conf`;;

let muttag_header_def = cake_define
  `muttag_header x1 =
      match x1 with
        ThunkTag e -> (thunk_tag_to_bits e << 3 || (n2w 6))
      | _13 -> (n2w 2)`;;

let partial_len_inv_def = cake_define
  `partial_len_inv s <=>
     heap_length (gc_state_heap s) =
     heap_length (gc_state_h1 s ++ gc_state_h2 s) + gc_state_n s +
       heap_length (gc_state_r4 s ++ gc_state_r3 s ++ gc_state_r2 s
       ++ gc_state_r1 s ++ gc_state_old s)`;;

let ends_with_refs_def = cake_define
  `ends_with_refs rs heap =
     (?h1 h2. heap_split rs heap = SOME (h1,h2) /\ EVERY isRef h2)`;;

let do_partial_def = cake_define
  `do_partial c s =
     (match data_to_word_config_gc_kind c with Generational l ->
       word_gen_gc_can_do_partial l s | _14 -> F)`;;

let alloc_size_def = cake_define
  `alloc_size k = ((if k * (dimindex (:'a) DIV 8) < dimword (:'ga) then
                     n2w (k * (dimindex (:'a) DIV 8)) else (--(n2w
                       1))):'a word)`;;

(* -------------------------------------------------------
    definition of state relation
   ------------------------------------------------------- *)

let code_rel_def = cake_define
  `data_to_word_gcProof_code_rel c s_code (t_code:(num#'a wordLang_prog)
  spt) <=>
     domain t_code = domain s_code UNION set_of_list (MAP FST (stubs
       (:'a) c)) /\
     EVERY (\(n,x). (sptree_lookup) n t_code = SOME x) (stubs (:'a)
       c) /\
     (!n arg_count prog.
       ((sptree_lookup) n s_code = SOME ((arg_count:num),prog)) ==>
       ((sptree_lookup) n t_code = SOME (arg_count + 1,FST (comp c
         n 2 prog))))`;;
hol4_overload "code_rel" "data_to_word_gcProof_code_rel";;

let stack_rel_def = cake_define
  `data_to_word_gcProof_stack_rel x1 x2 =
        match (x1,x2) with
          ((Env s1 env:stack),StackFrame s2 ws vs NONE) ->
        EVERY (\(x1,x2). ~(x1 = 0) /\ EVEN x1) vs /\ s1 = s2 /\
        EVERY (\(x1,x2). x1 = 0) ws /\
        ALL_DISTINCT (MAP FST vs) /\
        (!n. IS_SOME ((sptree_lookup) n env) <=>
            IS_SOME ((sptree_lookup) (adjust_var n) (fromAList vs)))
        | ((Exc s1 env n),(StackFrame s2 ws vs (SOME (x1,x2,x3)))) ->
        data_to_word_gcProof_stack_rel (Env s1 env) (StackFrame s2 ws
          vs NONE) /\ (x1 = n)
        | (_15,_16) -> F`;;
hol4_overload "stack_rel" "data_to_word_gcProof_stack_rel";;

let the_global_def = cake_define
  `the_global g = the (Number (&0)) (OPTION_MAP (RefPtr T) g)`;;

let contains_loc_def = cake_define
  `contains_loc (StackFrame _17 vs _18 _19) (l1,l2) = (ALOOKUP vs 0 =
  SOME (Loc l1 l2))`;;

let code_oracle_rel_def = cake_define
  `code_oracle_rel c (s_compile:'c->(num#num#dataLang_prog) list->(word8
  list#word64 list#'c) option)
       s_compile_oracle t_store (t_compile:'c->(num#num#'a
         wordLang_prog) list->(word8 list#('a word) list#'c) option)
       t_compile_oracle t_code_buffer t_data_buffer <=> buffer_buffer
     t_code_buffer = [] /\ buffer_buffer
     t_data_buffer = [] /\
     FLOOKUP t_store CodeBuffer = SOME (Word (buffer_position
       t_code_buffer)) /\
     FLOOKUP t_store CodeBufferEnd =
       SOME (Word (buffer_position t_code_buffer + n2w
         (buffer_space_left t_code_buffer))) /\
     FLOOKUP t_store BitmapBuffer = SOME (Word (buffer_position
       t_data_buffer)) /\
     FLOOKUP t_store BitmapBufferEnd =
       SOME (Word (buffer_position t_data_buffer +
                   bytes_in_word * n2w (buffer_space_left
                     t_data_buffer))) /\
     s_compile = (\cfg. OPTION_MAP (I ## MAP upper_w2w ## I) o
       t_compile cfg o
                        MAP (compile_part c)) /\
     t_compile_oracle = (I ## MAP (compile_part c)) o
       s_compile_oracle /\
     (!n. EVERY (\(n,_20). data_num_stubs <= n) (SND
       (s_compile_oracle n)))`;;

let limits_inv_def = cake_define
  `limits_inv (lims:limits) heaplength t_stack_limit c_len_size
  c_has_fp_ops c_has_fp_tern <=> ?_stack_limit
     lims = t_stack_limit /\ limits_length_limit
     lims = c_len_size /\ limits_arch_64_bit
     lims = (dimindex (:'a) = 64) /\
     heaplength = SOME (Word (bytes_in_word * (n2w (limits_heap_limit
       lims):'a word))) /\ limits_heap_limit
     lims * w2n (bytes_in_word:'a word) < dimword (:'a) /\
       ?_has_fp_ops
     lims = c_has_fp_ops /\ limits_has_fp_tops
     lims = c_has_fp_tern`;;

(* HOL4 ML code, not ported:
val s = ``(s:('c,'ffi) dataSem$state)``
*)

let state_rel_thm = cake_define
  `(\x y. strcat x y)
     (state_rel c l1 l2) (s (t:('a,'c,'ffi)wordSem_state) v1 locs)
       <=>
       (?_ffi t = ?_ffi s) /\
       (?_clock t = ?_clock s) /\
       (?_handler t = ?_handler s) /\
       (wordSem_state_gc_fun t = word_gc_fun c) /\
       code_rel c (?_code s) (?_code t) /\
       code_oracle_rel c (?_compile s) (?_compile_oracle s)
         (wordSem_state_store t) (?_compile
         t) (?_compile_oracle t) (?_code_buffer t)
           (wordSem_state_data_buffer t) /\
       good_dimindex (:'a) /\
       shift_length c < dimindex (:'a) /\
       IS_SOME (dataSem_state_tstamps s) /\
       EVERY (\n. n IN FDOM (wordSem_state_store t)) [Globals] /\
       (v1 = NONE ==> (sptree_lookup) 0 (?_locals t) = SOME (Loc l1
         l2)) /\
       (!n. IS_SOME ((sptree_lookup) n (?_locals s)) ==>
            IS_SOME ((sptree_lookup) (adjust_var n) (?_locals t))) /\
       EVERY2 stack_rel (?_stack s) (?_stack t) /\
       EVERY2 contains_loc (?_stack t) locs /\
       option_le (OPTION_MAP2 (+) (stack_size (?_stack t))
         (?_locals_size t)) (?_stack_max t) /\
       option_le (?_stack_max t) (?_stack_max s) /\
         wordSem_state_stack_size
       t = dataSem_state_stack_frame_sizes s /\ ?_locals_size
       t = ?_locals_size s /\
       limits_inv (dataSem_state_limits s) (FLOOKUP
         (wordSem_state_store t) HeapLength) (?_stack_limit t)
         (data_to_word_config_len_size c) (?_has_fp_ops c)
         (data_to_word_config_has_fp_tern c) /\
       memory_rel c (?_be t) (THE (dataSem_state_tstamps s)) (?_refs
         s) (dataSem_state_space s) (wordSem_state_store t)
         (wordSem_state_memory t) (wordSem_state_mdomain t)
         ((match v1 with NONE -> [] | SOME vs -> vs) ++
          join_env (?_locals s) (toAList (inter (?_locals t)
            (adjust_set (?_locals s)))) ++
          [(the_global (dataSem_state_global s),FAPPLY
            (wordSem_state_store t) Globals)] ++
          flat (?_stack s) (?_stack t))`;;

(* the relation places no constraint on the FP registers *)

(* -------------------------------------------------------
    init
   ------------------------------------------------------- *)

let init_store_ok_def = cake_define
  `init_store_ok c store m (dm:'a word->bool) code_buffer' data_buffer'
  <=>
     (?limit curr.
       limit <= max_heap_limit (:'a) c /\
       FLOOKUP store Globals = SOME (Word (n2w 0)) /\
       FLOOKUP store GlobReal = SOME (Word curr) /\
       FLOOKUP store GenStart = SOME (Word (n2w 0)) /\
       FLOOKUP store CurrHeap = SOME (Word curr) /\
       FLOOKUP store OtherHeap = FLOOKUP store EndOfHeap /\
       FLOOKUP store NextFree = SOME (Word curr) /\
       FLOOKUP store EndOfHeap =
         SOME (Word (curr + bytes_in_word * n2w limit)) /\
       FLOOKUP store TriggerGC =
         SOME (Word (match data_to_word_config_gc_kind c with
           Generational _21 -> curr | _22 -> curr + bytes_in_word * n2w
           limit)) /\
       FLOOKUP store HeapLength =
         SOME (Word (bytes_in_word * n2w limit)) /\
       FLOOKUP store CodeBuffer = SOME (Word (buffer_position
         code_buffer')) /\
       FLOOKUP store CodeBufferEnd =
         SOME (Word (buffer_position code_buffer' + n2w
           (buffer_space_left code_buffer'))) /\
       FLOOKUP store BitmapBuffer = SOME (Word (buffer_position
         data_buffer')) /\
       FLOOKUP store BitmapBufferEnd = SOME
         (Word (buffer_position data_buffer' +
                bytes_in_word * n2w (buffer_space_left
                  data_buffer'))) /\ buffer_buffer
       code_buffer' = [] /\ buffer_buffer
       data_buffer' = [] /\
       (word_list_exists curr (limit + limit)) (fun2set (m,dm)) /\
       byte_aligned curr)`;;

(* -------------------------------------------------------
    compiler proof
   ------------------------------------------------------- *)

let mk_loc_def = cake_define
  `mk_loc (SOME (t1,d1,d2)) = Loc d1 d2`;;

(* HOL4 ML code, not ported:
val s1 = mk_var("s1",type_of s);
*)

let inc_clock_def = cake_define
  `data_to_word_gcProof_inc_clock n (t:('a,'c,'ffi)wordSem_state) =
  ?_clock_fupd (K (?_clock t + n)) t`;;
hol4_overload "inc_clock" "data_to_word_gcProof_inc_clock";;

(* HOL4 ML code, not ported:
val s' = mk_var("s'",type_of s);
*)

let loc_ok_def = cake_define
  `loc_ok x1 =
      match x1 with
        (Loc m n:dataSem_v) -> (n = 0)
      | _23 -> T`;;

(* HOL4 ML code, not ported:
val IMP_EQ_DISJ = METIS_PROVE [] ``(b1 ==> b2) <=> ~b1 \/ b2``
*)

let loc_merge_def = cake_define_list
  [`loc_merge [] ys = []`;
   `loc_merge ((Loc l1 l2:word_loc) :: xs) ys = Loc l1 l2 ::
  loc_merge xs ys`;
   `loc_merge ((Word w:word_loc) :: xs) (y :: ys) = y :: loc_merge xs
  ys`;
   `loc_merge ((Word w:word_loc) :: xs) [] = Word w :: xs`];;

let traverse_heap = cake_inductive
  `(!heap p1.
      traverse_heap heap p1 [] p1) /\
   (!heap vs1 vs2 vars p1 p2 p3.
      traverse_heap heap p1 vs1 p2 /\
      traverse_heap heap p2 vs2 p3 /\
      set_of_list vars = set_of_list (vs1 ++ vs2) ==>
      traverse_heap heap p1 vars p3) /\
   (!heap p1 d.
      traverse_heap heap p1 [Data d] p1) /\
   (!heap p1 n t.
      MEM n p1 ==>
      traverse_heap heap p1 [Pointer n t] p1) /\
   (!heap p1 n t p2 xs l d.
      heap_lookup n heap = SOME (DataElement xs l d) /\
      traverse_heap heap (n :: p1) xs p2 ==>
      traverse_heap heap p1 [Pointer n t] p2)`;;

(* Root-set-generalised alloc chain: the _gen theorems bound the
   NotEnoughSpace
   heap usage over any roots2 with PERM roots2 (dups ++ canonical roots)
     and
   set dups SUBSET roots.  alloc_lemma / AllocVar_thm are corollaries
     (dups:=[]);
   AllocVar_thm_nary supplies the args-prepended narrow cut as roots2.
     *)


let cut_locals_def = cake_define
  `cut_locals names (s:('a,'b)dataSem_state) =
     (match dataSem_cut_env names (?_locals s) with SOME env ->
       ?_locals_fupd (K env) s | NONE -> ?_locals_fupd (K LN) s)`;;

(* HOL4 ML code, not ported:
val do_app = LIST_CONJ [dataSemTheory.do_app_def,do_space_def,
  data_spaceTheory.op_space_req_def,
  dataLangTheory.op_space_reset_def,
  dataSemTheory.do_app_aux_def]
*)
(* HOL4 ML code, not ported:
val alloc_alt_gen =
  SPEC_ALL alloc_lemma_gen
  |> ConseqConv.WEAKEN_CONSEQ_CONV_RULE
     (ConseqConv.CONSEQ_REWRITE_CONV
        ([],[],[prove(``alloc_size k <> -1w ==> T``,fs [])]))
  |> GEN_ALL;
*)

(* HOL4 ML code, not ported:
val alloc_alt =
  SPEC_ALL alloc_lemma
  |> ConseqConv.WEAKEN_CONSEQ_CONV_RULE
     (ConseqConv.CONSEQ_REWRITE_CONV
        ([],[],[prove(``alloc_size k ≠ -1w ==> T``,fs [])]))
  |> GEN_ALL
*)

(* HOL4 ML code, not ported:
val alloc_fail_lemma = alloc_lemma
  |> Q.INST [`k`|->`dimword (:'a)`]
  |> SIMP_RULE std_ss [UNDISCH alloc_size_dimword]
  |> DISCH_ALL |> MP_CANON
  |> SIMP_RULE std_ss [AC ADD_COMM ADD_ASSOC]
*)

let join_env_locals_def = cake_define
  `join_env_locals sl tl =
     join_env sl (toAList (inter tl (adjust_set sl)))`;;
