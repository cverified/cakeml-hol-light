(* ======================================================== *)
(*  stack_allocProof: ported from HOL4's
    compiler/backend/proofs/stack_allocProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for stack_alloc
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/word_bignum.ml";;
(* HOL4 ancestors outside the port: (* for memcpy *) *)

(* HOL4 ML code, not ported:
val _ = (max_print_depth := 18);
*)

(* HOL4 ML code, not ported:
val word_shift_def = backend_commonTheory.word_shift_def
val theWord_def = wordSemTheory.theWord_def;
val isWord_def = wordSemTheory.isWord_def;
val is_fwd_ptr_def = wordSemTheory.is_fwd_ptr_def;
*)

(* HOL4 overload (expanded in the port):
     good_dimindex = misc$good_dimindex *)

(* TODO: move and join with stack_remove *)

(* ---- *)

let get_bits_def = cake_define
  `get_bits w = GENLIST (\i. FAPPLY w i) (bit_length w - 1)`;;

(* HOL4 ML code, not ported:
val nine_less = DECIDE
  ``9 < n ==> n <> 0 /\ n <> 1 /\ n <> 2 /\ n <> 3 /\ n <> 4 /\
              n <> 5 /\ n <> 6 /\ n <> 7 /\ n <> 8 /\ n <> 9n``
*)

(* HOL4 ML code, not ported:
val tac = simp
  [list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,
       wordSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,word_shift_not_0,FLOOKUP_UPDATE];
*)

(* HOL4 ML code, not ported:
val tac1 = simp [Once list_Seq_def,
  evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,set_store_def,
       wordSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,word_shift_not_0,FLOOKUP_UPDATE];
*)

(* HOL4 ML code, not ported:
fun abbrev_under_exists tm tac =
  (fn state => (`?^(tm). ^(hd (fst (hd (fst (tac state)))))` by
        (fs [markerTheory.Abbrev_def] \\ NO_TAC)) state);
*)

(* gc_kind = Simple *)

(* HOL4 ML code, not ported:
val word_gc_fun_lemma =
  word_gc_fun_def
  |> SPEC_ALL
  |> DISCH ``conf.gc_kind = Simple``
  |> SIMP_RULE std_ss [TypeBase.case_def_of ``:gc_kind`` ]
  |> SIMP_RULE std_ss [word_full_gc_def]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM,word_gc_move_roots_def]
*)

(* HOL4 ML code, not ported:
val gc_lemma = gc_def
  |> SPEC_ALL
  |> DISCH ``s.gc_fun = word_gc_fun conf``
  |> SIMP_RULE std_ss [] |> UNDISCH
  |> DISCH ``conf.gc_kind = Simple``
  |> SIMP_RULE std_ss [word_gc_fun_thm] |> DISCH_ALL
*)

let word_gc_move_roots_bitmaps_def = cake_define
  `word_gc_move_roots_bitmaps conf (stack,bitmaps,i1,pa1,curr,m,dm) =
     (match enc_stack bitmaps stack with NONE -> (ARB,ARB,ARB,ARB,F)
       | SOME wl_list ->
         (let (wl,i2,pa2,m2,c2) =
             word_gc_move_roots conf (wl_list,i1,pa1,curr,m,dm) in
           match dec_stack bitmaps wl stack with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME stack ->
             (stack,i2,pa2,m2,c2)))`;;

let word_gc_move_bitmaps_def = cake_define
  `word_gc_move_bitmaps conf (w,stack,bitmaps,i1,pa1,curr,m,dm) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack with NONE -> NONE | SOME (ts,ws)
         ->
         (let (wl,i2,pa2,m2,c2) =
                 word_gc_move_roots conf (ts,i1,pa1,curr,m,dm) in
           match map_bitmap bs wl stack with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,m2,c2))))`;;

let word_gc_move_bitmap_def = cake_define
  `word_gc_move_bitmap conf (w,stack,i1,pa1,curr,m,dm) =
     (let bs = get_bits w in
       match filter_bitmap bs stack with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,m2,c2) = word_gc_move_roots conf
            (ts,i1,pa1,curr,m,dm) in
            match map_bitmap bs wl stack with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 ML code, not ported:
val map_bitmap_APPEND_APPEND = Q.prove(
  `!vs1 stack x0 x1 ws2 vs2 ws1.
      filter_bitmap vs1 stack = SOME (x0,x1) /\
      LENGTH x0 = LENGTH ws1 ==>
      map_bitmap (vs1 ++ vs2) (ws1 ++ ws2) stack =
      case map_bitmap vs1 ws1 stack of
      | NONE => NONE
      | SOME (ts1,ts2,ts3) =>
        case map_bitmap vs2 ws2 ts3 of
        | NONE => NONE
        | SOME (us1,us2,us3) => SOME (ts1++us1,ts2++us2,us3)`,
  Induct \\ full_simp_tac(srw_ss())[map_bitmap_def] THEN1
   (Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def]
    \\ once_rewrite_tac [EQ_SYM_EQ] \\
      full_simp_tac(srw_ss())[LENGTH_NIL]
    \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  \\ reverse Cases \\
    full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def]
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `ws1` \\ full_simp_tac(srw_ss())[LENGTH,map_bitmap_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [];
*)

(* HOL4 ML code, not ported:
val word_gc_move_bitmaps_Loc =
  ``word_gc_move_bitmaps conf (Loc l1
    l2,stack,bitmaps,i1,pa1,curr,m,dm)``
  |> SIMP_CONV std_ss [word_gc_move_bitmaps_def,full_read_bitmap_def];
*)

(* gc_kind = Generational *)

(* HOL4 ML code, not ported:
val kind = ``Generational gen_sizes``
*)

(* HOL4 ML code, not ported:
val word_gc_fun_lemma =
  word_gc_fun_def
  |> SPEC_ALL
  |> DISCH ``conf.gc_kind = ^kind``
  |> SIMP_RULE std_ss [TypeBase.case_def_of ``:gc_kind`` ]
  |> SIMP_RULE std_ss [word_gen_gc_def]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM]
  |> SIMP_RULE std_ss [Once LET_THM,word_gen_gc_move_roots_def]
*)

(* HOL4 ML code, not ported:
val gc_lemma = gc_def
  |> SPEC_ALL
  |> DISCH ``s.gc_fun = word_gc_fun conf``
  |> SIMP_RULE std_ss [] |> UNDISCH
  |> DISCH ``conf.gc_kind = ^kind``
  |> SIMP_RULE std_ss [word_gc_fun_thm] |> DISCH_ALL
*)

let word_gen_gc_move_roots_bitmaps_def = cake_define
  `word_gen_gc_move_roots_bitmaps conf
  (stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
     (match enc_stack bitmaps stack with NONE ->
       (ARB,ARB,ARB,ARB,ARB,ARB,F) | SOME wl_list ->
         (let (wl,i2,pa2,ib2,pb2,m2,c2) =
             word_gen_gc_move_roots conf
               (wl_list,i1,pa1,ib1,pb1,curr,m,dm) in
           match dec_stack bitmaps wl stack with NONE ->
             (ARB,ARB,ARB,ARB,ARB,ARB,F) | SOME stack ->
             (stack,i2,pa2,ib2,pb2,m2,c2)))`;;

let word_gen_gc_partial_move_roots_bitmaps_def = cake_define
  `word_gen_gc_partial_move_roots_bitmaps conf
  (stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
     (match enc_stack bitmaps stack with NONE -> (ARB,ARB,ARB,ARB,F)
       | SOME wl_list ->
         (let (wl,i2,pa2,m2,c2) =
             word_gen_gc_partial_move_roots conf
               (wl_list,i1,pa1,curr,m,dm,gs,rs) in
           match dec_stack bitmaps wl stack with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME stack ->
             (stack,i2,pa2,m2,c2)))`;;

let word_gen_gc_move_bitmaps_def = cake_define
  `word_gen_gc_move_bitmaps conf
  (w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack with NONE -> NONE | SOME (ts,ws)
         ->
         (let (wl,i2,pa2,ib2,pb2,m2,c2) =
                 word_gen_gc_move_roots conf
                   (ts,i1,pa1,ib1,pb1,curr,m,dm) in
           match map_bitmap bs wl stack with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2))))`;;

let word_gen_gc_partial_move_bitmaps_def = cake_define
  `word_gen_gc_partial_move_bitmaps conf
  (w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack with NONE -> NONE | SOME (ts,ws)
         ->
         (let (wl,i2,pa2,m2,c2) =
                 word_gen_gc_partial_move_roots conf
                   (ts,i1,pa1,curr,m,dm,gs,rs) in
           match map_bitmap bs wl stack with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,m2,c2))))`;;

let word_gen_gc_move_bitmap_def = cake_define
  `word_gen_gc_move_bitmap conf (w,stack,i1,pa1,ib1,pb1,curr,m,dm) =
     (let bs = get_bits w in
       match filter_bitmap bs stack with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,ib2,pb2,m2,c2) =
            word_gen_gc_move_roots conf (ts,i1,pa1,ib1,pb1,curr,m,dm)
              in
            match map_bitmap bs wl stack with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2)))`;;

let word_gen_gc_partial_move_bitmap_def = cake_define
  `word_gen_gc_partial_move_bitmap conf (w,stack,i1,pa1,curr,m,dm,gs,rs)
  =
     (let bs = get_bits w in
       match filter_bitmap bs stack with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,m2,c2) =
            word_gen_gc_partial_move_roots conf
              (ts,i1,pa1,curr,m,dm,gs,rs) in
            match map_bitmap bs wl stack with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 ML code, not ported:
val map_bitmap_APPEND_APPEND = Q.prove(
  `!vs1 stack x0 x1 ws2 vs2 ws1.
      filter_bitmap vs1 stack = SOME (x0,x1) /\
      LENGTH x0 = LENGTH ws1 ==>
      map_bitmap (vs1 ++ vs2) (ws1 ++ ws2) stack =
      case map_bitmap vs1 ws1 stack of
      | NONE => NONE
      | SOME (ts1,ts2,ts3) =>
        case map_bitmap vs2 ws2 ts3 of
        | NONE => NONE
        | SOME (us1,us2,us3) => SOME (ts1++us1,ts2++us2,us3)`,
  Induct \\ full_simp_tac(srw_ss())[map_bitmap_def] THEN1
   (Cases \\ full_simp_tac(srw_ss())[filter_bitmap_def]
    \\ once_rewrite_tac [EQ_SYM_EQ] \\
      full_simp_tac(srw_ss())[LENGTH_NIL]
    \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `stack` \\ full_simp_tac(srw_ss())[filter_bitmap_def]
  \\ reverse Cases \\
    full_simp_tac(srw_ss())[filter_bitmap_def,map_bitmap_def]
  THEN1 (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `ws1` \\ full_simp_tac(srw_ss())[LENGTH,map_bitmap_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  |> SIMP_RULE std_ss [];
*)

(* HOL4 ML code, not ported:
val word_gen_gc_move_bitmaps_Loc =
  ``word_gen_gc_move_bitmaps conf (Loc l1
    l2,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm)``
  |> SIMP_CONV std_ss
    [word_gen_gc_move_bitmaps_def,full_read_bitmap_def];
*)

(* HOL4 ML code, not ported:
val word_gen_gc_partial_move_bitmaps_Loc =
  ``word_gen_gc_partial_move_bitmaps conf (Loc l1
    l2,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs)``
  |> SIMP_CONV std_ss
    [word_gen_gc_partial_move_bitmaps_def,full_read_bitmap_def];
*)

(* gc_kind = None *)

(* --- *)

(* This proof is very slow! *)

(* HOL4 ML code, not ported:
val comp_correct_thm =
  comp_correct |> SPEC_ALL
  |> Q.INST [`regs`|->`s.regs`]
  |> REWRITE_RULE [SUBMAP_REFL];
*)
(* HOL4 ML code, not ported:
val _ = augment_srw_ss[rewrites[with_same_regs_lemma]];
*)

(* TODO: does this have to initialize the data_buffer to empty? *)
let make_init_def = cake_define
  `stack_allocProof_make_init c code oracle s = ?_compile_oracle_fupd (K
  oracle) (?_compile_fupd (K (\c. ?_compile s c o (MAP prog_comp)))
  (?_gc_fun_fupd (K (word_gc_fun c)) (stackSem_state_use_stack_fupd (K
  T) (stackSem_state_use_alloc_fupd (K T) (?_code_fupd (K code)
     s)))))`;;
