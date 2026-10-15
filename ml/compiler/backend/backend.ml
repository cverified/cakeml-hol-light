(* ======================================================== *)
(*  backend: ported from HOL4's
    compiler/backend/backendScript.sml  *)
(* ======================================================== *)

(*
  Composes all of the compiler phases within the compiler backend into
  a single compile function which is connected (in
    ../compilerScript.sml)
  to the front-end, i.e. parsing and type inference.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/jsonLang.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/presLang.ml";;
needs "compiler/backend/source_to_flat.ml";;
needs "compiler/backend/source_to_source.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_copy.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_to_stack.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/primTypes.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

let backend_config_FIELDS = define_record "backend_config"
  ["source_conf","source_to_flat_config";
   "clos_conf","clos_to_bvl_config";
   "bvl_conf","bvl_to_bvi_config";
   "data_conf","data_to_word_config";
   "word_to_word_conf","word_to_word_config";
   "word_conf","word_to_stack_config";
   "stack_conf","stack_to_lab_config";
   "lab_conf","lab_to_target_config";
   "symbols","(mlstring#num#num) list";
   "tap_conf","tap_config";
   "exported","mlstring list"];;

(* HOL4 ML code, not ported:
val config_component_equality = theorem"config_component_equality";
*)

let attach_bitmaps_def = cake_define_list
  [`attach_bitmaps names c bm (SOME (bytes,c')) =
        SOME (bytes,bm,backend_config_symbols_fupd (K (MAP
          (\(n,p,l). (lookup_any n names (implode "NOTFOUND"),p,l))
          (lab_to_target_config_sec_pos_len c')))
          (backend_config_lab_conf_fupd (K c')
              c))`;
   `attach_bitmaps names c bm NONE = NONE`];;

let compile_def = cake_define
  `backend_compile asm_conf c p =
     (let p = source_to_source_compile p in
     let _1 = empty_ffi (implode "finished: source_to_source") in
     let (c',p) = source_to_flat_compile (backend_config_source_conf
       c) p in
     let _2 = empty_ffi (implode "finished: source_to_flat") in
     let c = backend_config_source_conf_fupd (K c') c in
     let p = flat_to_clos_compile_prog p in
     let _3 = empty_ffi (implode "finished: flat_to_clos") in
     let (c',p,names) = clos_to_bvl_compile (backend_config_clos_conf
       c) p in
     let c = backend_config_clos_conf_fupd (K c') c in
     let _4 = empty_ffi (implode "finished: clos_to_bvl") in
     let (s,p,l,bl,n1,n2,n3,names) = bvl_to_bvi_compile
       (clos_to_bvl_config_start (backend_config_clos_conf c))
       (backend_config_bvl_conf c) names p in
     let c = backend_config_clos_conf_fupd (\c.
       clos_to_bvl_config_start_fupd (K s) c) c in
     let c = backend_config_bvl_conf_fupd (\c.
       bvl_to_bvi_config_next_name3_fupd (K n3)
       (bvl_to_bvi_config_next_name2_fupd (K n2)
       (bvl_to_bvi_config_next_name1_fupd (K n1)
       (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
       (bvl_to_bvi_config_inlines_fupd (K l) c))))) c in
     let _5 = empty_ffi (implode "finished: bvl_to_bvi") in
     let p = bvi_to_data_compile_prog p in
     let _6 = empty_ffi (implode "finished: bvi_to_data") in
     let (col,p) = data_to_word_compile (backend_config_data_conf c)
       (backend_config_word_to_word_conf c) asm_conf p in
     let c = backend_config_word_to_word_conf_fupd (\c.
       word_to_word_config_col_oracle_fupd (K col) c) c in
     let names = sptree_union (fromAList (data_to_word_stub_names one
       ++
       word_to_stack_stub_names one ++ stack_alloc_stub_names one ++
       stack_remove_stub_names one)) names in
     let _7 = empty_ffi (implode "finished: data_to_word") in
     let (bm,c',fs,p) = word_to_stack_compile asm_conf
       (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p
       in
     let c = backend_config_word_conf_fupd (K c') c in
     let _8 = empty_ffi (implode "finished: word_to_stack") in
     let p = stack_to_lab_compile (backend_config_stack_conf
       c) (backend_config_data_conf c) (2 * max_heap_limit (:'a)
         (backend_config_data_conf c) - 1)
       (asm_config_reg_count asm_conf - (LENGTH
         (asm_config_avoid_regs asm_conf) + 3))
       (asm_config_addr_offset asm_conf) p in
     let _9 = empty_ffi (implode "finished: stack_to_lab") in
     let res = attach_bitmaps names c bm
       (lab_to_target_compile asm_conf (backend_config_lab_conf c)
         (p:'a labLang_prog)) in
     let _10 = empty_ffi (implode "finished: lab_to_target") in
       res)`;;
hol4_overload "compile" "backend_compile";;

let to_flat_def = cake_define
  `to_flat c p =
     (let p = source_to_source_compile p in
     let (c',p) = source_to_flat_compile (backend_config_source_conf
       c) p in
     let c = backend_config_source_conf_fupd (K c') c in
     (c,p))`;;

let to_clos_def = cake_define
  `to_clos c p =
   (let (c,p) = to_flat c p in
   let p = flat_to_clos_compile_prog p in
   (c,p))`;;

let to_bvl_def = cake_define
  `to_bvl c p =
   (let (c,p) = to_clos c p in
   let (c',p,names) = clos_to_bvl_compile (backend_config_clos_conf
     c) p in
   let c = backend_config_clos_conf_fupd (K c') c in
   (c,p,names))`;;

let to_bvi_def = cake_define
  `to_bvi c p =
   (let (c,p,names) = to_bvl c p in
   let (s,p,l,bl,n1,n2,n3,names) = bvl_to_bvi_compile
     (clos_to_bvl_config_start (backend_config_clos_conf c))
     (backend_config_bvl_conf c) names p in
   let names = sptree_union (fromAList (data_to_word_stub_names one
     ++
     word_to_stack_stub_names one ++ stack_alloc_stub_names one ++
     stack_remove_stub_names one)) names in
   let c = backend_config_clos_conf_fupd (\c.
     clos_to_bvl_config_start_fupd (K s) c) c in
   let c = backend_config_bvl_conf_fupd (\c.
     bvl_to_bvi_config_next_name3_fupd (K n3)
     (bvl_to_bvi_config_next_name2_fupd (K n2)
     (bvl_to_bvi_config_next_name1_fupd (K n1)
     (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
     (bvl_to_bvi_config_inlines_fupd (K l) c))))) c in
   (c,p,names))`;;

let to_data_def = cake_define
  `to_data c p =
   (let (c,p,names) = to_bvi c p in
   let p = bvi_to_data_compile_prog p in
   (c,p,names))`;;

let to_word_0_def = cake_define
  `to_word_0 asm_conf c p =
     (let (c,p,names) = to_data c p in
     let p = compile_0 (backend_config_data_conf c) asm_conf p in
       (c,p,names))`;;

let to_word_def = cake_define
  `to_word asm_conf c p =
   (let (c,p,names) = to_data c p in
   let (col,p) = data_to_word_compile (backend_config_data_conf c)
     (backend_config_word_to_word_conf c) asm_conf p in
   let c = backend_config_word_to_word_conf_fupd (\c.
     word_to_word_config_col_oracle_fupd (K col) c) c in
   (c,p,names))`;;

let to_stack_def = cake_define
  `to_stack asm_conf c p =
   (let (c,p,names) = to_word asm_conf c p in
   let (bm,c',fs,p) = word_to_stack_compile asm_conf
     (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
   let c = backend_config_word_conf_fupd (K c') c in
   (bm,c,p,names))`;;

let to_lab_def = cake_define
  `to_lab asm_conf c p =
   (let (bm,c,p,names) = to_stack asm_conf c p in
   let p = stack_to_lab_compile (backend_config_stack_conf
     c) (backend_config_data_conf c) (2 * max_heap_limit (:'a)
       (backend_config_data_conf c) - 1)
     (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs
       asm_conf) + 3))
     (asm_config_addr_offset asm_conf) p in
   (bm,c,(p:'a labLang_prog),names))`;;

let to_target_def = cake_define
  `to_target asm_conf c p =
   (let (bm,c,p,names) = to_lab asm_conf c p in
     attach_bitmaps names c bm (
       lab_to_target_compile
         asm_conf (backend_config_lab_conf c) p))`;;

let prim_src_config_def = cake_define
  `prim_src_config =
     (let (_11,next,env,_12,_13) = compile_decs [] 1 (?_next
       empty_config) empty_env
         ARB prim_types_program in
     (source_to_flat_config_mod_env_fupd (K env) (?_next_fupd (K
       next) empty_config)))`;;

let prim_config_def = cake_define
  `prim_config =
     FST (to_flat (mk_backend_config empty_config ARB ARB ARB ARB
       ARB ARB ARB ARB ARB ARB) (prim_types_program))`;;

let from_lab_def = cake_define
  `from_lab asm_conf c names p bm =
     attach_bitmaps names c bm
       (lab_to_target_compile asm_conf (backend_config_lab_conf c)
         p)`;;

let from_stack_def = cake_define
  `from_stack asm_conf c names p bm =
   (let p = stack_to_lab_compile (backend_config_stack_conf
     c) (backend_config_data_conf c) (2 * max_heap_limit (:'a)
       (backend_config_data_conf c) - 1)
     (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs
       asm_conf) + 3))
     (asm_config_addr_offset asm_conf) p in
   from_lab asm_conf c names (p:'a labLang_prog) bm)`;;

let from_word_def = cake_define
  `from_word asm_conf c names p =
   (let (bm,c',fs,p) = word_to_stack_compile asm_conf
     (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
   let c = backend_config_word_conf_fupd (K c') c in
   from_stack asm_conf c names p bm)`;;

let from_word_0_def = cake_define
  `from_word_0 asm_conf c names p =
   (let (col,prog) = word_to_word_compile
     (backend_config_word_to_word_conf c) asm_conf p in
   let c = backend_config_word_to_word_conf_fupd (\c.
     word_to_word_config_col_oracle_fupd (K col) c) c in
   from_word asm_conf c names prog)`;;

let from_data_def = cake_define
  `from_data asm_conf c names p =
   (let (col,p) = data_to_word_compile (backend_config_data_conf c)
     (backend_config_word_to_word_conf c) asm_conf p in
   let c = backend_config_word_to_word_conf_fupd (\c.
     word_to_word_config_col_oracle_fupd (K col) c) c in
   from_word asm_conf c names p)`;;

let from_bvi_def = cake_define
  `from_bvi asm_conf c names p =
   (let p = bvi_to_data_compile_prog p in
     from_data asm_conf c names p)`;;

let from_bvl_def = cake_define
  `from_bvl asm_conf c names p =
   (let (s,p,l,bl,n1,n2,n3,names) = bvl_to_bvi_compile
     (clos_to_bvl_config_start (backend_config_clos_conf c))
     (backend_config_bvl_conf c) names p in
   let names = sptree_union (fromAList (data_to_word_stub_names one
     ++
     word_to_stack_stub_names one ++ stack_alloc_stub_names one ++
     stack_remove_stub_names one)) names in
   let c = backend_config_clos_conf_fupd (\c.
     clos_to_bvl_config_start_fupd (K s) c) c in
   let c = backend_config_bvl_conf_fupd (\c.
     bvl_to_bvi_config_next_name3_fupd (K n3)
     (bvl_to_bvi_config_next_name2_fupd (K n2)
     (bvl_to_bvi_config_next_name1_fupd (K n1)
     (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
     (bvl_to_bvi_config_inlines_fupd (K l) c))))) c in
   from_bvi asm_conf c names p)`;;

let from_clos_def = cake_define
  `from_clos asm_conf c e =
   (let (c',p,names) = clos_to_bvl_compile (backend_config_clos_conf
     c) e in
   let c = backend_config_clos_conf_fupd (K c') c in
   from_bvl asm_conf c names p)`;;

let from_flat_def = cake_define
  `from_flat asm_conf c p =
   (let p = flat_to_clos_compile_prog p in
   from_clos asm_conf c p)`;;

let from_source_def = cake_define
  `from_source asm_conf c p =
   (let p = source_to_source_compile p in
   let (c',p) = source_to_flat_compile (backend_config_source_conf c)
     p in
   let c = backend_config_source_conf_fupd (K c') c in
   from_flat asm_conf c p)`;;

let to_livesets_0_def = cake_define
  `to_livesets_0 asm_conf ((c:backend_config),p,(names:mlstring spt)) =
   (let word_conf = backend_config_word_to_word_conf c in
   let alg = word_to_word_config_reg_alg word_conf in
   let p =
     MAP (\(name_num,arg_count,prog).
     let prog = word_simp_compile_exp prog in
     let maxv = max_var prog + 1 in
     let inst_prog = inst_select asm_conf maxv prog in
     let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
     let rm_ssa_prog = remove_dead_prog ssa_prog in
     let cse_prog = word_common_subexp_elim rm_ssa_prog in
     let cp_prog = copy_prop cse_prog in
     let two_prog = three_to_two_reg_prog (asm_config_two_reg_arith
       asm_conf) cp_prog in
     let unreach_prog = remove_unreach two_prog in
     let rm_prog = remove_dead_prog unreach_prog in
         (name_num,arg_count,rm_prog))
       p in
     let data = MAP (\(name_num,arg_count,prog).
     let (heu_moves,spillcosts) = get_heuristics alg name_num prog in
     (get_clash_tree prog [],heu_moves,spillcosts,
       get_forced asm_conf prog [],get_stack_only prog)) p in
     ((asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf)),data),c,names,p))`;;

let to_livesets_def = cake_define
  `to_livesets asm_conf c p =
     to_livesets_0 asm_conf (to_word_0 asm_conf c p)`;;

let from_livesets_def = cake_define
  `from_livesets asm_conf ((k,data),c,names,p) =
   (let word_conf = backend_config_word_to_word_conf c in
   let (n_oracles,col) = next_n_oracle (LENGTH p)
     (word_to_word_config_col_oracle word_conf) in
   let alg = word_to_word_config_reg_alg word_conf in
   let prog_with_oracles = ZIP n_oracles (ZIP data p) in
   let p =
     MAP
       (\(col_opt,((tree,heu_moves,spillcosts,forced,fs),name_num
       ,arg_count,prog)).
       match oracle_colour_ok k col_opt tree prog forced with
         NONE ->
           (let cp =
             (match select_reg_alloc alg spillcosts k heu_moves tree
               forced fs with
               M_success col ->
                 (apply_colour (total_colour col) prog) | M_failure
                   _14 -> prog) in
           (name_num,arg_count,remove_must_terminate cp)) | SOME
             col_prog -> (name_num,arg_count,remove_must_terminate
             col_prog)) prog_with_oracles in
   let c = backend_config_word_to_word_conf_fupd (\c.
     word_to_word_config_col_oracle_fupd (K col) c) c in
   from_word asm_conf c names p)`;;

(* TODO delete?
Theorem to_livesets_invariant:
  wc.reg_alg = c.word_to_word_conf.reg_alg ⇒
  to_livesets asm_conf (c with word_to_word_conf:=wc) p =
  let (rcm,c,p) = to_livesets asm_conf c p in
    (rcm,c with word_to_word_conf:=wc,p)
Proof
  srw_tac[][FUN_EQ_THM,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_flat_def,to_livesets_def] >>
  unabbrev_all_tac>>fs[]>>
  rpt(rfs[]>>fs[])
QED

Theorem to_livesets_0_invariant:
  (wc.reg_alg = c.word_to_word_conf.reg_alg) ⇒
  (to_livesets_0 (c with word_to_word_conf:=wc,p,names) =
  let (rcm,c,p) = to_livesets_0 (c,p,names) in
    (rcm,c with word_to_word_conf:=wc,p))
Proof
  rw[FUN_EQ_THM,to_livesets_0_def]
QED
*)

let ensure_fp_conf_ok_def = cake_define
  `ensure_fp_conf_ok asm_c c = data_to_word_config_has_fp_tern_fupd (K
  (asm_config_ISA asm_c = ARMv7 /\ 2 < asm_config_fp_reg_count asm_c))
  (data_to_word_config_has_fp_ops_fupd (K (1 < asm_config_fp_reg_count
  asm_c))
   c)`;;

(* HOL4 overload (expanded in the port):
     bvl_inline_compile_prog = bvl_inline$compile_prog *)
(* HOL4 overload (expanded in the port):
     bvi_tailrec_compile_prog = bvi_tailrec$compile_prog *)
(* HOL4 overload (expanded in the port):
     bvi_to_data_compile_prog = bvi_to_data$compile_prog *)
(* HOL4 overload (expanded in the port):
     bvl_to_bvi_compile_prog = bvl_to_bvi$compile_prog *)
(* HOL4 overload (expanded in the port):
     bvl_to_bvi_compile_inc = bvl_to_bvi$compile_inc *)
(* HOL4 overload (expanded in the port):
     bvl_to_bvi_compile = bvl_to_bvi$compile *)
(* HOL4 overload (expanded in the port):
     bvi_to_data_compile = bvi_to_data$compile *)
(* HOL4 overload (expanded in the port):
     bvi_let_compile = bvi_let$compile *)
(* HOL4 overload (expanded in the port):
     bvl_const_compile = bvl_const$compile *)
(* HOL4 overload (expanded in the port):
     bvl_handle_compile = bvl_handle$compile *)
(* HOL4 overload (expanded in the port):
     bvl_inline_compile_inc = bvl_inline$compile_inc *)
(* HOL4 overload (expanded in the port):
     bvl_to_bvi_compile_exps = bvl_to_bvi$compile_exps *)
(* HOL4 overload (expanded in the port):
     flat_to_clos_inc_compile = flat_to_clos$inc_compile_decs *)
(* HOL4 overload (expanded in the port):
     stack_remove_prog_comp = stack_remove$prog_comp *)
(* HOL4 overload (expanded in the port):
     stack_alloc_prog_comp = stack_alloc$prog_comp *)
(* HOL4 overload (expanded in the port):
     stack_names_prog_comp = stack_names$prog_comp *)

let backend_progs_FIELDS = define_record "backend_progs"
  ["env_id","num#num";
   "source_prog","dec list";
   "flat_prog","flatLang_exp list";
   "clos_prog","closLang_exp list#(num#num#closLang_exp) list";
   "bvl_prog","(num#num#bvl_exp) list";
   "bvi_prog","(num#num#bvi_exp) list";
   "data_prog","(num#num#dataLang_prog) list";
   "word_prog","(num#num#'a wordLang_prog) list";
   "stack_prog","(num#'a stackLang_prog) list";
   "cur_bm","('a word) list";
   "lab_prog","('a sec) list";
   "target_prog","(word8 list#('a word) list) option"];;

let empty_progs_def = cake_define
  `empty_progs = mk_backend_progs (0,0) [] [] ([],[]) [] [] [] [] []
  [] [] (SOME ([],[]))`;;

let keep_progs_def = cake_define
  `keep_progs k ps = (match k with T -> ps | _15 -> [])`;;

let compile_inc_progs_def = cake_define
  `compile_inc_progs k asm_conf c p_tup =
     (let (env_id,p) = p_tup in
     let ps = backend_progs_source_prog_fupd (K p)
       (backend_progs_env_id_fupd (K env_id) empty_progs) in
     let p = source_to_source_compile p in
     let (c',p) = inc_compile env_id (backend_config_source_conf c) p
       in
     let ps = backend_progs_flat_prog_fupd (K (keep_progs k p)) ps in
     let c = backend_config_source_conf_fupd (K c') c in
     let p = (inc_compile_decs) p in
     let ps = backend_progs_clos_prog_fupd (K ((keep_progs k ##
       keep_progs k) p)) ps in
     let (c',p) = clos_to_bvl_compile_inc (backend_config_clos_conf
       c) p in
     let c = backend_config_clos_conf_fupd (K c') c in
     let ps = backend_progs_bvl_prog_fupd (K (keep_progs k p)) ps in
     let (c',p) = bvl_to_bvi_compile_inc_all (backend_config_bvl_conf
       c) p in
     let c = backend_config_bvl_conf_fupd (K c') c in
     let ps = backend_progs_bvi_prog_fupd (K (keep_progs k p)) ps in
     let p = (bvi_to_data_compile_prog) p in
     let ps = backend_progs_data_prog_fupd (K (keep_progs k p)) ps in
     let dc = ensure_fp_conf_ok asm_conf (backend_config_data_conf c)
       in
     let p = MAP (compile_part dc) p in
     let reg_count1 = asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf)) in
     let p = MAP (\p. full_compile_single (asm_config_two_reg_arith
       asm_conf) reg_count1 (word_to_word_config_reg_alg
       (backend_config_word_to_word_conf
         c)) asm_conf (p,NONE)) p in
     let ps = backend_progs_word_prog_fupd (K (keep_progs k p)) ps in
     let bm0 = word_to_stack_config_bitmaps_length
       (backend_config_word_conf c) in
     let (p,fs,bm) = compile_word_to_stack asm_conf
       (stack_to_lab_config_perf_calls (backend_config_stack_conf c))
       reg_count1 p (Nil,bm0) in
     let cur_bm = append (FST bm) in
     let c = backend_config_word_conf_fupd (K
       (word_to_stack_config_bitmaps_length_fupd (K (SND bm))
       (backend_config_word_conf c))) c in
     let ps = backend_progs_cur_bm_fupd (K cur_bm)
       (backend_progs_stack_prog_fupd (K (keep_progs k p)) ps) in
     let reg_count2 = asm_config_reg_count asm_conf - (3 + LENGTH
       (asm_config_avoid_regs asm_conf)) in
     let p = compile_no_stubs (stack_to_lab_config_reg_names
       (backend_config_stack_conf
         c)) (stack_to_lab_config_jump (backend_config_stack_conf c))
           (asm_config_addr_offset asm_conf)
         reg_count2 p in
     let ps = backend_progs_lab_prog_fupd (K (keep_progs k p)) ps in
     let target = lab_to_target_compile asm_conf
       (backend_config_lab_conf c) (p:'a labLang_prog) in
     let ps = backend_progs_target_prog_fupd (K (OPTION_MAP
         (\(bytes,_16). (bytes,cur_bm)) target)) ps in
     let c = backend_config_lab_conf_fupd (match target with NONE ->
       I | SOME (_17,c') -> K c') c in
     (c,ps))`;;
let compile_inc_progs_for_eval_def = cake_define
  `compile_inc_progs_for_eval asm_conf x =
   (let (env_id,c',decs) = x in
   let (c'',ps) = compile_inc_progs T asm_conf c' (env_id,decs) in
     OPTION_MAP (\(bs,ws). (c'',bs,MAP upper_w2w ws))
       (backend_progs_target_prog
         ps))`;;

let ffinames_to_string_list_def = cake_define_list
  [`ffinames_to_string_list [] = []`;
   `ffinames_to_string_list (ExtCall s :: rest) =
        s :: (ffinames_to_string_list rest)`;
   `ffinames_to_string_list (SharedMem _18 :: rest) =
        ffinames_to_string_list rest`];;

let set_oracle_def = cake_define
  `set_oracle c oracle = backend_config_word_to_word_conf_fupd (K
  (word_to_word_config_col_oracle_fupd (K oracle)
  (backend_config_word_to_word_conf c)))
     c`;;
