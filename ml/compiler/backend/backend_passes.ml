(* ======================================================== *)
(*  backend_passes: ported from HOL4's
    compiler/backend/backend_passesScript.sml
    A definition theory, with 18 definitions, 1 datatype and 20
    theorems.  Needed by backendProof.ml, compiler.ml and
    compilerProof.ml.  *)
(* ======================================================== *)

(*
  Reformulates compile definition to expose the result of each internal
  compiler pass
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_to_data.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/flat_elim.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_filter.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/presLang.ml";;
needs "compiler/backend/stack_remove.ml";;
needs "compiler/backend/stack_to_lab.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_copy.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "backend_passes"
  ["backend"; "presLang"];;


let any_prog_INDUCT,any_prog_RECURSION = define_datatype
  "any_prog = backend_passes_Source (dec list) | backend_passes_Flat \
   (flatLang_exp list) | backend_passes_Clos (closLang_exp list) \
   ((num#num#closLang_exp) list) | backend_passes_Bvl \
   ((num#num#bvl_exp) list) (mlstring spt) | backend_passes_Bvi \
   ((num#num#bvi_exp) list) (mlstring spt) | backend_passes_Data \
   ((num#num#dataLang_prog) list) (mlstring spt) | \
   backend_passes_Word ((num#num#'a wordLang_prog) list) (mlstring \
   spt) | backend_passes_Stack ((num#'a stackLang_prog) list) \
   (mlstring spt) | backend_passes_Lab (('a sec) list) (mlstring spt)";;
hol4_overload "Source" "backend_passes_Source";;
hol4_overload "Flat" "backend_passes_Flat";;
hol4_overload "Clos" "backend_passes_Clos";;
hol4_overload "Bvl" "backend_passes_Bvl";;
hol4_overload "Bvi" "backend_passes_Bvi";;
hol4_overload "Data" "backend_passes_Data";;
hol4_overload "Word" "backend_passes_Word";;
hol4_overload "Stack" "backend_passes_Stack";;
hol4_overload "Lab" "backend_passes_Lab";;

let to_flat_all_def = new_definition
  `to_flat_all (c:backend_config) p =
     (let ps = [] in
     let ps = APPEND ps [((implode
       "original source code"),backend_passes_Source p)] in
     let p = source_let_compile_decs p in
     let ps = APPEND ps [((implode
       "after source_let"),backend_passes_Source p)] in
     let (c',p) = source_to_flat_compile_prog
       (backend_config_source_conf c) p in
     let ps = APPEND ps [((implode
       "after source_to_flat"),backend_passes_Flat p)] in
     let p = remove_flat_prog p in
     let ps = APPEND ps [((implode
       "after remove_flat"),backend_passes_Flat p)] in
     let p = MAP (compile_dec (source_to_flat_config_pattern_cfg c'))
       p in
     let ps = APPEND ps [((implode
       "after flat_pattern"),backend_passes_Flat p)] in
     let c = backend_config_source_conf_fupd (K c') c in
       ((ps:(mlstring#'a any_prog) list),c,p))`;;

let to_flat_thm = prove
 (`SND (to_flat_all c p) = to_flat c p`,
  CHEAT_TAC);;

let to_clos_all_def = new_definition
  `to_clos_all (c:backend_config) p =
     (let (ps,c,p) = to_flat_all c p in
     let p = flat_to_clos_compile_prog p in
     let ps = APPEND ps [((implode "after flat_to_clos"),Clos p [])]
       in
       ((ps:(mlstring#'a any_prog) list),c,p))`;;

let to_clos_thm = prove
 (`SND (to_clos_all c p) = to_clos c p`,
  CHEAT_TAC);;

let to_bvl_all_def = new_definition
  `to_bvl_all (c:backend_config) p =
     (let (ps,c,es0) = to_clos_all c p in
     let c0 = backend_config_clos_conf c in
     let es = clos_mti_compile (clos_to_bvl_config_do_mti c0)
       (clos_to_bvl_config_max_app c0) es0 in
     let ps = APPEND ps [((implode "after clos_mti"),Clos es [])] in
     let loc = clos_to_bvl_config_next_loc c0 + MAX 1 (LENGTH es) in
     let loc = (if loc MOD 2 = 0 then loc else loc + 1) in
     let (n,es) = renumber_code_locs_list loc es in
     let ps = APPEND ps [((implode "after clos_number"),Clos es [])]
       in
     let (kc,es) = clos_known_compile (clos_to_bvl_config_known_conf
       c0) es in
     let ps = APPEND ps [((implode "after clos_known"),Clos es [])]
       in
     let (es,g,aux) = clos_call_compile (clos_to_bvl_config_do_call
       c0) es in
     let ps = APPEND ps [((implode "after clos_call"),Clos es aux)]
       in
     let prog = APPEND (chain_exps (clos_to_bvl_config_next_loc c0)
       es) aux in
     let prog = clos_annotate_compile prog in
     let ps = APPEND ps [((implode "after clos_annotate"),Clos []
       prog)] in
     let c1 = clos_to_bvl_config_call_state_fupd (K (g,aux))
       (clos_to_bvl_config_known_conf_fupd (K kc)
       (clos_to_bvl_config_next_loc_fupd (K n)
       (clos_to_bvl_config_start_fupd (K (clos_to_bvl_config_next_loc
       c0)) c0))) in
     let init_stubs' = toAList (init_code (clos_to_bvl_config_max_app
       c1)) in
     let init_globs =
             [(num_stubs (clos_to_bvl_config_max_app c1) -
               2,2,force_thunk_code);
              (num_stubs (clos_to_bvl_config_max_app c1) - 1,0,
               init_globals (clos_to_bvl_config_max_app c1)
                 (num_stubs (clos_to_bvl_config_max_app c1) +
                 clos_to_bvl_config_start c1))] in
     let comp_progs = clos_to_bvl_compile_prog
       (clos_to_bvl_config_max_app c1) prog in
     let prog' = APPEND (APPEND init_stubs' init_globs) comp_progs in
     let func_names =
             make_name_alist (MAP FST prog') prog (num_stubs
               (clos_to_bvl_config_max_app c1))
               (clos_to_bvl_config_next_loc
               c0) (LENGTH es0) in
     let ps = APPEND ps [((implode
       "after clos_to_bvl"),backend_passes_Bvl prog' func_names)] in
     let c2 = clos_to_bvl_config_start_fupd (K (num_stubs
       (clos_to_bvl_config_max_app c1) - 1)) c1 in
     let p = code_sort prog' in
     let c = backend_config_clos_conf_fupd (K c2) c in
       ((ps:(mlstring#'a any_prog) list),c,p,func_names))`;;

let to_bvl_thm = prove
 (`SND (to_bvl_all c p) = to_bvl c p`,
  CHEAT_TAC);;

let to_bvi_all_def = new_definition
  `to_bvi_all (c:backend_config) p =
     (let (ps,c,p,names) = to_bvl_all c p in
     let start' = clos_to_bvl_config_start (backend_config_clos_conf
       c) in
     let c0 = backend_config_bvl_conf c in
     let limit' = bvl_to_bvi_config_inline_size_limit c0 in
     let split_seq = bvl_to_bvi_config_split_main_at_seq c0 in
     let cut_size = bvl_to_bvi_config_exp_cut c0 in
     let (inlines,prog1) = tick_compile_prog limit' LN p in
     let prog = MAP (\(name,arity,exp). (name,arity,HD (remove_ticks
       [exp]))) prog1 in
     let ps = APPEND ps [((implode
       "after bvl_inline and remove_ticks"),backend_passes_Bvl prog
       names)] in
     let prog = MAP (\(name,arity,exp). (name,arity,let_op_sing exp))
       prog in
     let ps = APPEND ps [((implode
       "after let_op_sing"),backend_passes_Bvl prog names)] in
     let prog = MAP (\(name,arity,exp). (name,arity,
                        compile_any split_seq cut_size arity exp))
                          prog in
     let ps = APPEND ps [((implode
       "after bvl_handle"),backend_passes_Bvl prog names)] in
     let (loc,code,n1) = bvl_to_bvi_compile_prog start' 0 prog in
     let (n2,code2) = bvi_tailrec_compile_prog
       (bvl_to_bvi_config_do_tailrec c0) (bvl_num_stubs + 2) code in
     let (n3,code3) = bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
       c0) (bvl_num_stubs + 3) code2 in
     let (bvi_inlines,code') = bvi_inline_compile_prog code3 in
     let (s,p,l,bl,n1,n2,n3,names) =
       (loc,code',inlines,bvi_inlines,n1,n2,n3,get_names (MAP FST
         code') names) in
     let names = sptree_union (fromAList (APPEND (APPEND (APPEND
       (data_to_word_stub_names one)
       (word_to_stack_stub_names one)) (stack_alloc_stub_names one))
       (stack_remove_stub_names one))) names in
     let ps = APPEND ps [((implode
       "after bvl_to_bvi"),backend_passes_Bvi code names)] in
     let ps = APPEND ps [((implode
       "after bvi_tailrec"),backend_passes_Bvi code2 names)] in
     let ps = APPEND ps [((implode
       "after bvi_tmc"),backend_passes_Bvi code3 names)] in
     let ps = APPEND ps [((implode
       "after bvi_inline"),backend_passes_Bvi code' names)] in
     let c = backend_config_clos_conf_fupd (\c.
       clos_to_bvl_config_start_fupd (K s) c) c in
     let c = backend_config_bvl_conf_fupd
       (\c. bvl_to_bvi_config_next_name3_fupd (K n3)
         (bvl_to_bvi_config_next_name2_fupd (K n2)
         (bvl_to_bvi_config_next_name1_fupd (K n1)
         (bvl_to_bvi_config_bvi_inlines_fupd (K bl)
         (bvl_to_bvi_config_inlines_fupd (K l) c))))) c in
      ((ps:(mlstring#'a any_prog) list),c,p,names))`;;

let to_bvi_thm = prove
 (`SND (to_bvi_all c p) = to_bvi c p`,
  CHEAT_TAC);;

let to_data_all_def = new_definition
  `to_data_all (c:backend_config) p =
     (let (ps,c,p,names) = to_bvi_all c p in
     let p = MAP (\(a,n,e). (a,n,FST (compile n (COUNT_LIST n) T []
       [e]))) p in
     let ps = APPEND ps [((implode
       "after bvi_to_data"),backend_passes_Data p names)] in
     let p = MAP (\(a,n,e). (a,n,FST (data_live_compile e LN))) p in
     let ps = APPEND ps [((implode
       "after data_live"),backend_passes_Data p names)] in
     let p = MAP (\(a,n,e). (a,n,simp e Skip)) p in
     let ps = APPEND ps [((implode
       "after data_simp"),backend_passes_Data p names)] in
     let p = MAP (\(a,n,e). (a,n,data_space_compile e)) p in
     let ps = APPEND ps [((implode
       "after data_space"),backend_passes_Data p names)] in
       ((ps:(mlstring#'a any_prog) list),c,p,names))`;;

let to_data_thm = prove
 (`SND (to_data_all (c:backend_config) p) = to_data c p`,
  CHEAT_TAC);;

(* NOTE: this definition is meant to minimize code duplication
  in the explorer pretty printing. *)
let word_internal_all_def = new_definition
  `word_internal_all asm_conf ps names p =
     (let two_reg_arith = asm_config_two_reg_arith asm_conf in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,word_simp_compile_exp prog)))
                     p in
     let ps = APPEND ps [((implode "after word_simp"),Word p names)]
       in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,
                      inst_select asm_conf (max_var prog + 1) prog)))
                        p in
     let ps = APPEND ps [((implode "after word_inst"),Word p names)]
       in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,full_ssa_cc_trans arg_count
                     prog))) p in
     let ps = APPEND ps [((implode "after word_ssa"),Word p names)]
       in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,remove_dead_prog prog))) p in
     let ps = APPEND ps [((implode
       "after remove_dead in word_ssa"),Word p names)] in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,word_common_subexp_elim
                     prog))) p in
     let ps = APPEND ps [((implode "after word_cse"),Word p names)]
       in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,copy_prop prog))) p in
     let ps = APPEND ps [((implode "after word_copy"),Word p names)]
       in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,
                    three_to_two_reg_prog two_reg_arith prog))) p in
     let ps = APPEND ps [((implode
       "after three_to_two_reg from word_inst"),Word p names)] in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,remove_unreach prog))) p in
     let ps = APPEND ps [((implode "after word_unreach"),Word p
       names)] in
     let p = MAP (\((name_num,arg_count,prog)).
                   ((name_num,arg_count,remove_dead_prog prog))) p in
     let ps = APPEND ps [((implode
       "after remove_dead in word_alloc"),Word p names)] in
     (p,ps))`;;

let to_word_all_def = new_definition
  `to_word_all asm_conf (c:backend_config) p =
     (let (ps,c,p,names) = to_data_all c p in
     let word_conf = backend_config_word_to_word_conf c in
     let data_conf = backend_config_data_conf c in
     let data_conf = data_to_word_config_has_fp_tern_fupd (K
                 (asm_config_ISA asm_conf = ARMv7 /\ 2 <
                   asm_config_fp_reg_count asm_conf))
                   (data_to_word_config_has_fp_ops_fupd (K (1 <
                   asm_config_fp_reg_count asm_conf))
             data_conf) in
     let p = APPEND (stubs (:'a) data_conf) (MAP (compile_part
       data_conf) p) in
     let ps = APPEND ps [((implode "after data_to_word"),Word p
       names)] in
     let (p,ps) = word_internal_all asm_conf ps names p in
     let reg_count = asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf)) in
     let alg = word_to_word_config_reg_alg word_conf in
     let (n_oracles,col) = next_n_oracle (LENGTH p)
       (word_to_word_config_col_oracle word_conf) in
     let p = MAP (\((name_num,arg_count,prog),col_opt).
                   ((name_num,arg_count,
                    remove_must_terminate
                      (word_alloc name_num asm_conf alg reg_count
                        prog col_opt)))) (ZIP p n_oracles) in
     let ps = APPEND ps [((implode
       "after word_alloc (and remove_must_terminate)"),Word p names)] in
     let c = backend_config_word_to_word_conf_fupd (\c.
       word_to_word_config_col_oracle_fupd (K col) c) c in
       ((ps:(mlstring#'a any_prog) list),c,p,names))`;;

let LENGTH_next_n_oracle = prove
 (`next_n_oracle n col = (a,b) ==> LENGTH a = n`,
  CHEAT_TAC);;

(* [local] *)
let ZIP_MAP_1 = prove
 (`!l1 l2 f1 f2.
     LENGTH l1 = LENGTH l2 ==>
     ZIP (MAP f1 l1) l2 = MAP (\p. (f1 (FST p),SND p)) (ZIP l1 l2)`,
  CHEAT_TAC);;

(* to_word_thm *)
let backend_passes_to_word_thm = prove
 (`SND (to_word_all asm_conf (c:backend_config) p) = to_word asm_conf
  c p`,
  CHEAT_TAC);;

let to_stack_all_def = new_definition
  `to_stack_all asm_conf (c:backend_config) p =
     (let (ps,c,p,names) = to_word_all asm_conf c p in
     let (bm,c',fs,p) = word_to_stack_compile asm_conf
       (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p
       in
     let ps = APPEND ps [((implode
       "after word_to_stack"),backend_passes_Stack p names)] in
     let c = backend_config_word_conf_fupd (K c') c in
       ((ps:(mlstring#'a any_prog) list),bm,c,p,names))`;;

let to_stack_thm = prove
 (`SND (to_stack_all asm_conf (c:backend_config) p) = to_stack
  asm_conf c p`,
  CHEAT_TAC);;

let to_lab_all_def = new_definition
  `to_lab_all asm_conf (c:backend_config) p =
     (let (ps,bm,c,p,names) = to_stack_all asm_conf c p in
     let stack_conf = backend_config_stack_conf c in
     let data_conf = backend_config_data_conf c in
     let max_heap = 2 * max_heap_limit (:'a)
       (backend_config_data_conf c) - 1 in
     let sp = asm_config_reg_count asm_conf - (LENGTH
       (asm_config_avoid_regs asm_conf) + 3) in
     let offset = asm_config_addr_offset asm_conf in
     let prog = stack_rawcall_compile p in
     let ps = APPEND ps [((implode
       "after stack_rawcall"),backend_passes_Stack prog names)] in
     let prog = stack_alloc_compile data_conf prog in
     let ps = APPEND ps [((implode
       "after stack_alloc"),backend_passes_Stack prog names)] in
     let prog = stack_remove_compile (stack_to_lab_config_jump
       stack_conf) offset (is_gen_gc (data_to_word_config_gc_kind
       data_conf))
                  max_heap sp InitGlobals_location prog in
     let ps = APPEND ps [((implode
       "after stack_remove"),backend_passes_Stack prog names)] in
     let prog = stack_names_compile (stack_to_lab_config_reg_names
       stack_conf) prog in
     let ps = APPEND ps [((implode
       "after stack_names"),backend_passes_Stack prog names)] in
     let p = MAP prog_to_section prog in
     let ps = APPEND ps [((implode "after stack_to_lab"),Lab p
       names)] in
       ((ps:(mlstring#'a any_prog) list),(bm:('a word)
         list),c,(p:('a sec) list),names))`;;

let to_lab_thm = prove
 (`SND (to_lab_all asm_conf (c:backend_config) p) = to_lab asm_conf c
  p`,
  CHEAT_TAC);;

let to_target_all_def = new_definition
  `to_target_all asm_conf (c:backend_config) p =
     (let (ps,bm,c,p,names) = to_lab_all asm_conf c p in
     let p = filter_skip p in
     let ps = APPEND ps [((implode "after filter_skip"),Lab p names)]
       in
     let p = compile_lab asm_conf (backend_config_lab_conf c) p in
       ((ps:(mlstring#'a any_prog) list),attach_bitmaps names c bm
         p))`;;

let to_target_thm = prove
 (`SND (to_target_all asm_conf c p) = to_target asm_conf c p`,
  CHEAT_TAC);;

let from_lab_all_def = new_definition
  `from_lab_all ps asm_conf (c:backend_config) names p (bm:('a word)
  list) =
     (let p = filter_skip p in
     let ps = APPEND ps [((implode "after filter_skip"),Lab p names)]
       in
     let p = compile_lab asm_conf (backend_config_lab_conf c) p in
       ((ps:(mlstring#'a any_prog) list),attach_bitmaps names c bm
         p))`;;

let from_lab_thm = prove
 (`SND (from_lab_all ps asm_conf c names p bm) = from_lab asm_conf c
  names p bm`,
  CHEAT_TAC);;

let from_stack_all_def = new_definition
  `from_stack_all ps (asm_conf:'a asm_config) (c:backend_config) names p
  bm =
     (let stack_conf = backend_config_stack_conf c in
     let data_conf = backend_config_data_conf c in
     let max_heap = 2 * max_heap_limit (:'a)
       (backend_config_data_conf c) - 1 in
     let sp = asm_config_reg_count asm_conf - (LENGTH
       (asm_config_avoid_regs asm_conf) + 3) in
     let offset = asm_config_addr_offset asm_conf in
     let prog = stack_rawcall_compile p in
     let ps = APPEND ps [((implode
       "after stack_rawcall"),backend_passes_Stack prog names)] in
     let prog = stack_alloc_compile data_conf prog in
     let ps = APPEND ps [((implode
       "after stack_alloc"),backend_passes_Stack prog names)] in
     let prog = stack_remove_compile (stack_to_lab_config_jump
       stack_conf) offset (is_gen_gc (data_to_word_config_gc_kind
       data_conf))
                  max_heap sp InitGlobals_location prog in
     let ps = APPEND ps [((implode
       "after stack_remove"),backend_passes_Stack prog names)] in
     let prog = stack_names_compile (stack_to_lab_config_reg_names
       stack_conf) prog in
     let ps = APPEND ps [((implode
       "after stack_names"),backend_passes_Stack prog names)] in
     let p = MAP prog_to_section prog in
     let ps = APPEND ps [((implode "after stack_to_lab"),Lab p
       names)] in
       from_lab_all ps asm_conf c names p bm)`;;

let from_stack_thm = prove
 (`SND (from_stack_all ps asm_conf c names p bm) = from_stack asm_conf
  c names p bm`,
  CHEAT_TAC);;

let from_word_all_def = new_definition
  `from_word_all ps asm_conf (c:backend_config) names p =
     (let (bm,c',fs,p) = word_to_stack_compile asm_conf
       (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p
       in
     let ps = APPEND ps [((implode
       "after word_to_stack"),backend_passes_Stack p names)] in
     let c = backend_config_word_conf_fupd (K c') c in
       from_stack_all ps asm_conf c names p bm)`;;

let from_word_thm = prove
 (`SND (from_word_all ps asm_conf c names p) = from_word asm_conf c
  names p`,
  CHEAT_TAC);;

let from_word_0_all_def = new_definition
  `from_word_0_all ps asm_conf (c:backend_config) names p =
     (let word_conf = backend_config_word_to_word_conf c in
     let (p,ps) = word_internal_all asm_conf ps names p in
     let reg_count = asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf)) in
     let alg = word_to_word_config_reg_alg word_conf in
     let (n_oracles,col) = next_n_oracle (LENGTH p)
       (word_to_word_config_col_oracle word_conf) in
     let p = MAP (\((name_num,arg_count,prog),col_opt).
                   ((name_num,arg_count,
                    remove_must_terminate
                      (word_alloc name_num asm_conf alg reg_count
                        prog col_opt)))) (ZIP p n_oracles) in
     let ps = APPEND ps [((implode
       "after word_alloc (and remove_must_terminate)"),Word p names)] in
     let c = backend_config_word_to_word_conf_fupd (\c.
       word_to_word_config_col_oracle_fupd (K col) c) c in
       from_word_all ps asm_conf c names p)`;;

let from_word_0_thm = prove
 (`SND (from_word_0_all ps asm_conf c names p) = from_word_0 asm_conf
  c names p`,
  CHEAT_TAC);;

let from_data_all_def = new_definition
  `from_data_all ps asm_conf c names p =
     (let data_conf = backend_config_data_conf c in
     let word_conf = backend_config_word_to_word_conf c in
     let data_conf = data_to_word_config_has_fp_tern_fupd (K
                 (asm_config_ISA asm_conf = ARMv7 /\ 2 <
                   asm_config_fp_reg_count asm_conf))
                   (data_to_word_config_has_fp_ops_fupd (K (1 <
                   asm_config_fp_reg_count asm_conf))
             data_conf) in
     let p = APPEND (stubs (:'a) data_conf) (MAP (compile_part
       data_conf) p) in
     let ps = APPEND ps [((implode "after data_to_word"),Word p
       names)] in
       from_word_0_all ps asm_conf c names p)`;;

(* from_data_thm *)
let backend_passes_from_data_thm = prove
 (`SND (from_data_all ps asm_conf c names p) = from_data asm_conf c
  names p`,
  CHEAT_TAC);;

let to_data_all_from_data_all_correctness = prove
 (`to_target_all asm_conf c p =
     (let (ps,c',p,ns) = to_data_all c p in
       from_data_all ps asm_conf c' ns p)`,
  CHEAT_TAC);;

let compile_eq_to_target_all = prove
 (`compile asm_conf c p = SND (to_target_all asm_conf c p)`,
  CHEAT_TAC);;

let number_of_passes = prove
 (`LENGTH (FST (to_target_all asm_conf c p)) = 41`,
  CHEAT_TAC);;

let any_prog_pp_def = new_definition
  `any_prog_pp p = (match p with backend_passes_Source p ->
  source_to_strs p | backend_passes_Flat p -> flat_to_strs p | Clos
  decs funs -> clos_to_strs (decs,funs) | backend_passes_Bvl p names
  -> bvl_to_strs names p | backend_passes_Bvi p names -> bvi_to_strs
  names p | backend_passes_Data p names -> data_to_strs names p |
  Word p names -> word_to_strs names p | backend_passes_Stack p names
  -> stack_to_strs names p | Lab p names -> lab_to_strs names p)`;;

let pp_with_title_def = new_definition
  `pp_with_title pp (title,p) acc =
     Append (List [(implode "# "); title; (implode "\n\n")])
     (Append (pp p) acc)`;;

let compile_tap_def = new_definition
  `compile_tap asm_conf (c:backend_config) p =
     (if tap_config_explore_flag (backend_config_tap_conf c) then
       let (ps,out) = to_target_all asm_conf c p in
         (out,ITLIST (pp_with_title any_prog_pp) ps misc_Nil) else
           (compile asm_conf c p,misc_Nil))`;;

(* compile_alt *)
let backend_passes_compile_alt = prove
 (`compile asm_conf c p = FST (compile_tap asm_conf c p)`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
