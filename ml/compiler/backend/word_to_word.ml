(* ======================================================== *)
(*  word_to_word: ported from HOL4's
    compiler/backend/word_to_wordScript.sml  *)
(* ======================================================== *)

(*
  This compiler phase composes the phases internal to wordLang:
      1) word_simp ; 2) inst_select ; 3) SSA ; 4) remove_dead
      5) word_cse ; 6) copy_prop ; 7) three-to-two reg
      8) remove_unreach ; 9) remove_dead ; 10) word_alloc
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/backend/word_copy.ml";;
needs "compiler/backend/word_cse.ml";;
needs "compiler/backend/word_inst.ml";;
needs "compiler/backend/word_remove.ml";;
needs "compiler/backend/word_simp.ml";;
needs "compiler/backend/word_unreach.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;

(*reg_alg = choice of register allocator*)
let word_to_word_config_FIELDS = define_record "word_to_word_config"
  ["reg_alg","num";
   "col_oracle","((num spt) option) list"];;

let compile_single_def = cake_define
  `word_to_word_compile_single two_reg_arith reg_count alg c
  (((name_num:num),arg_count,prog),col_opt) =
   (let prog = word_simp_compile_exp prog in
   let maxv = max_var prog + 1 in
   let inst_prog = inst_select c maxv prog in
   let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
   let rm_ssa_prog = remove_dead_prog ssa_prog in
   let cse_prog = word_common_subexp_elim rm_ssa_prog in
   let cp_prog = copy_prop cse_prog in
   let two_prog = three_to_two_reg_prog two_reg_arith cp_prog in
   let unreach_prog = remove_unreach two_prog in
   let rm_prog = remove_dead_prog unreach_prog in
   let reg_prog = word_alloc name_num c alg reg_count rm_prog col_opt
     in
     (name_num,arg_count,reg_prog))`;;
hol4_overload "compile_single" "word_to_word_compile_single";;

let full_compile_single_def = cake_define
  `full_compile_single two_reg_arith reg_count alg c p =
   (let (name_num,arg_count,reg_prog) = compile_single two_reg_arith
     reg_count alg c p in
     (name_num,arg_count,remove_must_terminate reg_prog))`;;

let next_n_oracle_def = cake_define
  `next_n_oracle n (col:((num spt) option) list) =
   (if n <= LENGTH col then
     (TAKE n col,DROP n col) else
     (REPLICATE n NONE,[]))`;;

let compile_def = cake_define
  `word_to_word_compile word_conf (asm_conf:'a asm_config) progs =
     (let (two_reg_arith,reg_count) = (asm_config_two_reg_arith
       asm_conf,asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf))) in
     let (n_oracles,col) = next_n_oracle (LENGTH progs)
       (word_to_word_config_col_oracle word_conf) in
     let progs = ZIP (progs,n_oracles) in
     (col,MAP (full_compile_single two_reg_arith reg_count
       (word_to_word_config_reg_alg word_conf) asm_conf) progs))`;;
hol4_overload "compile" "word_to_word_compile";;

let full_compile_single_for_eval_def = cake_define
  `full_compile_single_for_eval two_reg_arith reg_count alg c p =
     (let ((name_num,arg_count,prog),col_opt) = p in
     let prog = word_simp_compile_exp prog in
     let _1 = empty_ffi (implode "finished: word_simp") in
     let maxv = max_var prog + 1 in
     let inst_prog = inst_select c maxv prog in
     let _2 = empty_ffi (implode "finished: word_inst") in
     let ssa_prog = full_ssa_cc_trans arg_count inst_prog in
     let _3 = empty_ffi (implode "finished: word_ssa") in
     let rm_ssa_prog = remove_dead_prog ssa_prog in
     let _4 = empty_ffi (implode
       "finished: word_remove_dead after word_ssa") in
     let cse_prog = word_common_subexp_elim rm_ssa_prog in
     let _5 = empty_ffi (implode "finished: word_cse") in
     let cp_prog = copy_prop cse_prog in
     let _6 = empty_ffi (implode "finished: word_copy") in
     let two_prog = three_to_two_reg_prog two_reg_arith cp_prog in
     let _7 = empty_ffi (implode "finished: word_two_reg") in
     let unreach_prog = remove_unreach two_prog in
     let _8 = empty_ffi (implode "finished: word_unreach") in
     let rm_prog = remove_dead_prog unreach_prog in
     let _9 = empty_ffi (implode "finished: word_remove_dead") in
     let reg_prog = word_alloc name_num c alg reg_count rm_prog
       col_opt in
     let _10 = empty_ffi (implode "finished: word_alloc") in
     let rmt_prog = remove_must_terminate reg_prog in
     let _11 = empty_ffi (implode "finished: word_remove") in
       (name_num,arg_count,rmt_prog))`;;

(* used for bootstrap translation *)
