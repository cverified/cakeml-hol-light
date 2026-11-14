(* ======================================================== *)
(*  word_to_word: ported from HOL4's
    compiler/backend/word_to_wordScript.sml
    A definition theory, with 5 definitions, 1 datatype and 2
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  This compiler phase composes the phases internal to wordLang:
      1) word_simp ; 2) inst_select ; 3) SSA ; 4) remove_dead
      5) word_cse ; 6) copy_prop ; 7) three-to-two reg
      8) remove_unreach ; 9) remove_dead ; 10) word_alloc
*)

needs "basis/pure/mlstring.ml";;
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_to_word"
  ["asm"; "mlstring"; "wordLang"; "word_alloc"; "word_copy";
   "word_cse"; "word_inst"; "word_remove"; "word_simp";
   "word_unreach"];;

(*reg_alg = choice of register allocator*)
let word_to_word_config_FIELDS = define_record "word_to_word_config"
  ["reg_alg","num";
   "col_oracle","((num spt) option) list"];;

let word_to_word_compile_single_def = new_definition
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

let full_compile_single_def = new_definition
  `full_compile_single two_reg_arith reg_count alg c p =
   (let (name_num,arg_count,reg_prog) = word_to_word_compile_single
     two_reg_arith reg_count alg c p in
     (name_num,arg_count,remove_must_terminate reg_prog))`;;

let next_n_oracle_def = new_definition
  `next_n_oracle n (col:((num spt) option) list) =
   (if n <= LENGTH col then
     (TAKE n col,DROP n col) else
     (REPLICATE n NONE,[]))`;;

let word_to_word_compile_def = new_definition
  `word_to_word_compile word_conf (asm_conf:'a asm_config) progs =
     (let (two_reg_arith,reg_count) = (asm_config_two_reg_arith
       asm_conf,asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf))) in
     let (n_oracles,col) = next_n_oracle (LENGTH progs)
       (word_to_word_config_col_oracle word_conf) in
     let progs = ZIP progs n_oracles in
     (col,MAP (full_compile_single two_reg_arith reg_count
       (word_to_word_config_reg_alg word_conf) asm_conf) progs))`;;

let full_compile_single_for_eval_def = new_definition
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

let full_compile_single_for_eval_eq = prove
 (`full_compile_single two_reg_arith reg_count alg c p =
   full_compile_single_for_eval two_reg_arith reg_count alg c p`,
  CHEAT_TAC);;

(* used for bootstrap translation *)
let compile_alt = prove
 (`word_to_word_compile word_conf (asm_conf:'a asm_config) progs =
   (let (two_reg_arith,reg_count) = (asm_config_two_reg_arith
     asm_conf,asm_config_reg_count asm_conf - (5 + LENGTH
     (asm_config_avoid_regs asm_conf))) in
   let (n_oracles,col) = next_n_oracle (LENGTH progs)
     (word_to_word_config_col_oracle word_conf) in
   let alg = word_to_word_config_reg_alg word_conf in
   let names = MAP (\(x,y,z). x) progs in
   let args = MAP (\(x,y,z). y) progs in
   let ps = MAP (\(x,y,z). z) progs in
   let simp_ps = MAP word_simp_compile_exp ps in
   let _12 = empty_ffi (implode "finished: word_simp") in
   let inst_ps = MAP (\p. inst_select asm_conf (max_var p + 1) p)
     simp_ps in
   let _13 = empty_ffi (implode "finished: word_inst") in
   let ssa_ps = MAP2 (\a p. full_ssa_cc_trans a p) args inst_ps in
   let _14 = empty_ffi (implode "finished: word_ssa") in
   let rm_ssa_ps = MAP remove_dead_prog ssa_ps in
   let _15 = empty_ffi (implode
     "finished: word_remove_dead after word_ssa") in
   let cse_ps = MAP word_common_subexp_elim rm_ssa_ps in
   let _16 = empty_ffi (implode "finished: word_cse") in
   let cp_ps = MAP copy_prop cse_ps in
   let _17 = empty_ffi (implode "finished: word_copy") in
   let two_ps = MAP (three_to_two_reg_prog two_reg_arith) cp_ps in
   let _18 = empty_ffi (implode "finished: word_two_reg") in
   let unreach_ps = MAP remove_unreach two_ps in
   let _19 = empty_ffi (implode "finished: word_unreach") in
   let dead_ps = MAP remove_dead_prog unreach_ps in
   let _20 = empty_ffi (implode "finished: word_remove_dead") in
   let reg_ps = MAP2 (\c (n,p). word_alloc n asm_conf alg reg_count p
     c) n_oracles (ZIP names dead_ps) in
   let _21 = empty_ffi (implode "finished: word_alloc") in
   let rmt_ps = MAP remove_must_terminate reg_ps in
   let _22 = empty_ffi (implode "finished: word_remove") in
   (col,ZIP names (ZIP args rmt_ps)))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
