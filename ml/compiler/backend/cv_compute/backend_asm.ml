(* ======================================================== *)
(*  backend_asm: ported from HOL4's
    compiler/backend/cv_compute/backend_asmScript.sml
    A definition theory, with 20 definitions and 13 theorems.
    Needed by to_data_cv.ml.  *)
(* ======================================================== *)

(*
  cv-compute-specific versions of lab_to_target and later passes
  where asm_conf is lifted out. Used for in-logic evaluation by cv_translator.
*)

needs "basis/RuntimeProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/labLang.ml";;
needs "compiler/backend/lab_filter.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/serialiser/backend_enc_dec.ml";;
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
needs "translator/evaluate_dec.ml";;
needs "translator/ml_prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "backend_asm"
  ["backend"; "backend_enc_dec"; "backend_passes"; "evaluate_dec";
   "lab_to_target"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["encode","clFFI_encode";
   "encode","fsFFI_encode";
   "encode","runtimeFFI_encode"];;


(*----------------------------------------------------------------*
    Adjustments to lab_to_target
 *----------------------------------------------------------------*)

let backend_asm_enc_line_def = define_cases
  `(backend_asm_enc_line (c:'a asm_config) skip_len (lab_Label n1 n2 n3) =
      lab_Label n1 n2 skip_len) /\
   (backend_asm_enc_line (c:'a asm_config) skip_len (lab_Asm a v0 v1) =
      (let bs = asm_config_encode c (cbw_to_asm a) in lab_Asm a bs
          (LENGTH bs))) /\
   (backend_asm_enc_line (c:'a asm_config) skip_len (lab_LabAsm l v2 v3 v4) =
      (let bs = asm_config_encode c (lab_inst (n2w 0) l) in lab_LabAsm
          l (n2w 0) bs (LENGTH bs)))`;;

let backend_asm_enc_sec_def = new_definition
  `backend_asm_enc_sec (c:'a asm_config) skip_len (Section k xs) =
     Section k (MAP (backend_asm_enc_line c skip_len) xs)`;;

let backend_asm_enc_sec_list_def = new_definition
  `backend_asm_enc_sec_list (c:'a asm_config) xs =
     let skip_len = LENGTH (asm_config_encode c (asm_Inst asm_Skip)) in
       MAP (backend_asm_enc_sec c skip_len) xs`;;

let backend_asm_enc_lines_again_def,backend_asm_enc_lines_again_ind =
  define_guess
  `(backend_asm_enc_lines_again labs ffis pos c [] (acc,ok) = (REVERSE
    acc,pos,(ok:bool))) /\
   (backend_asm_enc_lines_again labs ffis pos c (CONS (lab_Label k1 k2 l) xs)
    (acc,ok) =
         backend_asm_enc_lines_again labs ffis (pos + l) c xs (CONS
             (lab_Label k1 k2 l) acc,ok)) /\
   (backend_asm_enc_lines_again labs ffis pos c (CONS (lab_Asm x1 x2 l) xs)
    (acc,ok) =
         backend_asm_enc_lines_again labs ffis (pos + l) c xs (CONS
             (lab_Asm x1 x2 l) acc,ok)) /\
   (backend_asm_enc_lines_again labs ffis pos c (CONS (lab_LabAsm a w bytes l)
    xs) (acc,ok) =
         let w1 = get_jump_offset a ffis labs pos in
           if w = w1 then
             backend_asm_enc_lines_again labs ffis (pos + l) c xs (CONS
                 (lab_LabAsm a w bytes l) acc,ok)
           else let bs = asm_config_encode c (lab_inst w1 a) in
             let l1 = MAX (LENGTH bs) l in
               backend_asm_enc_lines_again labs ffis (pos + l1) c xs
                              (CONS (lab_LabAsm a w1 bs l1) acc,(ok
                                  /\ (l1 = l))))`;;

let backend_asm_enc_secs_again_def,backend_asm_enc_secs_again_ind =
  define_guess
  `(backend_asm_enc_secs_again pos labs ffis (c:'a asm_config) [] = ([],T)) /\
   (backend_asm_enc_secs_again pos labs ffis (c:'a asm_config) (CONS (Section s
    lines) rest) =
      let (lines1,pos1,ok) = backend_asm_enc_lines_again labs ffis pos c
          lines ([],T) in let
          (rest1,ok1) = backend_asm_enc_secs_again pos1 labs ffis c
              rest in (CONS (Section s lines1) rest1,(ok /\ ok1)))`;;

(* [local] *)
let enc_line_eq = prove
 (`lab_to_target_enc_line (asm_config_encode c) skip_len l =
  backend_asm_enc_line c skip_len l`,
  CHEAT_TAC);;

(* [local] *)
let enc_sec_eq = prove
 (`lab_to_target_enc_sec (asm_config_encode c) skip_len l =
  backend_asm_enc_sec c skip_len l`,
  CHEAT_TAC);;

(* [local] *)
let enc_sec_list_eq = prove
 (`lab_to_target_enc_sec_list (asm_config_encode c) l =
  backend_asm_enc_sec_list c l`,
  CHEAT_TAC);;

(* [local] *)
let enc_lines_again_eq = prove
 (`!xs pos acc ok.
     lab_to_target_enc_lines_again labs ffis pos (asm_config_encode c) xs
       (acc,ok) =
     backend_asm_enc_lines_again labs ffis pos c xs (acc,ok)`,
  CHEAT_TAC);;

(* [local] *)
let enc_secs_again_eq = prove
 (`!xs pos labs ffis.
     lab_to_target_enc_secs_again pos labs ffis (asm_config_encode c) xs =
     backend_asm_enc_secs_again pos labs ffis c xs`,
  CHEAT_TAC);;

let backend_asm_remove_labels_def =
  REWRITE_RULE [enc_sec_list_eq] remove_labels_def;;

let backend_asm_remove_labels_loop_def =
  REWRITE_RULE [enc_secs_again_eq] remove_labels_loop_def;;

let backend_asm_compile_lab_def = new_definition
  `backend_asm_compile_lab asm_conf c sec_list =
     (let current_ffis = find_ffi_names sec_list in
     let (ffis,ffis_ok) =
         (match lab_to_target_config_ffi_names c with SOME ffis ->
           (ffis,list_subset current_ffis ffis)
          | _ -> (current_ffis,T)) in
     if ffis_ok then
       match remove_labels (lab_to_target_config_init_clock c) asm_conf
         (lab_to_target_config_pos c) (lab_to_target_config_labels c) ffis
         sec_list with SOME (sec_list,l1) ->
           let bytes = prog_to_bytes sec_list in
           let (new_ffis,shmem_infos) = get_shmem_info sec_list
             (lab_to_target_config_pos c) [] [] in
           SOME (bytes,lab_to_target_config_shmem_extra_fupd (K shmem_infos)
             (lab_to_target_config_ffi_names_fupd (K (SOME (APPEND ffis
             new_ffis))) (lab_to_target_config_sec_pos_len_fupd (K (get_symbols
             (lab_to_target_config_pos c) sec_list))
             (lab_to_target_config_pos_fupd (K (LENGTH bytes +
             lab_to_target_config_pos c)) (lab_to_target_config_labels_fupd (K
             l1)
                 c)))))
       | NONE -> NONE
     else NONE)`;;

let lab_to_target_def = new_definition
  `lab_to_target asm_conf c sec_list = backend_asm_compile_lab asm_conf c
  (filter_skip sec_list)`;;

let backend_asm_attach_bitmaps_def = define_cases
  `(backend_asm_attach_bitmaps names (c:backend_config) data (SOME
    (code_bytes,c')) =
      (let ffi_names' = ffinames_to_string_list (the []
          (lab_to_target_config_ffi_names c')) in
       let syms = MAP (\(n,p,l). (lookup_any n names (implode
           "NOTFOUND"),p,l)) (lab_to_target_config_sec_pos_len
                      c') in
         SOME (code_bytes,LENGTH code_bytes,
               data,LENGTH data,
               ffi_names',LENGTH (lab_to_target_config_shmem_extra c'),
               syms,encode_backend_config (backend_config_symbols_fupd
                   (K syms) (backend_config_lab_conf_fupd (K c') c))))) /\
   (backend_asm_attach_bitmaps names (c:backend_config) bm NONE = NONE)`;;

let backend_asm_from_lab_def = new_definition
  `backend_asm_from_lab (asm_conf:'a asm_config) (c:backend_config) names p bm
  =
     backend_asm_attach_bitmaps names c bm (lab_to_target asm_conf
       (backend_config_lab_conf c) p)`;;

(*----------------------------------------------------------------*
    Remaining middle passes
 *----------------------------------------------------------------*)

let backend_asm_from_stack_def = new_definition
  `backend_asm_from_stack (asm_conf:'a asm_config) (c:backend_config) names p
  bm =
     let p = stack_to_lab_compile (backend_config_stack_conf
       c) (backend_config_data_conf c) (2 * max_heap_limit (:'a)
         (backend_config_data_conf c) - 1)
       (asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs
         asm_conf) + 3))
       (asm_config_addr_offset asm_conf) p in
     backend_asm_from_lab asm_conf c names p bm`;;

let backend_asm_from_word_def = new_definition
  `backend_asm_from_word (asm_conf:'a asm_config) (c:backend_config) names p =
     let (bm,c',fs,p) = word_to_stack_compile asm_conf
       (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
     let c = backend_config_word_conf_fupd (K c') c in
       backend_asm_from_stack asm_conf c names p bm`;;

let word_alloc_inlogic_def = new_definition
  `word_alloc_inlogic c prog col_opt =
     let tree = get_clash_tree prog [] in
     let forced = get_forced c prog [] in
       oracle_colour_ok (asm_config_reg_count c - (5 + LENGTH
         (asm_config_avoid_regs c)))
                        col_opt tree prog forced`;;

let each_inlogic_def,each_inlogic_ind = define_guess
  `(each_inlogic asm_conf [] = SOME []) /\
   (each_inlogic asm_conf (CONS ((name_num,arg_count,prog),col_opt) rest) =
     let prog = word_simp_compile_exp prog in let
         maxv = max_var prog + 1 in let
         inst_prog = inst_select asm_conf maxv prog in let
         ssa_prog = full_ssa_cc_trans arg_count inst_prog in let
         rm_ssa_prog = remove_dead_prog ssa_prog in let
         cse_prog = word_common_subexp_elim rm_ssa_prog in let
         cp_prog = copy_prop cse_prog in let
         two_prog = three_to_two_reg_prog (asm_config_two_reg_arith
             asm_conf) cp_prog in let
         unreach_prog = remove_unreach two_prog in let
         rm_prog = remove_dead_prog unreach_prog in
       match word_alloc_inlogic asm_conf rm_prog col_opt with NONE -> NONE
        | SOME reg_prog ->
          (match each_inlogic asm_conf rest with
            NONE -> NONE
          | SOME progs -> SOME (CONS
              (name_num,arg_count,remove_must_terminate reg_prog) progs)))`;;

let word_to_word_inlogic_def = new_definition
  `word_to_word_inlogic asm_conf word_conf progs =
     (let (n_oracles,col) = next_n_oracle (LENGTH progs)
       (word_to_word_config_col_oracle word_conf) in
     let progs = ZIP progs n_oracles in
       match each_inlogic asm_conf progs with NONE -> NONE
       | SOME res -> SOME (col,res))`;;

let backend_asm_from_word_0_def = new_definition
  `backend_asm_from_word_0 (asm_conf:'a asm_config) (c,p,names) =
     match word_to_word_inlogic asm_conf (backend_config_word_to_word_conf
       c) p with NONE -> NONE
     | SOME (col,prog) ->
         let c = backend_config_word_to_word_conf_fupd
                   (\c. word_to_word_config_col_oracle_fupd (K col) c) c in
           backend_asm_from_word asm_conf c names prog`;;

(*----------------------------------------------------------------*
   End-to-end compiler
 *----------------------------------------------------------------*)

let compile_cake_def = new_definition
  `compile_cake (asm_conf:'a asm_config) (c:backend_config) p =
     if prog_syntax_ok p then
       backend_asm_from_word_0 asm_conf (to_word_0 asm_conf c p)
     else NONE`;;

(*----------------------------------------------------------------*
   Correspondence proofs
 *----------------------------------------------------------------*)

(* from_lab_thm[local] *)
let backend_asm_from_lab_thm = prove
 (`backend_asm_from_lab asm_conf c names p bm =
   SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ==>
   (?c1.
     backend_from_lab asm_conf c names p bm = SOME (bytes,bm1,c1) /\
     ffi_names = ffinames_to_string_list (the []
       (lab_to_target_config_ffi_names (backend_config_lab_conf c1))) /\
     syms = backend_config_symbols c1 /\
     LENGTH bytes = bytes_len /\
     LENGTH bm1 = bm1_len /\
     LENGTH (lab_to_target_config_shmem_extra (backend_config_lab_conf c1))
       = shmem_len /\
     conf_str = encode_backend_config c1)`,
  CHEAT_TAC);;

(* from_stack_thm[local] *)
let backend_asm_from_stack_thm = prove
 (`backend_asm_from_stack asm_conf c names p bm =
   SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ==>
   (?c1.
     backend_from_stack asm_conf c names p bm = SOME (bytes,bm1,c1) /\
     ffi_names = ffinames_to_string_list (the []
       (lab_to_target_config_ffi_names (backend_config_lab_conf c1))) /\
     syms = backend_config_symbols c1 /\
     LENGTH bytes = bytes_len /\
     LENGTH bm1 = bm1_len /\
     LENGTH (lab_to_target_config_shmem_extra (backend_config_lab_conf c1))
       = shmem_len /\
     conf_str = encode_backend_config c1)`,
  CHEAT_TAC);;

(* [local] *)
let word_to_word_inlogic_thm = prove
 (`word_to_word_inlogic asm_conf (backend_config_word_to_word_conf c) p = SOME
  (col,prog) ==>
   backend_compile (backend_config_word_to_word_conf c) asm_conf p =
     (col,prog)`,
  CHEAT_TAC);;

(* from_word_0_thm[local] *)
let backend_asm_from_word_0_thm = prove
 (`backend_asm_from_word_0 asm_conf (c,p,names) =
   SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ==>
   (?c1.
     backend_from_word_0 asm_conf c names p = SOME (bytes,bm1,c1) /\
     ffi_names = ffinames_to_string_list (the []
       (lab_to_target_config_ffi_names (backend_config_lab_conf c1))) /\
     syms = backend_config_symbols c1 /\
     LENGTH bytes = bytes_len /\
     LENGTH bm1 = bm1_len /\
     LENGTH (lab_to_target_config_shmem_extra (backend_config_lab_conf c1))
       = shmem_len /\
     conf_str = encode_backend_config c1)`,
  CHEAT_TAC);;

let compile_cake_thm = prove
 (`!(asm_conf:'a asm_config).
     compile_cake asm_conf c p =
     SOME (bytes,bytes_len,bm,bm_len,ffi_names,shmem_len,syms,conf_str) ==>
     (?c1.
       backend_compile asm_conf c p = SOME (bytes,bm,c1) /\
       ffi_names = ffinames_to_string_list (the []
         (lab_to_target_config_ffi_names (backend_config_lab_conf c1))) /\
       syms = backend_config_symbols c1 /\
       LENGTH bytes = bytes_len /\
       LENGTH bm = bm_len /\
       LENGTH (lab_to_target_config_shmem_extra (backend_config_lab_conf
         c1)) = shmem_len /\
       prog_syntax_ok p /\
       conf_str = encode_backend_config c1)`,
  CHEAT_TAC);;

(*----------------------------------------------------------------*
   Explorer for in-logic evaluation of it
 *----------------------------------------------------------------*)

let backend_asm_to_word_all_def = new_definition
  `backend_asm_to_word_all asm_conf (c:backend_config) p =
     (let (ps,c,p,names) = to_data_all c p in
     let data_conf = backend_config_data_conf c in
     let word_conf = backend_config_word_to_word_conf c in
     let data_conf = data_to_word_config_has_fp_tern_fupd (K
                 (asm_config_ISA asm_conf = ARMv7 /\ 2 <
                   asm_config_fp_reg_count asm_conf))
                   (data_to_word_config_has_fp_ops_fupd (K (1 <
                   asm_config_fp_reg_count asm_conf))
             data_conf) in
     let p = APPEND (data_to_word_stubs (:'a) data_conf) (MAP
       (bvi_to_data_compile_part data_conf) p) in
     let ps = APPEND ps [((implode "after data_to_word"),backend_passes_Word
       p names)] in
     let (p,ps) = word_internal_all asm_conf ps names p in
     let reg_count = asm_config_reg_count asm_conf - (5 + LENGTH
       (asm_config_avoid_regs asm_conf)) in
     let alg = word_to_word_config_reg_alg word_conf in
     let (n_oracles,col) = next_n_oracle (LENGTH p)
       (word_to_word_config_col_oracle word_conf) in
     let p = MAP (\((name_num,arg_count,prog),col_opt).
               ((name_num,arg_count,
                remove_must_terminate
                  (match word_alloc_inlogic asm_conf prog col_opt with NONE
                    -> word_FFI (implode "reg alloc fail") 0 0 0 0 (LN,LN)
                   | SOME x -> x)))) (ZIP p n_oracles) in
     let ps = APPEND ps [((implode
       "after word_alloc (and remove_must_terminate)"),backend_passes_Word p
       names)] in
     let c = backend_config_word_to_word_conf_fupd (\c.
       word_to_word_config_col_oracle_fupd (K col) c) c in
       ((ps:(mlstring#'a any_prog) list),c,p,names))`;;

let backend_asm_to_stack_all_def = new_definition
  `backend_asm_to_stack_all asm_conf (c:backend_config) p =
     let (ps,c,p,names) = backend_asm_to_word_all asm_conf c p in
     let (bm,c',fs,p) = word_to_stack_compile asm_conf
       (stack_to_lab_config_perf_calls (backend_config_stack_conf c)) p in
     let ps = APPEND ps [((implode
       "after word_to_stack"),backend_passes_Stack p names)] in
     let c = backend_config_word_conf_fupd (K c') c in
       ((ps:(mlstring#'a any_prog) list),bm,c,p,names)`;;

let backend_asm_to_lab_all_def = new_definition
  `backend_asm_to_lab_all (asm_conf:'a asm_config) (c:backend_config) p =
     (let (ps,bm,c,p,names) = backend_asm_to_stack_all asm_conf c p in
     let stack_conf = backend_config_stack_conf c in
     let data_conf = backend_config_data_conf c in
     let max_heap = 2 * max_heap_limit (:'a) (backend_config_data_conf c) -
       1 in
     let sp = asm_config_reg_count asm_conf - (LENGTH (asm_config_avoid_regs
       asm_conf) + 3) in
     let offset = asm_config_addr_offset asm_conf in
     let prog = stack_rawcall_compile p in
     let ps = APPEND ps [((implode
       "after stack_rawcall"),backend_passes_Stack prog names)] in
     let prog = stack_alloc_compile data_conf prog in
     let ps = APPEND ps [((implode "after stack_alloc"),backend_passes_Stack
       prog names)] in
     let prog = stack_remove_compile (stack_to_lab_config_jump stack_conf)
       offset (is_gen_gc (data_to_word_config_gc_kind data_conf))
                  max_heap sp InitGlobals_location prog in
     let ps = APPEND ps [((implode
       "after stack_remove"),backend_passes_Stack prog names)] in
     let prog = stack_names_compile (stack_to_lab_config_reg_names
       stack_conf) prog in
     let ps = APPEND ps [((implode "after stack_names"),backend_passes_Stack
       prog names)] in
     let p = MAP prog_to_section prog in
     let ps = APPEND ps [((implode "after stack_to_lab"),backend_passes_Lab
       p names)] in
       ((ps:(mlstring#'a any_prog) list),(bm:('a word) list),c,p,names))`;;

let compile_cake_explore_def = new_definition
  `compile_cake_explore (asm_conf:'a asm_config) (c:backend_config) p =
     let (ps,bm,c,p,names) = backend_asm_to_lab_all asm_conf c p in
     let p = filter_skip p in
     let ps = APPEND ps [((implode "after filter_skip"),backend_passes_Lab p
       names)] in
       mlvector_concat (append (ITLIST (pp_with_title any_prog_pp) ps
         misc_Nil))`;;

(*----------------------------------------------------------------*
   Misc
 *----------------------------------------------------------------*)

let exists_oracle = prove
 (`P x ==> (?oracle'. P oracle')`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
