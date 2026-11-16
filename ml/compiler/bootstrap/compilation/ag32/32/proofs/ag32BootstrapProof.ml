(* ======================================================== *)
(*  ag32BootstrapProof: ported from HOL4's
    compiler/bootstrap/compilation/ag32/32/proofs/
      ag32BootstrapProofScript.sml
    A proof theory about ag32Bootstrap.ml, with 1 definition and 20
    theorems.  No file of the port needs it.  *)
(* ======================================================== *)

(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)

needs "basis/CommandLineProof.ml";;
needs "basis/TextIOProof.ml";;
needs "basis/fsFFI.ml";;
needs "basis/fsFFIProps.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/ag32/ag32_config.ml";;
needs "compiler/backend/ag32/ag32_memory.ml";;
needs "compiler/backend/ag32/proofs/ag32_basis_ffiProof.ml";;
needs "compiler/backend/ag32/proofs/ag32_configProof.ml";;
needs "compiler/backend/ag32/proofs/ag32_ffi_codeProof.ml";;
needs "compiler/backend/ag32/proofs/ag32_machine_config.ml";;
needs "compiler/backend/ag32/proofs/ag32_memoryProof.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/proofs/backendProof.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/bootstrap/compilation/ag32/32/ag32Bootstrap.ml";;
needs "compiler/bootstrap/translation/compiler32Prog.ml";;
needs "compiler/compiler.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmProps.ml";;
needs "compiler/repl/repl_decs_allowed.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32BootstrapProof"
  ["ag32Bootstrap"; "ag32_basis_ffiProof"; "ag32_configProof";
   "ag32_ffi_codeProof"; "ag32_machine_config"; "ag32_memoryProof";
   "backendProof"; "compiler32Prog"; "repl_decs_allowed"; "semanticsProps"];;

(* [local] *)
let with_clos_conf_simp = prove
 (`(mc_init_ok ag32_config (backend_config_bvl_conf_fupd
                   (\c. bvl_to_bvi_config_exp_cut_fupd (K t2)
                     (bvl_to_bvi_config_inline_size_limit_fupd (K t1) c))
                     (backend_config_clos_conf_fupd (K z) ag32_backend_config))
                     =
    mc_init_ok ag32_config ag32_backend_config) /\
   (~(closSem_state_max_app x = 0) /\ (match clos_to_bvl_config_known_conf x
     with NONE -> T | SOME k -> clos_known_config_val_approx_spt k = LN) ==>
    (backend_config_ok ag32_config (backend_config_clos_conf_fupd (K x)
      ag32_backend_config) =
     backend_config_ok ag32_config ag32_backend_config))`,
  CHEAT_TAC);;

(* HOL4 ag32BootstrapProofScript.sml:24: the overload cake_config, which the
   port expands *)

let compiler_instance_def = new_definition
  `ag32BootstrapProof_compiler_instance =
     mk_source_evalProof_compiler_instance (compile_inc_progs_for_eval
       ag32_config) BACKEND_CONFIG_v UNIV (LIST_v AST_DEC_v) decs_allowed
       info`;;

(* [local] *)
let compiler_instance_lemma = prove
 (`INJ (source_evalProof_compiler_instance_config_v
  ag32BootstrapProof_compiler_instance) (UNIV:backend_config->bool)
  (UNIV:semanticPrimitives_v->bool)
  /\ source_evalProof_compiler_instance_init_state
   ag32BootstrapProof_compiler_instance = info
     /\ source_evalProof_compiler_instance_compiler_fun
   ag32BootstrapProof_compiler_instance =
     compile_inc_progs_for_eval ag32_config`,
  CHEAT_TAC);;

(* HOL4 ag32BootstrapProofScript.sml:45-53: a proof *)

(* HOL4 ag32BootstrapProofScript.sml:55-56: ML code, not ported *)

let extcalls_ffi_names = prove
 (`extcalls (lab_to_target_config_ffi_names (backend_config_lab_conf info)) =
  ffis`,
  CHEAT_TAC);;

(* HOL4 ag32BootstrapProofScript.sml:73-74: ML code, not ported *)

(* HOL4 ag32BootstrapProofScript.sml:76-78: the ML values that the
   definitions below antiquote *)

(* HOL4 ag32BootstrapProofScript.sml:80-81: the overload
   cake_machine_config, which the port expands *)

let target_state_rel_cake_start_asm_state = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   is_ag32_init_state (ag32_memory_init_memory code data (extcalls
     (lab_to_target_config_ffi_names (backend_config_lab_conf info))) (cl,inp))
     ms ==>
   (?n. target_state_rel ag32_target
          (init_asm_state code data (extcalls
            (lab_to_target_config_ffi_names (backend_config_lab_conf info)))
            (cl,inp))
          (ITER n Next ms) /\
       (ffi_state_io_events (ITER n Next ms) = ffi_state_io_events ms) /\
       (!x. ~(x IN (ag32_startup_addresses)) ==>
         (?_MEM (ITER n Next ms) x = ?_MEM ms x)))`,
  CHEAT_TAC);;

(* HOL4 ag32BootstrapProofScript.sml:109-112: ML code, not ported *)

(* HOL4 ag32BootstrapProofScript.sml:114-130: ML code, not ported *)

(* HOL4 ag32BootstrapProofScript.sml:132-135: a theorem that HOL4 states as
   the value of an ML expression: cake_compiled_thm *)

let cake_installed = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\
   LENGTH inp <= stdin_size /\
   is_ag32_init_state (ag32_memory_init_memory code data
                         (extcalls (lab_to_target_config_ffi_names
                           (backend_config_lab_conf info))) (cl,inp)) ms0 ==>
   installed code 0 data 0 (lab_to_target_config_ffi_names
     (backend_config_lab_conf info))
     (heap_regs (stack_to_lab_config_reg_names (backend_config_stack_conf
       ag32_backend_config)))
     ((ag32_machine_config (extcalls (lab_to_target_config_ffi_names
       (backend_config_lab_conf info))) (LENGTH code) (LENGTH data)))
       (lab_to_target_config_shmem_extra (backend_config_lab_conf info))
     (ITER (cake_startup_clock ms0 inp cl) Next ms0)`,
  CHEAT_TAC);;

(* HOL4 ag32BootstrapProofScript.sml:173-176: a theorem that HOL4 states as
   the value of an ML expression: cake_machine_sem *)

(* TODO: move *)

let get_stdin_stdin_fs = prove
 (`get_stdin (stdin_fs inp) = inp`,
  CHEAT_TAC);;
add_simp get_stdin_stdin_fs;;

let inFS_fname_fastForwardFD = prove
 (`inFS_fname (fastForwardFD fs fd) fnm <=> inFS_fname fs fnm`,
  CHEAT_TAC);;
add_simp inFS_fname_fastForwardFD;;

let not_inFS_fname_stdin_fs = prove
 (`!nm. ~(inFS_fname (stdin_fs inp) nm)`,
  CHEAT_TAC);;
add_simp not_inFS_fname_stdin_fs;;

let ALOOKUP_stdin_fs_File_NONE = prove
 (`ALOOKUP (IO_fs_inode_tbl (stdin_fs inp)) (File ino) = NONE`,
  CHEAT_TAC);;
add_simp ALOOKUP_stdin_fs_File_NONE;;

let ALOOKUP_fastForwardFD_infds_neq = prove
 (`~(fd = fd') ==> (ALOOKUP (IO_fs_infds (fastForwardFD fs fd)) fd' = ALOOKUP
  (IO_fs_infds fs) fd')`,
  CHEAT_TAC);;

let FST_ALOOKUP_fastForwardFD_infds = prove
 (`OPTION_MAP FST (ALOOKUP (IO_fs_infds (fastForwardFD fs fd)) fd') =
   OPTION_MAP FST (ALOOKUP (IO_fs_infds fs) fd')`,
  CHEAT_TAC);;

let FST_ALOOKUP_add_stdo_infds = prove
 (`OPTION_MAP FST (ALOOKUP (IO_fs_infds (add_stdo fd nm fs out)) fd') =
   OPTION_MAP FST (ALOOKUP (IO_fs_infds fs) fd')`,
  CHEAT_TAC);;

let ALOOKUP_add_stdout_inode_tbl = prove
 (`STD_streams fs ==> (
   ALOOKUP (IO_fs_inode_tbl ((add_stdo 1 "stdout") fs out)) fnm =
   (if fnm = UStream (implode "stdout") then
     SOME (APPEND (THE (ALOOKUP (IO_fs_inode_tbl fs) fnm)) (explode out))
   else ALOOKUP (IO_fs_inode_tbl fs) fnm))`,
  CHEAT_TAC);;

let ALOOKUP_add_stderr_inode_tbl = prove
 (`STD_streams fs ==> (
   ALOOKUP (IO_fs_inode_tbl ((add_stdo 2 "stderr") fs err)) fnm =
   (if fnm = UStream (implode "stderr") then
     SOME (APPEND (THE (ALOOKUP (IO_fs_inode_tbl fs) fnm)) (explode err))
   else ALOOKUP (IO_fs_inode_tbl fs) fnm))`,
  CHEAT_TAC);;

let ALOOKUP_add_stdout_infds = prove
 (`STD_streams fs ==> (
   ALOOKUP (IO_fs_infds ((add_stdo 1 "stdout") fs out)) fd =
   (if fd = 1 then
     SOME ((I ## I ## ((+) (strlen out))) (THE (ALOOKUP (IO_fs_infds fs)
       fd)))
   else ALOOKUP (IO_fs_infds fs) fd))`,
  CHEAT_TAC);;

let ALOOKUP_add_stderr_infds = prove
 (`STD_streams fs ==> (
   ALOOKUP (IO_fs_infds ((add_stdo 2 "stderr") fs err)) fd =
   (if fd = 2 then
     SOME ((I ## I ## ((+) (strlen err))) (THE (ALOOKUP (IO_fs_infds fs)
       fd)))
   else ALOOKUP (IO_fs_infds fs) fd))`,
  CHEAT_TAC);;

(* -- *)

let cake_extract_writes = prove
 (`wfcl cl ==>
   (let events = MAP get_output_io_event (cake_io_events cl (stdin_fs inp))
     in
   let out = extract_writes 1 events in
   let err = extract_writes 2 events in
   if has_help_flag (TL cl) then
     (out = explode help_string) /\ (err = "")
   else if has_version_flag (TL cl) then
     (out = explode current_build_info_str) /\ (err = "")
   else if has_pancake_flag (TL cl) then
     let (cout,cerr) = compile_pancake_32 (TL cl) inp in
     (out = explode (mlvector_concat (append cout))) /\
     (err = explode cerr)
   else let (cout,cerr) = compile_32 (TL cl) inp in
     (out = explode (mlvector_concat (append cout))) /\
     (err = explode cerr))`,
  CHEAT_TAC);;

let cake_ag32_next = prove
 (`SUM (MAP strlen cl) + LENGTH cl <= cline_size /\ wfcl cl /\
   LENGTH inp <= stdin_size /\
   is_ag32_init_state (ag32_memory_init_memory code data (extcalls
     (lab_to_target_config_ffi_names (backend_config_lab_conf info))) (cl,inp))
     ms0 ==>
   (?k1. !k. k1 <= k ==>
     (let ms = ITER k Next ms0 in
     let outs = MAP (get_ag32_io_event) (ffi_state_io_events ms) in
       (?_PC ms = machine_config_halt_pc ((ag32_machine_config (extcalls
         (lab_to_target_config_ffi_names (backend_config_lab_conf info)))
         (LENGTH code) (LENGTH data)))) /\
       (get_mem_word (?_MEM ms) (?_PC ms) = Encode (asm_Jump (fAdd,(n2w
         0),Imm (n2w 0)))) /\
       outs <<= MAP get_output_io_event (cake_io_events cl (stdin_fs inp))
         /\
       ((?_R ms (n2w (machine_config_ptr_reg ((ag32_machine_config (extcalls
         (lab_to_target_config_ffi_names (backend_config_lab_conf info)))
         (LENGTH code) (LENGTH data))))) = (n2w 0)) ==>
        (outs = MAP get_output_io_event (cake_io_events cl (stdin_fs
          inp))))))`,
  CHEAT_TAC);;

(* HOL4 ag32BootstrapProofScript.sml:561-562: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
