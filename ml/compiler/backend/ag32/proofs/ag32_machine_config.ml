(* ======================================================== *)
(*  ag32_machine_config: ported from HOL4's
    compiler/backend/ag32/proofs/ag32_machine_configScript.sml
    A proof theory, with 8 definitions and 2 theorems.  Needed by
    ag32BootstrapProof.ml, ag32_basis_ffiProof.ml and
    ag32_memoryProof.ml.  *)
(* ======================================================== *)

(*
  Define the Sliver machine configuration.
  This includes the FFI interference oracle.
*)

needs "basis/Marshalling.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/ag32/ag32_memory.ml";;
needs "compiler/backend/ag32/proofs/ag32_configProof.ml";;
needs "compiler/backend/lab_to_target.ml";;
needs "compiler/backend/semantics/targetSem.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "compiler/inference/infer.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_machine_config"
  ["ag32_configProof"; "ag32_memory"; "asmSem"; "targetSem"];;
(* HOL4 ancestors outside the port: ag32_target *)

let ag32_init_asm_state_def = new_definition
  `ag32_init_asm_state mem' md = mk_asm_state (K (n2w 0)) ARB mem' md (n2w
  0) 0 2 F F`;;

let ag32_prog_addresses_def = new_definition
  `ag32_prog_addresses num_ffis LENGTH_code LENGTH_data =
     {w | n2w heap_start_offset <=+ w /\ w <+ n2w (heap_start_offset +
       heap_size)} UNION
     {w | n2w (code_start_offset num_ffis) <=+ w /\
           w <+ n2w (code_start_offset num_ffis + LENGTH_code + 4 *
             LENGTH_data)}`;;

let ag32_startup_addresses_def = new_definition
  `ag32_startup_addresses =
       {w | w <+ n2w startup_code_size} UNION
       {w | n2w heap_start_offset <=+ w /\ w <+ n2w (heap_start_offset +
         4 * 5)}`;;

let ag32_ccache_interfer_def = new_definition
  `ag32_ccache_interfer num_ffis (_,_,ms) = ?_R_fupd (K (((n2w 0) =+ n2w
  (ffi_jumps_offset + num_ffis * ffi_offset + 4)) (?_R ms))) (?_PC_fupd (K (?_R
  ms (n2w 0)))
     ms)`;;

let ag32_ffi_mem_update_def = new_definition
  `ag32_ffi_mem_update name conf bytes new_bytes mem' =
     if (name = (implode "write")) then
       if (HD new_bytes = (n2w 0)) then
         match bytes with (CONS n1 (CONS n0 (CONS off1 (CONS off0 tll)))) ->
           if ~(LENGTH conf = 8) then mem' else let k = MIN (w22n [n1; n0])
             output_buffer_size in
           let written = TAKE k (DROP (w22n [off1; off0]) tll) in
             asm_write_bytearray (n2w output_offset) (APPEND (APPEND conf
               [(n2w 0); (n2w 0); n1; n0]) written) mem'
         | _ -> mem'
       else ((n2w output_offset) =+ (n2w 1)) mem'
     else if (name = (implode "read")) then
       match new_bytes with (CONS zz (CONS k1 (CONS k0 _))) ->
         if (zz = (n2w 0)) then
           set_mem_word (n2w stdin_offset)
             (get_mem_word mem' (n2w stdin_offset) + n2w (w22n [k1; k0]))
               mem'
         else mem'
       | _ -> mem'
     else mem'`;;

let ag32_ffi_interfer_def = new_definition
  `ag32_ffi_interfer ffi_names' md (index,new_bytes,ms) =
     (let name = EL index ffi_names' in
     let exitpc = THE (ALOOKUP ffi_exitpcs name) in
     if name = (implode "") then ffi_state_OverflowFlag_fupd (K F)
       (ffi_state_CarryFlag_fupd (K F) (ffi_state_R_fupd (K (((n2w 0) =+ n2w
       exitpc) (((n2w 5) =+ (n2w 0)) (?_R ms)))) (ffi_state_PC_fupd (K (?_R ms
       (n2w 0)))
       ms)))
     else let new_mem = ((n2w (ffi_code_start_offset - 1)) =+ n2w (THE
       (ALOOKUP FFI_codes name))) (?_MEM ms) in
     let new_mem = asm_write_bytearray (?_R ms (n2w 3)) new_bytes new_mem in
     let new_mem =
       ag32_ffi_mem_update name
         (THE (read_bytearray (?_R ms (n2w 1)) (w2n (?_R ms (n2w 2))) (\a.
           if a IN md then SOME (?_MEM ms a) else NONE)))
         (THE (read_bytearray (?_R ms (n2w 3)) (w2n (?_R ms (n2w 4))) (\a.
           if a IN md then SOME (?_MEM ms a) else NONE)))
         new_bytes new_mem in ffi_state_MEM_fupd (K new_mem)
           (ffi_state_io_events_fupd (K (APPEND (ffi_state_io_events ms)
           [new_mem])) (ffi_state_OverflowFlag_fupd (K F)
           (ffi_state_CarryFlag_fupd (K F) (ffi_state_R_fupd (K (((n2w 0) =+
           n2w exitpc)
                  (((n2w 1) =+ (n2w 0))
                  (((n2w 2) =+ (n2w 0))
                  (((n2w 3) =+ (n2w 0))
                  (((n2w 4) =+ (n2w 0))
                  (((n2w 5) =+ (n2w 0))
                  (((n2w 6) =+ (n2w 0))
                  (((n2w 7) =+ (n2w 0))
                  (((n2w 8) =+ (n2w 0)) (?_R ms)))))))))))
                    (ffi_state_PC_fupd (K (?_R ms (n2w 0)))
       ms))))))`;;

let ag32_machine_config_def = new_definition
  `ag32_machine_config ffi_names' LENGTH_code LENGTH_data =
   let num_ffis = LENGTH ffi_names' in
   let md = ag32_prog_addresses num_ffis LENGTH_code LENGTH_data in
   mk_machine_config md {} (REVERSE (list_of_seq (\i. n2w
     (ffi_jumps_offset + i * ffi_offset)) num_ffis)) (MAP ffi_ExtCall
     ffi_names') 1 2 3 4 (K (ag32_ffi_interfer ffi_names' md)) [60; 61; 62]
     (K I) (n2w (ffi_jumps_offset + (num_ffis + 1) * ffi_offset)) (n2w
     (ffi_jumps_offset + (num_ffis + 0) * ffi_offset)) (K
     (ag32_ccache_interfer num_ffis)) ag32_target []`;;

let is_ag32_machine_config_ag32_machine_config = prove
 (`is_ag32_machine_config (ag32_machine_config a b c)`,
  CHEAT_TAC);;

let ag32_ffi_mem_domain_def = new_definition
  `ag32_ffi_mem_domain =
     {w | n2w startup_code_size <=+ (w:word32) /\
           w <+ n2w ffi_code_start_offset}`;;

let ag32_ffi_mem_domain_DISJOINT_prog_addresses = prove
 (`num_ffis <= LENGTH FFI_codes /\
   code_start_offset num_ffis + lc + ld <= memory_size ==>
   DISJOINT (ag32_ffi_mem_domain) (ag32_prog_addresses num_ffis lc ld)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
