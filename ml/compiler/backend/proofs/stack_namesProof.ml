(* ======================================================== *)
(*  stack_namesProof: ported from HOL4's
    compiler/backend/proofs/stack_namesProofScript.sml
    A proof theory about stack_names.ml, with 2 definitions and 38
    theorems.  Needed by stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_names
*)

needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

cake_hide_consts
  ["code_buffer","code_buffer";
   "memory","memory"];;

let rename_state_def = cake_define
  `rename_state compile_rest f s = stackSem_state_ffi_save_regs_fupd (K
  (IMAGE (tlookup f) (stackSem_state_ffi_save_regs s)))
  (stackSem_state_compile_oracle_fupd (K ((I ## stack_names_compile f ##
  I) o stackSem_state_compile_oracle s)) (stackSem_state_compile_fupd (K
  compile_rest) (stackSem_state_code_fupd (K (fromAList
  (stack_names_compile f (toAList (stackSem_state_code s)))))
  (stackSem_state_regs_fupd (K (MAP_KEYS (tlookup f)
  (stackSem_state_regs s)))
    s))))`;;

let rename_state_with_clock = cake_theorem "rename_state_with_clock"
  (fun () ->
    `rename_state c f (stackSem_state_clock_fupd (K k) s) =
  state_clock_fupd (K k) (rename_state c f s)`)
  CHEAT_TAC;;

let rename_state_const = cake_theorem "rename_state_const[simp]"
  (fun () ->
    `state_memory
        (rename_state c f s) = stackSem_state_memory s /\ be
        (rename_state c f s) = stackSem_state_be s /\ state_mdomain
        (rename_state c f s) = stackSem_state_mdomain s /\
          state_sh_mdomain
        (rename_state c f s) = stackSem_state_sh_mdomain s /\
          state_code_buffer
        (rename_state c f s) = stackSem_state_code_buffer s /\
          state_clock
        (rename_state c f s) = stackSem_state_clock s /\ compile
        (rename_state c f s) = c /\ stackSem_state_use_stack
        (rename_state c f s) = stackSem_state_use_stack s /\
          fp_regs
        (rename_state c f s) = stackSem_state_fp_regs s`)
  CHEAT_TAC;;

let rename_state_with_memory = cake_theorem "rename_state_with_memory"
  (fun () ->
    `rename_state c f (stackSem_state_memory_fupd (K k) s) =
  state_memory_fupd (K k) (rename_state c f s)`)
  CHEAT_TAC;;

let dec_clock_rename_state = cake_theorem "dec_clock_rename_state"
  (fun () ->
    `dec_clock (rename_state c x y) = rename_state c x (dec_clock y)`)
  CHEAT_TAC;;

let mem_load_rename_state = cake_theorem "mem_load_rename_state[simp]"
  (fun () ->
    `mem_load x (rename_state c f s) = mem_load x s`)
  CHEAT_TAC;;

let mem_store_rename_state = cake_theorem "mem_store_rename_state[simp]"
  (fun () ->
    `mem_store x y (rename_state c f s) = OPTION_MAP (rename_state c
  f) (mem_store x y s)`)
  CHEAT_TAC;;

let get_var_find_name = cake_theorem "get_var_find_name[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
      get_var (tlookup f v) (rename_state c f s) = get_var v s`)
  CHEAT_TAC;;

let get_var_imm_find_name = cake_theorem "get_var_imm_find_name[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     get_var_imm (ri_find_name f ri) (rename_state c f s) =
     get_var_imm ri s`)
  CHEAT_TAC;;

let FLOOKUP_rename_state_find_name =
  cake_theorem "FLOOKUP_rename_state_find_name[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     FLOOKUP (stackSem_state_regs (rename_state c f s)) (tlookup
       f k) = FLOOKUP (stackSem_state_regs s) k`)
  CHEAT_TAC;;

let sh_mem_load_rename_state =
  cake_theorem "sh_mem_load_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_load (tlookup f x) y (rename_state c f s) =
     (FST (sh_mem_load x y s),(rename_state c f) (SND
       (sh_mem_load x y s)))`)
  CHEAT_TAC;;

let sh_mem_store_rename_state =
  cake_theorem "sh_mem_store_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_store (tlookup f x) y (rename_state c f s) =
     ((FST (sh_mem_store x y s):('a stackSem_result)
       option),(rename_state c f) (SND (sh_mem_store x y s)))`)
  CHEAT_TAC;;

let sh_mem_load_byte_rename_state =
  cake_theorem "sh_mem_load_byte_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_load_byte (tlookup f x) y (rename_state c f s) =
     (FST (sh_mem_load_byte x y s),(rename_state c f) (SND
       (sh_mem_load_byte x y s)))`)
  CHEAT_TAC;;

let sh_mem_store_byte_rename_state =
  cake_theorem "sh_mem_store_byte_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_store_byte (tlookup f x) y (rename_state c f s) =
     (FST (sh_mem_store_byte x y s),(rename_state c f) (SND
       (sh_mem_store_byte x y s)))`)
  CHEAT_TAC;;

let sh_mem_load16_rename_state =
  cake_theorem "sh_mem_load16_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_load16 (tlookup f x) y (rename_state c f s) =
     (FST (sh_mem_load16 x y s),(rename_state c f) (SND
       (sh_mem_load16 x y s)))`)
  CHEAT_TAC;;

let sh_mem_store16_rename_state =
  cake_theorem "sh_mem_store16_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_store16 (tlookup f x) y (rename_state c f s) =
     (FST (sh_mem_store16 x y s),(rename_state c f) (SND
       (sh_mem_store16 x y s)))`)
  CHEAT_TAC;;

let sh_mem_load32_rename_state =
  cake_theorem "sh_mem_load32_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_load32 (tlookup f x) y (rename_state c f s) =
     (FST (sh_mem_load32 x y s),(rename_state c f) (SND
       (sh_mem_load32 x y s)))`)
  CHEAT_TAC;;

let sh_mem_store32_rename_state =
  cake_theorem "sh_mem_store32_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_store32 (tlookup f x) y (rename_state c f s) =
     (FST (sh_mem_store32 x y s),(rename_state c f) (SND
       (sh_mem_store32 x y s)))`)
  CHEAT_TAC;;

let sh_mem_op_rename_store = cake_theorem "sh_mem_op_rename_store[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     sh_mem_op op (tlookup f r) a (rename_state c f s) =
     (FST (sh_mem_op op r a s),(rename_state c f) (SND (sh_mem_op
       op r a s)))`)
  CHEAT_TAC;;

let stack_namesProof_prog_comp_eta = cake_theorem "prog_comp_eta[local]"
  (fun () ->
    `stack_names_prog_comp f = (\(x,y). (x,stack_names_comp f y))`)
  CHEAT_TAC;;

let find_code_rename_state = cake_theorem "find_code_rename_state[simp]"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     find_code (dest_find_name f dest) (stackSem_state_regs
       (rename_state c f s)) (state_code (rename_state c f s)) =
     OPTION_MAP (stack_names_comp f) (find_code dest
       (stackSem_state_regs s) (stackSem_state_code s))`)
  CHEAT_TAC;;

let set_var_find_name = cake_theorem "set_var_find_name"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     rename_state c f (set_var x y z) =
     set_var (tlookup f x) y (rename_state c f z)`)
  CHEAT_TAC;;

let set_fp_var_find_name = cake_theorem "set_fp_var_find_name"
  (fun () ->
    `rename_state c f (set_fp_var x y z) =
     set_fp_var x y (rename_state c f z)`)
  CHEAT_TAC;;

let inst_rename = cake_theorem "inst_rename"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV ==>
     inst (inst_find_name f i) (rename_state c f s) =
     OPTION_MAP (rename_state c f) (inst i s)`)
  CHEAT_TAC;;

let stack_namesProof_MAP_FST_compile =
  cake_theorem "MAP_FST_compile[simp]"
  (fun () ->
    `MAP FST (stack_names_compile f c) = MAP FST c`)
  CHEAT_TAC;;

let domain_rename_state_code =
  cake_theorem "domain_rename_state_code[simp]"
  (fun () ->
    `domain (state_code (rename_state c f s)) = domain
  (stackSem_state_code s)`)
  CHEAT_TAC;;

let comp_STOP_Loop = cake_theorem "comp_STOP_Loop[local]"
  (fun () ->
    `stack_names_comp f (STOP (Loop c1)) =
       STOP (Loop (stack_names_comp f c1))`)
  CHEAT_TAC;;

let stack_namesProof_get_labels_comp =
  cake_theorem "get_labels_comp[local]"
  (fun () ->
    `!f p. stackSem_get_labels (stack_names_comp f p) =
  stackSem_get_labels p`)
  CHEAT_TAC;;

let loc_check_rename_state =
  cake_theorem "loc_check_rename_state[local]"
  (fun () ->
    `loc_check (state_code (rename_state c f s)) (l1,l2) =
       loc_check (stackSem_state_code s) (l1,l2)`)
  CHEAT_TAC;;

let stack_namesProof_comp_correct = cake_theorem "comp_correct[local]"
  (fun () ->
    `!p s r t.
        evaluate (p,s) = (r,t) /\ BIJ (tlookup f) UNIV UNIV /\
        ~(stackSem_state_use_alloc s) /\ ~(stackSem_state_use_store
          s) /\ ~(stackSem_state_use_stack s) /\ stackSem_state_compile
        s = (\cfg. c cfg o (stack_names_compile f)) ==>
        evaluate (stack_names_comp f p,rename_state c f s) =
          (r,rename_state c f t)`)
  CHEAT_TAC;;

let stack_namesProof_compile_semantics =
  cake_theorem "compile_semantics"
  (fun () ->
    `BIJ (tlookup f) UNIV UNIV /\
      ~(stackSem_state_use_alloc s) /\ ~(stackSem_state_use_store
        s) /\ ~(stackSem_state_use_stack s) /\ stackSem_state_compile
      s = (\cfg. c cfg o (stack_names_compile f)) ==>
      semantics start (rename_state c f s) = semantics start s`)
  CHEAT_TAC;;

let compile_semantics_alt = cake_theorem "compile_semantics_alt[local]"
  (fun () ->
    `!s t.
         BIJ (tlookup f) UNIV UNIV /\ (rename_state
           (stackSem_state_compile t) f s = t) /\ stackSem_state_compile
         s = (\c. stackSem_state_compile t c o (stack_names_compile
           f)) /\
         ~(stackSem_state_use_alloc s) /\
           ~(stackSem_state_use_store s) /\ ~(stackSem_state_use_stack
           s) ==>
         semantics start t = semantics start s`)
  CHEAT_TAC;;

let make_init_def = cake_define
  `stack_namesProof_make_init f code oracle'
  (s:('a,'c,'ffi)stackSem_state) = stackSem_state_ffi_save_regs_fupd (K
  (IMAGE (LINV (tlookup f) UNIV) (stackSem_state_ffi_save_regs s)))
  (stackSem_state_compile_oracle_fupd (K oracle')
  (stackSem_state_compile_fupd (K (\cfg. stackSem_state_compile s cfg o
  (stack_names_compile f))) (stackSem_state_regs_fupd (K (MAP_KEYS (LINV
  (tlookup f) UNIV) (stackSem_state_regs s))) (stackSem_state_code_fupd
  (K code)
     s))))
   // code_buffer := <| position := 0w; buffer := []; space_left := 0 |>;
   // data_buffer := <| position := 0w; buffer := []; space_left := 0 |>;`;;
hol4_overload "make_init" "stack_namesProof_make_init";;

let stack_namesProof_make_init_semantics =
  cake_theorem "make_init_semantics"
  (fun () ->
    `~(stackSem_state_use_alloc s) /\ ~(stackSem_state_use_store s) /\
  ~(stackSem_state_use_stack s) /\
     BIJ (tlookup f) UNIV UNIV /\ ALL_DISTINCT (MAP FST code) /\
       stackSem_state_code
     s = fromAList (stack_names_compile f code) /\
       stackSem_state_compile_oracle
     s = (I ## stack_names_compile f ## I) o oracle ==>
     semantics start s = semantics start
       (stack_namesProof_make_init f (fromAList code) oracle s)`)
  CHEAT_TAC;;

let stack_names_lab_pres = cake_theorem "stack_names_lab_pres"
  (fun () ->
    `!f p.
     stackProps_extract_labels p = stackProps_extract_labels
       (stack_names_comp f p)`)
  CHEAT_TAC;;

let names_ok_imp = cake_theorem "names_ok_imp[local]"
  (fun () ->
    `stack_names_names_ok f (asm_config_reg_count c)
  (asm_config_avoid_regs c) ==>
     (!n. reg_name n c ==>
     reg_ok (tlookup f n) c)`)
  CHEAT_TAC;;

let names_ok_imp2 = cake_theorem "names_ok_imp2[local]"
  (fun () ->
    `stack_names_names_ok f (asm_config_reg_count c)
  (asm_config_avoid_regs c) /\ ~(n = n') /\
     reg_name n c /\ reg_name n' c ==> ~(tlookup f n = tlookup f
       n')`)
  CHEAT_TAC;;

let stack_names_comp_stack_asm_ok =
  cake_theorem "stack_names_comp_stack_asm_ok[local]"
  (fun () ->
    `!f p.
     stack_asm_name c p /\ stack_names_names_ok f
       (asm_config_reg_count c) (asm_config_avoid_regs c) /\
     fixed_names f c ==>
     stack_asm_ok c (stack_names_comp f p)`)
  CHEAT_TAC;;

let stack_names_stack_asm_ok = cake_theorem "stack_names_stack_asm_ok"
  (fun () ->
    `EVERY (\(n,p). stack_asm_name c p) prog /\
     stack_names_names_ok f (asm_config_reg_count c)
       (asm_config_avoid_regs c) /\
     fixed_names f c ==>
     EVERY (\(n,p). stack_asm_ok c p) (stack_names_compile f
       prog)`)
  CHEAT_TAC;;

let stack_names_call_args = cake_theorem "stack_names_call_args"
  (fun () ->
    `stack_names_compile f p = p' /\
     EVERY (\p. call_args p 1 2 3 4 0) (MAP SND p) ==>
     EVERY (\p. call_args p (tlookup f 1)
                            (tlookup f 2)
                            (tlookup f 3)
                            (tlookup f 4)
                            (tlookup f 0)) (MAP SND p')`)
  CHEAT_TAC;;

cake_hide_consts [];;
