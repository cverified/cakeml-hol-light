(* ======================================================== *)
(*  stackProps: ported from HOL4's
    compiler/backend/semantics/stackPropsScript.sml
    A proof theory, with 24 definitions and 54 theorems.  Needed by
    7 files of the port.  *)
(* ======================================================== *)

(*
  Properties about stackLang and its semantics
*)

needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "stackProps"
  ["backendProps"; "stackSem"; "stack_names"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer"];;


(* HOL4 stackPropsScript.sml:11-18: a theorem that HOL4 states as the value
   of an ML expression: case_eq_thms *)

(* set_store_const *)
let stackProps_set_store_const = prove
 (`stackSem_state_ffi
      (stackSem_set_store x y z) = stackSem_state_ffi z
        /\ stackSem_state_clock
      (stackSem_set_store x y z) = stackSem_state_clock z
        /\ stackSem_state_use_alloc
      (stackSem_set_store x y z) = stackSem_state_use_alloc z
        /\ stackSem_state_use_store
      (stackSem_set_store x y z) = stackSem_state_use_store z
        /\ stackSem_state_use_stack
      (stackSem_set_store x y z) = stackSem_state_use_stack z
        /\ stackSem_state_code
      (stackSem_set_store x y z) = stackSem_state_code z
        /\ stackSem_state_be
      (stackSem_set_store x y z) = stackSem_state_be z
        /\ stackSem_state_gc_fun
      (stackSem_set_store x y z) = stackSem_state_gc_fun z
        /\ stackSem_state_memory
      (stackSem_set_store x y z) = stackSem_state_memory z
        /\ stackSem_state_mdomain
      (stackSem_set_store x y z) = stackSem_state_mdomain z
        /\ stackSem_state_sh_mdomain
      (stackSem_set_store x y z) = stackSem_state_sh_mdomain z
        /\ stackSem_state_bitmaps
      (stackSem_set_store x y z) = stackSem_state_bitmaps z
        /\ stackSem_state_data_buffer
      (stackSem_set_store x y z) = stackSem_state_data_buffer z
        /\ stackSem_state_code_buffer
      (stackSem_set_store x y z) = stackSem_state_code_buffer z
        /\ stackSem_state_compile
      (stackSem_set_store x y z) = stackSem_state_compile z
        /\ stackSem_state_compile_oracle
      (stackSem_set_store x y z) = stackSem_state_compile_oracle z
        /\ stackSem_state_stack_space
      (stackSem_set_store x y z) = stackSem_state_stack_space z
        /\ stackSem_state_stack
      (stackSem_set_store x y z) = stackSem_state_stack z`,
  CHEAT_TAC);;
add_simp stackProps_set_store_const;;

(* set_store_with_const *)
let stackProps_set_store_with_const = prove
 (`stackSem_set_store x y (stackSem_state_clock_fupd (K a) z) =
  stackSem_state_clock_fupd (K a) (stackSem_set_store x y z)`,
  CHEAT_TAC);;
add_simp stackProps_set_store_with_const;;

(* set_var_const *)
let stackProps_set_var_const = prove
 (`stackSem_state_ffi
      (stackSem_set_var x y z) = stackSem_state_ffi z
        /\ stackSem_state_clock
      (stackSem_set_var x y z) = stackSem_state_clock z
        /\ stackSem_state_use_alloc
      (stackSem_set_var x y z) = stackSem_state_use_alloc z
        /\ stackSem_state_use_store
      (stackSem_set_var x y z) = stackSem_state_use_store z
        /\ stackSem_state_use_stack
      (stackSem_set_var x y z) = stackSem_state_use_stack z
        /\ stackSem_state_code
      (stackSem_set_var x y z) = stackSem_state_code z /\ stackSem_state_be
      (stackSem_set_var x y z) = stackSem_state_be z
        /\ stackSem_state_fp_regs
      (stackSem_set_var x y z) = stackSem_state_fp_regs z
        /\ stackSem_state_data_buffer
      (stackSem_set_var x y z) = stackSem_state_data_buffer z
        /\ stackSem_state_code_buffer
      (stackSem_set_var x y z) = stackSem_state_code_buffer z
        /\ stackSem_state_gc_fun
      (stackSem_set_var x y z) = stackSem_state_gc_fun z
        /\ stackSem_state_memory
      (stackSem_set_var x y z) = stackSem_state_memory z
        /\ stackSem_state_mdomain
      (stackSem_set_var x y z) = stackSem_state_mdomain z
        /\ stackSem_state_sh_mdomain
      (stackSem_set_var x y z) = stackSem_state_sh_mdomain z
        /\ stackSem_state_bitmaps
      (stackSem_set_var x y z) = stackSem_state_bitmaps z
        /\ stackSem_state_compile
      (stackSem_set_var x y z) = stackSem_state_compile z
        /\ stackSem_state_compile_oracle
      (stackSem_set_var x y z) = stackSem_state_compile_oracle z
        /\ stackSem_state_store
      (stackSem_set_var x y z) = stackSem_state_store z
        /\ stackSem_state_stack
      (stackSem_set_var x y z) = stackSem_state_stack z
        /\ stackSem_state_stack_space
      (stackSem_set_var x y z) = stackSem_state_stack_space z`,
  CHEAT_TAC);;
add_simp stackProps_set_var_const;;

(* set_var_with_const *)
let stackProps_set_var_with_const = prove
 (`stackSem_set_var x y (stackSem_state_clock_fupd (K clk) z) =
  stackSem_state_clock_fupd (K clk) (stackSem_set_var x y z) /\
   stackSem_set_var x y (stackSem_state_memory_fupd (K m) z) =
     stackSem_state_memory_fupd (K m) (stackSem_set_var x y z) /\
   stackSem_set_var x y (stackSem_state_ffi_fupd (K ffi) z) =
     stackSem_state_ffi_fupd (K ffi) (stackSem_set_var x y z) /\
   stackSem_set_var x y (stackSem_state_stack_fupd (K stk) z) =
     stackSem_state_stack_fupd (K stk) (stackSem_set_var x y z) /\
   stackSem_set_var x y (stackSem_state_stack_space_fupd (K stk_space) z)
     = stackSem_state_stack_space_fupd (K stk_space) (stackSem_set_var x y z)`,
  CHEAT_TAC);;
add_simp stackProps_set_var_with_const;;

(* set_fp_var_with_const[local] *)
let stackProps_set_fp_var_with_const = prove
 (`stackSem_set_fp_var x y (stackSem_state_clock_fupd (K k) z) =
  stackSem_state_clock_fupd (K k) (stackSem_set_fp_var x y z)`,
  CHEAT_TAC);;
add_simp stackProps_set_fp_var_with_const;;

(* set_fp_var_const[local] *)
let stackProps_set_fp_var_const = prove
 (`stackSem_state_ffi
      (stackSem_set_fp_var x y z) = stackSem_state_ffi z
        /\ stackSem_state_clock
      (stackSem_set_fp_var x y z) = stackSem_state_clock z
        /\ stackSem_state_use_alloc
      (stackSem_set_fp_var x y z) = stackSem_state_use_alloc z
        /\ stackSem_state_use_store
      (stackSem_set_fp_var x y z) = stackSem_state_use_store z
        /\ stackSem_state_use_stack
      (stackSem_set_fp_var x y z) = stackSem_state_use_stack z
        /\ stackSem_state_code
      (stackSem_set_fp_var x y z) = stackSem_state_code z
        /\ stackSem_state_be
      (stackSem_set_fp_var x y z) = stackSem_state_be z
        /\ stackSem_state_gc_fun
      (stackSem_set_fp_var x y z) = stackSem_state_gc_fun z
        /\ stackSem_state_mdomain
      (stackSem_set_fp_var x y z) = stackSem_state_mdomain z
        /\ stackSem_state_sh_mdomain
      (stackSem_set_fp_var x y z) = stackSem_state_sh_mdomain z
        /\ stackSem_state_bitmaps
      (stackSem_set_fp_var x y z) = stackSem_state_bitmaps z
        /\ stackSem_state_compile
      (stackSem_set_fp_var x y z) = stackSem_state_compile z
        /\ stackSem_state_compile_oracle
      (stackSem_set_fp_var x y z) = stackSem_state_compile_oracle z
        /\ stackSem_state_stack
      (stackSem_set_fp_var x y z) = stackSem_state_stack z
        /\ stackSem_state_stack_space
      (stackSem_set_fp_var x y z) = stackSem_state_stack_space z`,
  CHEAT_TAC);;
add_simp stackProps_set_fp_var_const;;

(* get_fp_var_with_const[local] *)
let stackProps_get_fp_var_with_const = prove
 (`stackSem_get_fp_var x (stackSem_state_clock_fupd (K k) y) =
  stackSem_get_fp_var x y`,
  CHEAT_TAC);;
add_simp stackProps_get_fp_var_with_const;;

(* get_var_with_const *)
let stackProps_get_var_with_const = prove
 (`stackSem_get_var r (stackSem_state_clock_fupd (K clk) t) =
   (stackSem_get_var r t) /\
   stackSem_get_var r (stackSem_state_stack_space_fupd (K stk_space) t) =
   (stackSem_get_var r t)`,
  CHEAT_TAC);;
add_simp stackProps_get_var_with_const;;

(* get_vars_with_const[local] *)
let stackProps_get_vars_with_const = prove
 (`stackSem_get_vars xs (stackSem_state_clock_fupd (K k) y) =
  stackSem_get_vars xs y`,
  CHEAT_TAC);;
add_simp stackProps_get_vars_with_const;;

(* get_var_imm_with_const *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stackProps_get_var_imm_with_const = prove
 (cake_as_vars (fun () ->
    `stackSem_get_var_imm x (stackSem_state_clock_fupd (K k) y) =
  stackSem_get_var_imm x y`),
  CHEAT_TAC);;
add_simp stackProps_get_var_imm_with_const;;

(* set_fp_var_const *)
let stackProps_set_fp_var_const = prove
 (`stackSem_state_stack_space
     (stackSem_set_fp_var x y z) = stackSem_state_stack_space z
       /\ stackSem_state_stack
     (stackSem_set_fp_var x y z) = stackSem_state_stack z`,
  CHEAT_TAC);;
add_simp stackProps_set_fp_var_const;;

let empty_env_const = prove
 (`stackSem_state_ffi
      (stackSem_empty_env x) = stackSem_state_ffi x /\ stackSem_state_clock
      (stackSem_empty_env x) = stackSem_state_clock x
        /\ stackSem_state_use_alloc
      (stackSem_empty_env z) = stackSem_state_use_alloc z
        /\ stackSem_state_use_store
      (stackSem_empty_env z) = stackSem_state_use_store z
        /\ stackSem_state_use_stack
      (stackSem_empty_env z) = stackSem_state_use_stack z
        /\ stackSem_state_code
      (stackSem_empty_env z) = stackSem_state_code z /\ stackSem_state_be
      (stackSem_empty_env z) = stackSem_state_be z /\ stackSem_state_gc_fun
      (stackSem_empty_env z) = stackSem_state_gc_fun z
        /\ stackSem_state_mdomain
      (stackSem_empty_env z) = stackSem_state_mdomain z
        /\ stackSem_state_sh_mdomain
      (stackSem_empty_env z) = stackSem_state_sh_mdomain z
        /\ stackSem_state_bitmaps
      (stackSem_empty_env z) = stackSem_state_bitmaps z
        /\ stackSem_state_data_buffer
      (stackSem_empty_env z) = stackSem_state_data_buffer z
        /\ stackSem_state_code_buffer
      (stackSem_empty_env z) = stackSem_state_code_buffer z
        /\ stackSem_state_compile
      (stackSem_empty_env z) = stackSem_state_compile z
        /\ stackSem_state_compile_oracle
      (stackSem_empty_env z) = stackSem_state_compile_oracle z`,
  CHEAT_TAC);;
add_simp empty_env_const;;

let empty_env_with_const = prove
 (`stackSem_empty_env (stackSem_state_clock_fupd (K y) x) =
  stackSem_state_clock_fupd (K y) (stackSem_empty_env x)`,
  CHEAT_TAC);;
add_simp empty_env_with_const;;

(* alloc_const *)
let stackProps_alloc_const = prove
 (`stackSem_alloc w s = (r,t) ==> stackSem_state_ffi t = stackSem_state_ffi s
  /\ stackSem_state_clock
    t = stackSem_state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ stackSem_state_code
    t = stackSem_state_code s /\ stackSem_state_be
    t = stackSem_state_be s /\ stackSem_state_gc_fun
    t = stackSem_state_gc_fun s /\ stackSem_state_mdomain
    t = stackSem_state_mdomain s /\ stackSem_state_sh_mdomain
    t = stackSem_state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ stackSem_state_compile
    t = stackSem_state_compile s /\ stackSem_state_data_buffer
    t = stackSem_state_data_buffer s /\ stackSem_state_code_buffer
    t = stackSem_state_code_buffer s /\ stackSem_state_compile_oracle
    t = stackSem_state_compile_oracle s`,
  CHEAT_TAC);;

let store_const_sem_const = prove
 (`store_const_sem t1 t2 s = (r,t) ==> stackSem_state_ffi t =
  stackSem_state_ffi s /\ stackSem_state_clock
    t = stackSem_state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ stackSem_state_code
    t = stackSem_state_code s /\ stackSem_state_be
    t = stackSem_state_be s /\ stackSem_state_gc_fun
    t = stackSem_state_gc_fun s /\ stackSem_state_mdomain
    t = stackSem_state_mdomain s /\ stackSem_state_sh_mdomain
    t = stackSem_state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ stackSem_state_compile
    t = stackSem_state_compile s /\ stackSem_state_store
    t = stackSem_state_store s /\ stackSem_state_data_buffer
    t = stackSem_state_data_buffer s /\ stackSem_state_code_buffer
    t = stackSem_state_code_buffer s /\ stackSem_state_compile_oracle
    t = stackSem_state_compile_oracle s`,
  CHEAT_TAC);;

(* gc_with_const *)
let stackProps_gc_with_const = prove
 (`stackSem_gc (stackSem_state_clock_fupd (K k) x) = OPTION_MAP (\s.
  stackSem_state_clock_fupd (K k) s) (stackSem_gc x)`,
  CHEAT_TAC);;
add_simp stackProps_gc_with_const;;

(* alloc_with_const *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stackProps_alloc_with_const = prove
 (cake_as_vars (fun () ->
    `stackSem_alloc x (stackSem_state_clock_fupd (K z) y) = (I ## (\s.
  stackSem_state_clock_fupd (K z) s)) (stackSem_alloc x y)`),
  CHEAT_TAC);;
add_simp stackProps_alloc_with_const;;

let store_const_sem_with_const = prove
 (`store_const_sem t1 t2 (stackSem_state_clock_fupd (K z) y) =
   (I ## (\s. stackSem_state_clock_fupd (K z) s)) (store_const_sem t1 t2
     y)`,
  CHEAT_TAC);;
add_simp store_const_sem_with_const;;

(* mem_load_with_const *)
let stackProps_mem_load_with_const = prove
 (`stackSem_mem_store x y (stackSem_state_clock_fupd (K k) z) = OPTION_MAP
  (\s. stackSem_state_clock_fupd (K k) s) (stackSem_mem_store x y z)`,
  CHEAT_TAC);;
add_simp stackProps_mem_load_with_const;;

(* sh_mem_load_with_const *)
let stackProps_sh_mem_load_with_const = prove
 (`(stackSem_sh_mem_load r x (stackSem_state_clock_fupd (K k) y)) = (I ##
  (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_load r x y)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_load_with_const;;

(* sh_mem_store_with_const *)
let stackProps_sh_mem_store_with_const = prove
 (`(stackSem_sh_mem_store x y (stackSem_state_clock_fupd (K k) z)) = (I ##
  (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_store x y z)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_store_with_const;;

(* sh_mem_load32_with_const *)
let stackProps_sh_mem_load32_with_const = prove
 (`(stackSem_sh_mem_load32 r x (stackSem_state_clock_fupd (K k) y)) = (I ##
  (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_load32 r x y)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_load32_with_const;;

(* sh_mem_store32_with_const *)
let stackProps_sh_mem_store32_with_const = prove
 (`(stackSem_sh_mem_store32 x y (stackSem_state_clock_fupd (K k) z)) = (I ##
  (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_store32 x y z)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_store32_with_const;;

(* sh_mem_load16_with_const *)
let stackProps_sh_mem_load16_with_const = prove
 (`(stackSem_sh_mem_load16 r x (stackSem_state_clock_fupd (K k) y)) = (I ##
  (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_load16 r x y)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_load16_with_const;;

(* sh_mem_store16_with_const *)
let stackProps_sh_mem_store16_with_const = prove
 (`(stackSem_sh_mem_store16 x y (stackSem_state_clock_fupd (K k) z)) = (I ##
  (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_store16 x y z)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_store16_with_const;;

(* sh_mem_load_byte_with_const *)
let stackProps_sh_mem_load_byte_with_const = prove
 (`(stackSem_sh_mem_load_byte r x (stackSem_state_clock_fupd (K k) y)) = (I
  ## (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_load_byte r x
  y)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_load_byte_with_const;;

(* sh_mem_store_byte_with_const *)
let stackProps_sh_mem_store_byte_with_const = prove
 (`(stackSem_sh_mem_store_byte x y (stackSem_state_clock_fupd (K k) z)) = (I
  ## (\s. stackSem_state_clock_fupd (K k) s)) (stackSem_sh_mem_store_byte x y
  z)`,
  CHEAT_TAC);;
add_simp stackProps_sh_mem_store_byte_with_const;;

(* [local] *)
let sh_mem_op_with_const = prove
 (`(sh_mem_op op x y (stackSem_state_clock_fupd (K k) z)) = (I ## (\s.
  stackSem_state_clock_fupd (K k) s)) (sh_mem_op op x y z)`,
  CHEAT_TAC);;
add_simp sh_mem_op_with_const;;

(* word_exp_with_const *)
let stackProps_word_exp_with_const = prove
 (`!s y k. stackSem_word_exp (stackSem_state_clock_fupd (K k) s) y =
  stackSem_word_exp s y`,
  CHEAT_TAC);;
add_simp stackProps_word_exp_with_const;;

(* assign_with_const *)
let stackProps_assign_with_const = prove
 (`stackSem_assign x y (stackSem_state_clock_fupd (K k) s) = OPTION_MAP (\s.
  stackSem_state_clock_fupd (K k) s) (stackSem_assign x y s)`,
  CHEAT_TAC);;
add_simp stackProps_assign_with_const;;


(* inst_const *)
let stackProps_inst_const = prove
 (`stackSem_inst i s = SOME t ==> stackSem_state_ffi
    t = stackSem_state_ffi s /\ stackSem_state_clock
    t = stackSem_state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ stackSem_state_code
    t = stackSem_state_code s /\ stackSem_state_be
    t = stackSem_state_be s /\ stackSem_state_gc_fun
    t = stackSem_state_gc_fun s /\ stackSem_state_mdomain
    t = stackSem_state_mdomain s /\ stackSem_state_sh_mdomain
    t = stackSem_state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ stackSem_state_compile
    t = stackSem_state_compile s /\ stackSem_state_compile_oracle
    t = stackSem_state_compile_oracle s`,
  CHEAT_TAC);;

(* inst_with_const *)
let stackProps_inst_with_const = prove
 (`stackSem_inst i (stackSem_state_clock_fupd (K k) s) = OPTION_MAP (\s.
  stackSem_state_clock_fupd (K k) s) (stackSem_inst i s)`,
  CHEAT_TAC);;
add_simp stackProps_inst_with_const;;

(* dec_clock_const *)
let stackProps_dec_clock_const = prove
 (`stackSem_state_ffi
      (stackSem_dec_clock s) = stackSem_state_ffi s
        /\ stackSem_state_use_alloc
      (stackSem_dec_clock z) = stackSem_state_use_alloc z
        /\ stackSem_state_use_store
      (stackSem_dec_clock z) = stackSem_state_use_store z
        /\ stackSem_state_use_stack
      (stackSem_dec_clock z) = stackSem_state_use_stack z
        /\ stackSem_state_stack
      (stackSem_dec_clock z) = stackSem_state_stack z
        /\ stackSem_state_store
      (stackSem_dec_clock z) = stackSem_state_store z /\ stackSem_state_code
      (stackSem_dec_clock z) = stackSem_state_code z
        /\ stackSem_state_data_buffer
      (stackSem_dec_clock z) = stackSem_state_data_buffer z
        /\ stackSem_state_code_buffer
      (stackSem_dec_clock z) = stackSem_state_code_buffer z
        /\ stackSem_state_fp_regs
      (stackSem_dec_clock z) = stackSem_state_fp_regs z /\ stackSem_state_be
      (stackSem_dec_clock z) = stackSem_state_be z /\ stackSem_state_gc_fun
      (stackSem_dec_clock z) = stackSem_state_gc_fun z
        /\ stackSem_state_memory
      (stackSem_dec_clock z) = stackSem_state_memory z
        /\ stackSem_state_mdomain
      (stackSem_dec_clock z) = stackSem_state_mdomain z
        /\ stackSem_state_sh_mdomain
      (stackSem_dec_clock z) = stackSem_state_sh_mdomain z
        /\ stackSem_state_bitmaps
      (stackSem_dec_clock z) = stackSem_state_bitmaps z
        /\ stackSem_state_stack_space
      (stackSem_dec_clock z) = stackSem_state_stack_space z
        /\ stackSem_state_compile
      (stackSem_dec_clock z) = stackSem_state_compile z
        /\ stackSem_state_compile_oracle
      (stackSem_dec_clock z) = stackSem_state_compile_oracle z`,
  CHEAT_TAC);;
add_simp stackProps_dec_clock_const;;


let sh_mem_op_const = prove
 (`sh_mem_op op a r s = (res,t) ==> stackSem_state_clock
    t = stackSem_state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ stackSem_state_code
    t = stackSem_state_code s /\ stackSem_state_be
    t = stackSem_state_be s /\ stackSem_state_gc_fun
    t = stackSem_state_gc_fun s /\ stackSem_state_mdomain
    t = stackSem_state_mdomain s /\ stackSem_state_sh_mdomain
    t = stackSem_state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ stackSem_state_compile
    t = stackSem_state_compile s /\ stackSem_state_compile_oracle
    t = stackSem_state_compile_oracle s`,
  CHEAT_TAC);;
add_simp sh_mem_op_const;;

(* evaluate_consts *)
let stackProps_evaluate_consts = prove
 (`!c s r s1.
      stackSem_evaluate (c,s) = (r,s1) ==> stackSem_state_use_alloc
      s1 = stackSem_state_use_alloc s /\ stackSem_state_use_store
      s1 = stackSem_state_use_store s /\ stackSem_state_use_stack
      s1 = stackSem_state_use_stack s /\ stackSem_state_be
      s1 = stackSem_state_be s /\ stackSem_state_gc_fun
      s1 = stackSem_state_gc_fun s /\ stackSem_state_mdomain
      s1 = stackSem_state_mdomain s /\ stackSem_state_sh_mdomain
      s1 = stackSem_state_sh_mdomain s /\ stackSem_state_compile
      s1 = stackSem_state_compile s`,
  CHEAT_TAC);;

let evaluate_code_bitmaps = prove
 (`!c s r s1.
   stackSem_evaluate (c,s) = (r,s1) ==>
   (?n. stackSem_state_compile_oracle
    s1 = misc_shift_seq n (stackSem_state_compile_oracle s)
      /\ stackSem_state_code
    s1 = FOLDL sptree_union (stackSem_state_code s) (MAP (fromAList o FST o
      SND) (list_of_seq (stackSem_state_compile_oracle s) n))
      /\ stackSem_state_bitmaps
    s1 = APPEND (stackSem_state_bitmaps s) (FLAT (MAP (SND o SND)
      (list_of_seq (stackSem_state_compile_oracle s) n))))`,
  CHEAT_TAC);;

(* evaluate_mono *)
let stackProps_evaluate_mono = prove
 (`!c s r s1.
   stackSem_evaluate (c,s) = (r,s1) ==>
   isPREFIX (stackSem_state_bitmaps s) (stackSem_state_bitmaps s1) /\
   subspt (stackSem_state_code s) (stackSem_state_code s1)`,
  CHEAT_TAC);;

(* evaluate_io_events_mono *)
let stackProps_evaluate_io_events_mono = prove
 (`!exps s1 res s2.
    stackSem_evaluate (exps,s1) = (res,s2) ==> ffi_state_io_events
      (stackSem_state_ffi
    s1) <<= ffi_state_io_events (stackSem_state_ffi s2)`,
  CHEAT_TAC);;

let pair_map_eq = prove
 (`(f ## g) p = (x,y) <=> (?q r. p = (q,r) /\ x = (f q) /\ y = (g r))`,
  CHEAT_TAC);;

let bad_fun_return_IMP = prove
 (`stackSem_bad_fun_return res ==> res = NONE \/ (?n. res = SOME
  (stackLang_Break n) \/ res = SOME (stackLang_Continue n))`,
  CHEAT_TAC);;

let cont_loop_IMP = prove
 (`stackSem_cont_loop res ==> res = NONE \/ res = SOME (stackLang_Continue 0)`,
  CHEAT_TAC);;

(* evaluate_add_clock *)
let stackProps_evaluate_add_clock = prove
 (`!p s r s'.
    stackSem_evaluate (p,s) = (r,s') /\ ~(r = SOME stackSem_TimeOut) ==>
    stackSem_evaluate (p,stackSem_state_clock_fupd (K
      (stackSem_state_clock s + extra)) s) = (r,stackSem_state_clock_fupd (K
      (stackSem_state_clock s' + extra)) s')`,
  CHEAT_TAC);;

(* with_clock_ffi *)
let stackProps_with_clock_ffi = prove
 (`stackSem_state_ffi
      (stackSem_state_clock_fupd (K k) s) = stackSem_state_ffi s`,
  CHEAT_TAC);;

(* evaluate_add_clock_io_events_mono *)
let stackProps_evaluate_add_clock_io_events_mono = prove
 (`!e s. ffi_state_io_events (stackSem_state_ffi
     (SND (stackSem_evaluate (e,s)))) <<= ffi_state_io_events
       (stackSem_state_ffi
     (SND (stackSem_evaluate (e,stackSem_state_clock_fupd (K
       (stackSem_state_clock s + extra)) s))))`,
  CHEAT_TAC);;

let clock_neutral_def,clock_neutral_ind = define_shaped_rec
  "match"
  `clock_neutral r =
     match r with
       stackLang_Seq p1 p2 -> clock_neutral p1 /\ clock_neutral p2
     | stackLang_LocValue _ _ _ -> T
     | stackLang_Halt _ -> T
     | stackLang_Inst _ -> T
     | stackLang_Skip -> T
     | stackLang_If _ _ _ p1 p2 -> clock_neutral p1 /\ clock_neutral p2
     | r -> F`;;

(* [local] *)
let inst_clock_neutral = prove
 (`(stackSem_inst i s = SOME t ==> stackSem_inst i (stackSem_state_clock_fupd
  (K k) s) = SOME (stackSem_state_clock_fupd (K k) t)) /\
     (stackSem_inst i s = NONE ==> stackSem_inst i
       (stackSem_state_clock_fupd (K k) s) = NONE)`,
  CHEAT_TAC);;

(* [local] *)
let inst_clock_neutral_ffi = prove
 (`(stackSem_inst i s = SOME t ==> stackSem_inst i (stackSem_state_ffi_fupd (K
  k) s) = SOME (stackSem_state_ffi_fupd (K k) t)) /\
     (stackSem_inst i s = NONE ==> stackSem_inst i
       (stackSem_state_ffi_fupd (K k) s) = NONE)`,
  CHEAT_TAC);;

let evaluate_clock_neutral = prove
 (`!prog s res t.
      stackSem_evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      stackSem_evaluate (prog,stackSem_state_clock_fupd (K c) s) =
        (res,stackSem_state_clock_fupd (K c) t)`,
  CHEAT_TAC);;

let evaluate_ffi_neutral = prove
 (`!prog s res t.
      stackSem_evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      stackSem_evaluate (prog,stackSem_state_ffi_fupd (K c) s) =
        (res,stackSem_state_ffi_fupd (K c) t)`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let semantics_Terminate_IMP_PREFIX = prove
 (cake_as_vars (fun () ->
    `stackSem_semantics start s1 = ffi_Terminate x l ==> isPREFIX
  (ffi_state_io_events (stackSem_state_ffi s1)) l`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let semantics_Diverge_IMP_LPREFIX = prove
 (cake_as_vars (fun () ->
    `stackSem_semantics start s1 = ffi_Diverge l ==> LPREFIX (fromList
  (ffi_state_io_events (stackSem_state_ffi s1))) l`),
  CHEAT_TAC);;

let map_bitmap_length = prove
 (`!a b c x y z.
   map_bitmap a b c = SOME (x,y,z) ==>
   LENGTH c = LENGTH x + LENGTH z /\
   LENGTH x = LENGTH a`,
  CHEAT_TAC);;

let dec_stack_length = prove
 (`!bs enc orig_stack new_stack.
   stackSem_dec_stack bs enc orig_stack = SOME new_stack ==>
   LENGTH orig_stack = LENGTH new_stack`,
  CHEAT_TAC);;

let _ = size_thms "stackLang_prog";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stackProps_extract_labels_def,stackProps_extract_labels_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  `stackProps_extract_labels x1 =
     match x1 with
       stackLang_Call ret dest h ->
       (match ret with
         NONE -> []
       | SOME (ret_handler,_,l1,l2) ->
         (let ret_rest = stackProps_extract_labels ret_handler in
       (match h with
         NONE -> APPEND [(l1,l2)] ret_rest
       | SOME (prog,l1',l2') ->
         let h_rest = stackProps_extract_labels prog in APPEND (APPEND
           [(l1,l2); (l1',l2')] ret_rest) h_rest)))
     | stackLang_Loop s1 -> stackProps_extract_labels s1
     | stackLang_Seq s1 s2 -> APPEND (stackProps_extract_labels s1)
       (stackProps_extract_labels s2)
     | stackLang_If cmp r1 ri e2 e3 ->
       (APPEND (stackProps_extract_labels e2) (stackProps_extract_labels
         e3))
     | _ -> []`;;

let find_code_IMP_get_labels = prove
 (`stackSem_find_code d r code = SOME e ==>
    stackSem_get_labels e SUBSET loc_check code`,
  CHEAT_TAC);;

let addr_ok_def = define_general
  `addr_ok op (Addr a w) c <=>
   (reg_ok a c /\
    (if op IN {wordLang_Load,wordLang_Store,asm_Load32,asm_Store32} then
      (\c. asm_offset_ok 0 (asm_config_addr_offset c)) c w
    else if op IN {asm_Load16,asm_Store16} then (\c. asm_offset_ok 0
      (asm_config_hw_offset c)) c w /\ ~(asm_config_ISA c = Ag32) else (\c.
      asm_offset_ok 0 (asm_config_byte_offset c)) c w))`;;

(* TODO: This is not updated for Install, CBW and DBW *)
(* asm_ok out of stack_names *)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_asm_ok_def,stack_asm_ok_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x1)`
  `stack_asm_ok c x2 =
     match x2 with
       ((stackLang_Inst i):'a stackLang_prog) -> inst_ok i c
     | stackLang_ShMemOp op r ad -> reg_ok r c /\ addr_ok op ad c
     | stackLang_CodeBufferWrite r1 r2 -> r1 < asm_config_reg_count c /\ r2
       < asm_config_reg_count c /\ ~(MEM r1 (asm_config_avoid_regs c)) /\ ~(MEM
       r2 (asm_config_avoid_regs c))
     | stackLang_Seq p1 p2 -> stack_asm_ok c p1 /\ stack_asm_ok c p2
     | stackLang_If cmp n r p p' -> stack_asm_ok c p /\ stack_asm_ok c p'
     | stackLang_Loop p -> stack_asm_ok c p
     | stackLang_Raise n -> n < asm_config_reg_count c /\ ~(MEM n
       (asm_config_avoid_regs c))
     | stackLang_Return n -> n < asm_config_reg_count c /\ ~(MEM n
       (asm_config_avoid_regs c))
     | stackLang_Call r tar h ->
       (match tar with INR r -> r < asm_config_reg_count c /\ ~(MEM r
         (asm_config_avoid_regs c)) | _ -> T) /\
       (match r with SOME (p,_,_,_) -> stack_asm_ok c p /\
         (match h with
         SOME (p',_,_) -> stack_asm_ok c p'
         | _ -> T)
       | _ -> T)
     | _ -> T`;;

let reg_name_def = new_definition
  `reg_name r c <=>
   r < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)`;;

(* inst requirements just before stack_names *)

let reg_imm_name_def = define_cases
  `(reg_imm_name b (Reg r) c <=> reg_name r c) /\
   (reg_imm_name b (Imm w) c <=> asm_config_valid_imm c b w)`;;

let arith_name_def = new_definition
  `arith_name x1 c =
     match (x1,c) with
       (asm_Binop b r1 r2 ri,(c:'a asm_config)) ->
       (asm_config_two_reg_arith c ==> r1 = r2 \/ b = asm_Or /\ ri = Reg r2)
         /\ reg_name r1 c /\
       reg_name r2 c /\ reg_imm_name (INL b) ri c
     | (asm_Shift l r1 r2 (Imm i),c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name
         r2 c /\
       (i = (n2w 0) ==> l = Lsl) /\ w2n i < dimindex (:'a)
     | (asm_Shift l r1 r2 (Reg r3),c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
        reg_name r2 c /\ reg_name r3 c /\ (asm_config_ISA c = x86_64 ==> r3
          = 4)
     | (asm_Div r1 r2 r3,c) ->
       (reg_name r1 c /\ reg_name r2 c /\ reg_name r3 c /\ asm_config_ISA
       c IN {ARMv8,MIPS,RISC_V})
     | (asm_LongMul r1 r2 r3 r4,c) ->
       reg_name r1 c /\ reg_name r2 c /\ reg_name r3 c /\ reg_name r4 c /\
       (asm_config_ISA c = x86_64 ==> r1 = 3 /\ r2 = 0 /\ r3 = 0) /\
       (asm_config_ISA c = ARMv7 ==> ~(r1 = r2)) /\
       (asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/
         asm_config_ISA c = Ag32 ==> ~(r1 = r3) /\ ~(r1 = r4))
     | (asm_LongDiv r1 r2 r3 r4 r5,c) -> asm_config_ISA
       c = x86_64 /\ r1 = 0 /\ r2 = 3 /\ r3 = 3 /\ r4 = 0 /\
       reg_name r5 c
     | (asm_AddCarry r1 r2 r3 r4,c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name
         r2 c /\
       reg_name r3 c /\ reg_name r4 c /\
       (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1 = r3)
         /\ ~(r1 = r4))
     | (asm_AddOverflow r1 r2 r3 r4,c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name
         r2 c /\
       reg_name r3 c /\ reg_name r4 c /\
       (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1 = r3))
     | (asm_SubOverflow r1 r2 r3 r4,c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name
         r2 c /\
       reg_name r3 c /\ reg_name r4 c /\
       (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1 =
         r3))`;;

(* We could actually almost use fp_ok, except this needs to check reg_ok for
   some registers as well *)
let fp_name_def = define_cases
  `(fp_name (FPLess r d1 d2) (c:'a asm_config) <=>
          reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPLessEqual r d1 d2) (c:'a asm_config) <=>
          reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPEqual r d1 d2) (c:'a asm_config) <=>
          reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c) /\
   (fp_name (FPAbs d1 d2) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\ fp_reg_ok d1
              c /\ fp_reg_ok d2 c) /\
   (fp_name (FPNeg d1 d2) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\ fp_reg_ok d1
              c /\ fp_reg_ok d2 c) /\
   (fp_name (FPSqrt d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c
    /\ fp_reg_ok d2 c) /\
   (fp_name (FPAdd d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPSub d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPMul d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPDiv d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPFma d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_ISA c = ARMv7) /\
          2 < asm_config_fp_reg_count c /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c) /\
   (fp_name (FPMov d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c /\ fp_reg_ok
    d2 c) /\
   (fp_name (FPMovToReg r1 r2 d) (c:'a asm_config) <=>
          reg_name r1 c /\ ((dimindex (:'a) = 32) ==> ~(r1 = r2)
              /\ reg_name r2 c) /\
          fp_reg_ok d c) /\
   (fp_name (FPMovFromReg d r1 r2) (c:'a asm_config) <=>
          reg_name r1 c /\ ((dimindex (:'a) = 32) ==> ~(r1 = r2)
              /\ reg_name r2 c) /\
          fp_reg_ok d c) /\
   (fp_name (FPToInt d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c
    /\ fp_reg_ok d2 c) /\
   (fp_name (FPFromInt d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c
    /\ fp_reg_ok d2 c)`;;

let addr_name_def = define_general
  `addr_name m (Addr r w) c <=>
   reg_name r c /\
   (if m IN {wordLang_Load,wordLang_Store,asm_Load32,asm_Store32} then (\c.
     asm_offset_ok 0 (asm_config_addr_offset c)) c w
    else if m IN {asm_Load16,asm_Store16} then (\c. asm_offset_ok 0
      (asm_config_hw_offset c)) c w /\ ~(asm_config_ISA c = Ag32)
    else (\c. asm_offset_ok 0 (asm_config_byte_offset c)) c w)`;;

let inst_name_def = new_definition
  `inst_name c x2 =
     match x2 with
       asm_Const r w -> reg_name r c
     | asm_Mem m r a -> reg_name r c /\ addr_name m a c
     | asm_Arith x -> arith_name x c
     | asm_FP f -> fp_name f c
     | _ -> T`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_asm_name_def,stack_asm_name_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x1)`
  `stack_asm_name c x2 =
     match x2 with
       ((stackLang_Inst i):'a stackLang_prog) -> inst_name c i
     | stackLang_OpCurrHeap b r1 r2 ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\ reg_name
         r2 c
     | stackLang_ShMemOp op r a -> reg_name r c /\ addr_name op a c
     | stackLang_CodeBufferWrite r1 r2 -> reg_name r1 c /\ reg_name r2 c
     | stackLang_DataBufferWrite r1 r2 -> reg_name r1 c /\ reg_name r2 c
     | stackLang_Seq p1 p2 -> stack_asm_name c p1 /\ stack_asm_name c p2
     | stackLang_If cmp n r p p' -> stack_asm_name c p /\ stack_asm_name c
       p'
     | stackLang_Loop p -> stack_asm_name c p
     | stackLang_Raise n -> reg_name n c
     | stackLang_Return n -> reg_name n c
     | stackLang_Call r tar h ->
       (match tar with INR r -> reg_name r c | _ -> T) /\
       (match r with SOME (p,_,_,_) -> stack_asm_name c p /\
         (match h with
         SOME (p',_,_) -> stack_asm_name c p'
         | _ -> T)
       | _ -> T)
     | _ -> T`;;

let fixed_names_def = new_definition
  `fixed_names names c =
   if asm_config_ISA c = x86_64 then
     tlookup names 3 = 2 /\
     tlookup names 4 = 1 /\
     tlookup names 0 = 0
   else T`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_asm_remove_def,stack_asm_remove_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x1)`
  `stack_asm_remove c x2 =
     match x2 with
       ((stackLang_Get n s):'a stackLang_prog) -> reg_name n c
     | stackLang_OpCurrHeap binop v src -> reg_name v c /\ reg_name src c
     | stackLang_Set s n -> reg_name n c
     | stackLang_StackStore n n0 -> reg_name n c
     | stackLang_StackStoreAny n n0 -> reg_name n c /\ reg_name n0 c
     | stackLang_StackLoad n n0 -> reg_name n c
     | stackLang_StackLoadAny n n0 -> reg_name n c /\ reg_name n0 c
     | stackLang_StackGetSize n -> reg_name n c
     | stackLang_StackSetSize n -> reg_name n c
     | stackLang_BitmapLoad n n0 -> reg_name n c /\ reg_name n0 c
     | stackLang_StoreConsts n n0 _ -> reg_name n c /\ reg_name n0 c
     | stackLang_Seq p1 p2 -> stack_asm_remove c p1 /\ stack_asm_remove c p2
     | stackLang_If cmp n r p p' -> stack_asm_remove c p /\ stack_asm_remove
       c p'
     | stackLang_Loop p -> stack_asm_remove c p
     | stackLang_Call r tar h ->
       (match r with SOME (p,_,_,_) -> stack_asm_remove c p /\
         (match h with
         SOME (p',_,_) -> stack_asm_remove c p'
         | _ -> T)
       | _ -> T)
     | _ -> T`;;

(* Various syntactic properties required for correctness of the stackLang passes
  All of these are trivially preserved from word_to_stack until the pass that
  they are used.
*)

(* stack_alloc requires that Allocs have a fixed argument
   TODO: this can also be a semantic check...
*)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let alloc_arg_def,alloc_arg_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  `alloc_arg x1 =
     match x1 with
       stackLang_Alloc v -> (v = 1)
     | ((stackLang_Seq p1 p2):'a stackLang_prog) ->
        alloc_arg p1 /\ alloc_arg p2
     | ((stackLang_If c r ri p1 p2):'a stackLang_prog) ->
        alloc_arg p1 /\ alloc_arg p2
     | stackLang_Loop p1 ->
        alloc_arg p1
     | stackLang_Call x1 _ x2 ->
        (match x1 with SOME (y,r,_,_) -> alloc_arg y | NONE -> T) /\
        (match x2 with SOME (y,_,_) -> alloc_arg y | NONE -> T)
     | _ -> T`;;

(* stack_remove requires that all register arguments are bounded by k *)

(* the termination relation that HOL4 gives is
     MEASURE ((wordLang_exp_size ARB) o FST)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 stackPropsScript.sml:1027-1031: the tactic that proves the
   termination *)
let reg_bound_exp_def,reg_bound_exp_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_exp_size (\x. 0) x0)`
  `reg_bound_exp x1 k =
     match x1 with
       wordLang_Var n -> n < k
     | wordLang_Load e -> reg_bound_exp e k
     | wordLang_Shift _ e1 e2 -> reg_bound_exp e1 k /\ reg_bound_exp e2 k
     | wordLang_Lookup _ -> F
     | wordLang_Op _ es -> ALL (\e. reg_bound_exp e k) es
     | _ -> T`;;
add_simp reg_bound_exp_def;;

let reg_bound_inst_def = new_definition
  `reg_bound_inst x1 k =
     match x1 with
       asm_Mem _ n (Addr a _) -> n < k /\ a < k
     | asm_Const n _ -> n < k
     | asm_Arith (asm_Shift _ n r2 ri) -> r2 < k /\ n < k /\ (match ri with
       Reg r -> r < k | _ -> T)
     | asm_Arith (asm_Binop _ n r2 ri) -> r2 < k /\ n < k /\ (match ri with
       Reg r1 -> r1 < k | _ -> T)
     | asm_Arith (asm_Div r1 r2 r3) -> r1 < k /\ r2 < k /\ r3 < k
     | asm_Arith (asm_AddCarry r1 r2 r3 r4) -> r1 < k /\ r2 < k /\ r3 < k
       /\ r4 < k
     | asm_Arith (asm_AddOverflow r1 r2 r3 r4) -> r1 < k /\ r2 < k /\ r3 < k
       /\ r4 < k
     | asm_Arith (asm_SubOverflow r1 r2 r3 r4) -> r1 < k /\ r2 < k /\ r3 < k
       /\ r4 < k
     | asm_Arith (asm_LongMul r1 r2 r3 r4) -> r1 < k /\ r2 < k /\ r3 < k
       /\ r4 < k
     | asm_Arith (asm_LongDiv r1 r2 r3 r4 r5) -> r1 < k /\ r2 < k /\ r3 < k
       /\ r4 < k /\ r5 < k
     | asm_FP (FPLess r f1 f2) -> r < k
     | asm_FP (FPLessEqual r f1 f2) -> r < k
     | asm_FP (FPEqual r f1 f2) -> r < k
     | asm_FP (FPMovToReg r1 r2 d) -> r1 < k /\ r2 < k
     | asm_FP (FPMovFromReg d r1 r2) -> r1 < k /\ r2 < k
     | _ -> T`;;
add_simp reg_bound_inst_def;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let reg_bound_def,reg_bound_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x0)`
  `reg_bound x1 k =
     match x1 with
       stackLang_Halt v1 ->
        v1 < k
     | stackLang_Raise v1 ->
        v1 < k
     | stackLang_Get v1 n ->
        v1 < k
     | stackLang_OpCurrHeap op v1 v2 ->
        v1 < k /\ v2 < k
     | stackLang_Set n v1 ->
        v1 < k /\ ~(n = BitmapBase)
     | stackLang_LocValue v1 l1 l2 ->
        v1 < k
     | stackLang_StoreConsts t1 t2 _ ->
        3 < k /\ t1 < k /\ t2 < k
     | stackLang_Return v1 ->
        v1 < k
     | stackLang_JumpLower v1 v2 dest ->
        v1 < k /\ v2 < k
     | ((stackLang_Seq p1 p2):'a stackLang_prog) ->
        reg_bound p1 k /\ reg_bound p2 k
     | ((stackLang_If c r ri p1 p2):'a stackLang_prog) ->
        r < k /\ (match ri with Reg n -> n < k | _ -> T) /\
        reg_bound p1 k /\ reg_bound p2 k
     | stackLang_Loop p1 ->
        reg_bound p1 k
     | stackLang_Halt n -> n < k
     | stackLang_FFI ffi_index ptr' len' ptr2' len2' ret' ->
        ptr' < k /\ len' < k /\ ptr2' < k /\ len2' < k /\ ret' < k
     | stackLang_Call x1 dest x2 ->
        (match dest with INR i -> i < k | _ -> T) /\
        (match x1 with NONE -> T
         | SOME (y,r,_,_) -> reg_bound y k /\ r < k /\
                             (match x2 with SOME (y,_,_) -> reg_bound y k |
                               NONE -> T))
     | stackLang_Install ptr len dptr dlen ret ->
       ptr < k /\ len < k /\ dptr < k /\ dlen < k /\ ret < k
     | stackLang_ShMemOp op r (Addr a _) -> r < k /\ a < k
     | stackLang_CodeBufferWrite r1 r2 ->
       r1 < k /\ r2 < k
     | stackLang_DataBufferWrite r1 r2 ->
       r1 < k /\ r2 < k
     | stackLang_BitmapLoad r v -> r < k /\ v < k
     | stackLang_Inst i -> reg_bound_inst i k
     | stackLang_StackStore r _ -> r < k
     | stackLang_StackSetSize r -> r < k
     | stackLang_StackGetSize r -> r < k
     | stackLang_StackLoad r n -> r < k
     | stackLang_StackLoadAny r r2 -> r < k /\ r2 < k
     | stackLang_StackStore r n -> r < k
     | stackLang_StackStoreAny r r2 -> r < k /\ r2 < k
     | _ -> T`;;

(* Finally, stack_to_lab requires correct arguments for Call/FFI/Install calls *)
let call_args_def,call_args_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  `call_args x1 ptr len ptr2 len2 ret =
     match x1 with
       ((stackLang_Seq p1 p2):'a stackLang_prog) ->
        call_args p1 ptr len ptr2 len2 ret /\
        call_args p2 ptr len ptr2 len2 ret
     | ((stackLang_If c r ri p1 p2):'a stackLang_prog) ->
        call_args p1 ptr len ptr2 len2 ret /\
        call_args p2 ptr len ptr2 len2 ret
     | stackLang_Loop p1 ->
        call_args p1 ptr len ptr2 len2 ret
     | stackLang_Halt n -> (n = ptr)
     | stackLang_FFI ffi_index ptr' len' ptr2' len2' ret' ->
        ptr' = ptr /\ len' = len /\ ptr2' = ptr2 /\ len2' = len2 /\ ret' =
          ret
     | stackLang_Call x1 _ x2 ->
        (match x1 with NONE -> T
         | SOME (y,r,_,_) ->
             call_args y ptr len ptr2 len2 ret /\ r = ret /\
             (match x2 with SOME (y,_,_) -> call_args y ptr len ptr2 len2
               ret | NONE -> T))
     | stackLang_Install ptr' len' _ _ ret' ->
        ptr' = ptr /\ len' = len /\ ret' = ret
     | _ -> T`;;

(* TODO: remove "stack_" prefix from these functions *)

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stack_get_handler_labels_def,stack_get_handler_labels_ind = define_wf
  `MEASURE (\(x0,x1). stackLang_prog_size (\x. 0) x1)`
  `stack_get_handler_labels n x2 =
     match x2 with
       stackLang_Call r d h ->
       (match r with SOME (x,_,_) -> stack_get_handler_labels n x UNION
         (match h with SOME (x,l1,l2) -> (if l1 = n then {(l1,l2)} else {})
           UNION (stack_get_handler_labels n x) | _ -> {})
       | _ -> {})
     | stackLang_Seq p1 p2 -> stack_get_handler_labels n p1 UNION
       stack_get_handler_labels n p2
     | stackLang_If _ _ _ p1 p2 -> stack_get_handler_labels n p1 UNION
       stack_get_handler_labels n p2
     | stackLang_Loop p -> stack_get_handler_labels n p
     | _ -> {}`;;
add_simp stack_get_handler_labels_def;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stackProps_get_code_labels_def,stackProps_get_code_labels_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  `stackProps_get_code_labels x1 =
     match x1 with
       stackLang_Call r d h ->
       (match d with INL x -> {(x,0)} | _ -> {}) UNION
       (match r with SOME (x,_,_) -> stackProps_get_code_labels x | _ -> {})
         UNION
       (match h with SOME (x,_,_) -> stackProps_get_code_labels x | _ -> {})
     | stackLang_Seq p1 p2 -> stackProps_get_code_labels p1 UNION
       stackProps_get_code_labels p2
     | stackLang_If _ _ _ p1 p2 -> stackProps_get_code_labels p1 UNION
       stackProps_get_code_labels p2
     | stackLang_Loop p -> stackProps_get_code_labels p
     | stackLang_JumpLower _ _ t -> {(t,0)}
     | stackLang_RawCall t -> {(t,1)}
     | stackLang_LocValue _ l1 l2 -> {(l1,l2)}
     | stackLang_StoreConsts _ _ (SOME l) -> {(l,0)}
     | _ -> {}`;;
add_simp stackProps_get_code_labels_def;;

(* elabs gives a set of existing code labels *)
let stack_good_code_labels_def = new_definition
  `stack_good_code_labels p elabs <=>
   UNIONS (IMAGE stackProps_get_code_labels (set_of_list (MAP SND p)))
     SUBSET
   UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) p))
     UNION
   IMAGE (\n. n,0) (set_of_list (MAP FST p)) UNION IMAGE (\n. n,0) elabs
     UNION
   IMAGE (\n. n,1) (set_of_list (MAP FST p)) UNION IMAGE (\n. n,1) elabs`;;

let stack_good_handler_labels_def = new_definition
  `stack_good_handler_labels p <=>
   restrict_nonzero (UNIONS (IMAGE stackProps_get_code_labels (set_of_list
     (MAP SND p)))) SUBSET
   UNIONS (set_of_list (MAP (\(n,pp). stack_get_handler_labels n pp) p))
     UNION
   IMAGE (\n. n,1) (set_of_list (MAP FST p))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let stackProps_no_install_def,stackProps_no_install_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  `stackProps_no_install x1 =
     match x1 with
       stackLang_Call r d h ->
       ((match r with SOME (x,_,_) -> stackProps_no_install x | _ -> T) /\
        (match h with SOME (x,_,_) -> stackProps_no_install x | _ -> T))
     | stackLang_Seq p1 p2 -> (stackProps_no_install p1
       /\ stackProps_no_install p2)
     | stackLang_If _ _ _ p1 p2 -> (stackProps_no_install p1
       /\ stackProps_no_install p2)
     | stackLang_Loop p -> stackProps_no_install p
     | stackLang_Install _ _ _ _ _ -> F
     | _ -> T`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let no_shmemop_def,no_shmemop_ind = define_wf
  `MEASURE (\x0. stackLang_prog_size (\x. 0) x0)`
  `no_shmemop x1 =
     match x1 with
       stackLang_Call r d h ->
       ((match r with SOME (x,_,_) -> no_shmemop x | _ -> T) /\
        (match h with SOME (x,_,_) -> no_shmemop x | _ -> T))
     | stackLang_Seq p1 p2 -> (no_shmemop p1 /\ no_shmemop p2)
     | stackLang_If _ _ _ p1 p2 -> (no_shmemop p1 /\ no_shmemop p2)
     | stackLang_Loop p -> no_shmemop p
     | stackLang_ShMemOp _ _ _ -> F
     | _ -> T`;;

(* and the interface *)
let _ = unhide_overloads ();;
