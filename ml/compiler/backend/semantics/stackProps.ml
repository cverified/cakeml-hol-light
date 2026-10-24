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
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_names.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "data_buffer","data_buffer";
   "memory","memory"];;


(* HOL4 stackPropsScript.sml:11-18: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

(* set_store_const[simp] *)
let stackProps_set_store_const = prove
 (`state_ffi
      (set_store x y z) = state_ffi z /\ state_clock
      (set_store x y z) = state_clock z /\ stackSem_state_use_alloc
      (set_store x y z) = stackSem_state_use_alloc z /\
        stackSem_state_use_store
      (set_store x y z) = stackSem_state_use_store z /\
        stackSem_state_use_stack
      (set_store x y z) = stackSem_state_use_stack z /\ state_code
      (set_store x y z) = state_code z /\ be
      (set_store x y z) = be z /\ state_gc_fun
      (set_store x y z) = state_gc_fun z /\ state_memory
      (set_store x y z) = state_memory z /\ state_mdomain
      (set_store x y z) = state_mdomain z /\ state_sh_mdomain
      (set_store x y z) = state_sh_mdomain z /\
        stackSem_state_bitmaps
      (set_store x y z) = stackSem_state_bitmaps z /\
        state_data_buffer
      (set_store x y z) = state_data_buffer z /\ state_code_buffer
      (set_store x y z) = state_code_buffer z /\ compile
      (set_store x y z) = compile z /\ compile_oracle
      (set_store x y z) = compile_oracle z /\
        stackSem_state_stack_space
      (set_store x y z) = stackSem_state_stack_space z /\ stack
      (set_store x y z) = stack z`,
  CHEAT_TAC);;

(* set_store_with_const[simp] *)
let stackProps_set_store_with_const = prove
 (`set_store x y (state_clock_fupd (K a) z) = state_clock_fupd (K a)
  (set_store x y z)`,
  CHEAT_TAC);;

(* set_var_const[simp] *)
let stackProps_set_var_const = prove
 (`state_ffi
      (set_var x y z) = state_ffi z /\ state_clock
      (set_var x y z) = state_clock z /\ stackSem_state_use_alloc
      (set_var x y z) = stackSem_state_use_alloc z /\
        stackSem_state_use_store
      (set_var x y z) = stackSem_state_use_store z /\
        stackSem_state_use_stack
      (set_var x y z) = stackSem_state_use_stack z /\ state_code
      (set_var x y z) = state_code z /\ be
      (set_var x y z) = be z /\ fp_regs
      (set_var x y z) = fp_regs z /\ state_data_buffer
      (set_var x y z) = state_data_buffer z /\ state_code_buffer
      (set_var x y z) = state_code_buffer z /\ state_gc_fun
      (set_var x y z) = state_gc_fun z /\ state_memory
      (set_var x y z) = state_memory z /\ state_mdomain
      (set_var x y z) = state_mdomain z /\ state_sh_mdomain
      (set_var x y z) = state_sh_mdomain z /\ stackSem_state_bitmaps
      (set_var x y z) = stackSem_state_bitmaps z /\ compile
      (set_var x y z) = compile z /\ compile_oracle
      (set_var x y z) = compile_oracle z /\ state_store
      (set_var x y z) = state_store z /\ stack
      (set_var x y z) = stack z /\ stackSem_state_stack_space
      (set_var x y z) = stackSem_state_stack_space z`,
  CHEAT_TAC);;

(* set_var_with_const[simp] *)
let stackProps_set_var_with_const = prove
 (`set_var x y (state_clock_fupd (K clk) z) = state_clock_fupd (K clk)
  (set_var x y z) /\
   set_var x y (state_memory_fupd (K m) z) = state_memory_fupd (K m)
     (set_var x y z) /\
   set_var x y (state_ffi_fupd (K ffi) z) = state_ffi_fupd (K ffi)
     (set_var x y z) /\
   set_var x y (stack_fupd (K stk) z) = stack_fupd (K stk) (set_var x
     y z) /\
   set_var x y (stackSem_state_stack_space_fupd (K stk_space) z) =
     stackSem_state_stack_space_fupd (K stk_space) (set_var x y z)`,
  CHEAT_TAC);;

(* set_fp_var_with_const[local,simp] *)
let stackProps_set_fp_var_with_const = prove
 (`set_fp_var x y (state_clock_fupd (K k) z) = state_clock_fupd (K k)
  (set_fp_var x y z)`,
  CHEAT_TAC);;

(* set_fp_var_const[local,simp] *)
let stackProps_set_fp_var_const = prove
 (`state_ffi
      (set_fp_var x y z) = state_ffi z /\ state_clock
      (set_fp_var x y z) = state_clock z /\ stackSem_state_use_alloc
      (set_fp_var x y z) = stackSem_state_use_alloc z /\
        stackSem_state_use_store
      (set_fp_var x y z) = stackSem_state_use_store z /\
        stackSem_state_use_stack
      (set_fp_var x y z) = stackSem_state_use_stack z /\ state_code
      (set_fp_var x y z) = state_code z /\ be
      (set_fp_var x y z) = be z /\ state_gc_fun
      (set_fp_var x y z) = state_gc_fun z /\ state_mdomain
      (set_fp_var x y z) = state_mdomain z /\ state_sh_mdomain
      (set_fp_var x y z) = state_sh_mdomain z /\
        stackSem_state_bitmaps
      (set_fp_var x y z) = stackSem_state_bitmaps z /\ compile
      (set_fp_var x y z) = compile z /\ compile_oracle
      (set_fp_var x y z) = compile_oracle z /\ stack
      (set_fp_var x y z) = stack z /\ stackSem_state_stack_space
      (set_fp_var x y z) = stackSem_state_stack_space z`,
  CHEAT_TAC);;

(* get_fp_var_with_const[local,simp] *)
let stackProps_get_fp_var_with_const = prove
 (`get_fp_var x (state_clock_fupd (K k) y) = get_fp_var x y`,
  CHEAT_TAC);;

(* get_var_with_const[simp] *)
let stackProps_get_var_with_const = prove
 (`get_var r (state_clock_fupd (K clk) t) =
   (get_var r t) /\
   get_var r (stackSem_state_stack_space_fupd (K stk_space) t) =
   (get_var r t)`,
  CHEAT_TAC);;

(* get_vars_with_const[local,simp] *)
let stackProps_get_vars_with_const = prove
 (`get_vars xs (state_clock_fupd (K k) y) = get_vars xs y`,
  CHEAT_TAC);;

(* get_var_imm_with_const[simp] *)
let stackProps_get_var_imm_with_const = prove
 (`get_var_imm x (state_clock_fupd (K k) y) = get_var_imm x y`,
  CHEAT_TAC);;

(* set_fp_var_const[simp] *)
let stackProps_set_fp_var_const = prove
 (`stackSem_state_stack_space
     (set_fp_var x y z) = stackSem_state_stack_space z /\ stack
     (set_fp_var x y z) = stack z`,
  CHEAT_TAC);;

(* [simp] *)
let empty_env_const = prove
 (`state_ffi
      (stackSem_empty_env x) = state_ffi x /\ state_clock
      (stackSem_empty_env x) = state_clock x /\
        stackSem_state_use_alloc
      (stackSem_empty_env z) = stackSem_state_use_alloc z /\
        stackSem_state_use_store
      (stackSem_empty_env z) = stackSem_state_use_store z /\
        stackSem_state_use_stack
      (stackSem_empty_env z) = stackSem_state_use_stack z /\
        state_code
      (stackSem_empty_env z) = state_code z /\ be
      (stackSem_empty_env z) = be z /\ state_gc_fun
      (stackSem_empty_env z) = state_gc_fun z /\ state_mdomain
      (stackSem_empty_env z) = state_mdomain z /\ state_sh_mdomain
      (stackSem_empty_env z) = state_sh_mdomain z /\
        stackSem_state_bitmaps
      (stackSem_empty_env z) = stackSem_state_bitmaps z /\
        state_data_buffer
      (stackSem_empty_env z) = state_data_buffer z /\
        state_code_buffer
      (stackSem_empty_env z) = state_code_buffer z /\ compile
      (stackSem_empty_env z) = compile z /\ compile_oracle
      (stackSem_empty_env z) = compile_oracle z`,
  CHEAT_TAC);;

(* [simp] *)
let empty_env_with_const = prove
 (`stackSem_empty_env (state_clock_fupd (K y) x) = state_clock_fupd (K
  y) (stackSem_empty_env x)`,
  CHEAT_TAC);;

(* alloc_const *)
let stackProps_alloc_const = prove
 (`alloc w s = (r,t) ==> state_ffi t = state_ffi s /\ state_clock
    t = state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ state_code
    t = state_code s /\ be
    t = be s /\ state_gc_fun
    t = state_gc_fun s /\ state_mdomain
    t = state_mdomain s /\ state_sh_mdomain
    t = state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ compile
    t = compile s /\ state_data_buffer
    t = state_data_buffer s /\ state_code_buffer
    t = state_code_buffer s /\ compile_oracle
    t = compile_oracle s`,
  CHEAT_TAC);;

let store_const_sem_const = prove
 (`store_const_sem t1 t2 s = (r,t) ==> state_ffi t = state_ffi s /\
  state_clock
    t = state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ state_code
    t = state_code s /\ be
    t = be s /\ state_gc_fun
    t = state_gc_fun s /\ state_mdomain
    t = state_mdomain s /\ state_sh_mdomain
    t = state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ compile
    t = compile s /\ state_store
    t = state_store s /\ state_data_buffer
    t = state_data_buffer s /\ state_code_buffer
    t = state_code_buffer s /\ compile_oracle
    t = compile_oracle s`,
  CHEAT_TAC);;

(* gc_with_const[simp] *)
let stackProps_gc_with_const = prove
 (`gc (state_clock_fupd (K k) x) = OPTION_MAP (\s. state_clock_fupd (K
  k) s) (gc x)`,
  CHEAT_TAC);;

(* alloc_with_const[simp] *)
let stackProps_alloc_with_const = prove
 (`alloc x (state_clock_fupd (K z) y) = (I ## (\s. state_clock_fupd (K
  z) s)) (alloc x y)`,
  CHEAT_TAC);;

(* [simp] *)
let store_const_sem_with_const = prove
 (`store_const_sem t1 t2 (state_clock_fupd (K z) y) =
   (I ## (\s. state_clock_fupd (K z) s)) (store_const_sem t1 t2 y)`,
  CHEAT_TAC);;

(* mem_load_with_const[simp] *)
let stackProps_mem_load_with_const = prove
 (`mem_store x y (state_clock_fupd (K k) z) = OPTION_MAP (\s.
  state_clock_fupd (K k) s) (mem_store x y z)`,
  CHEAT_TAC);;

(* sh_mem_load_with_const[simp] *)
let stackProps_sh_mem_load_with_const = prove
 (`(sh_mem_load r x (state_clock_fupd (K k) y)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_load r x y)`,
  CHEAT_TAC);;

(* sh_mem_store_with_const[simp] *)
let stackProps_sh_mem_store_with_const = prove
 (`(sh_mem_store x y (state_clock_fupd (K k) z)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_store x y z)`,
  CHEAT_TAC);;

(* sh_mem_load32_with_const[simp] *)
let stackProps_sh_mem_load32_with_const = prove
 (`(sh_mem_load32 r x (state_clock_fupd (K k) y)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_load32 r x y)`,
  CHEAT_TAC);;

(* sh_mem_store32_with_const[simp] *)
let stackProps_sh_mem_store32_with_const = prove
 (`(sh_mem_store32 x y (state_clock_fupd (K k) z)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_store32 x y z)`,
  CHEAT_TAC);;

(* sh_mem_load16_with_const[simp] *)
let stackProps_sh_mem_load16_with_const = prove
 (`(sh_mem_load16 r x (state_clock_fupd (K k) y)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_load16 r x y)`,
  CHEAT_TAC);;

(* sh_mem_store16_with_const[simp] *)
let stackProps_sh_mem_store16_with_const = prove
 (`(sh_mem_store16 x y (state_clock_fupd (K k) z)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_store16 x y z)`,
  CHEAT_TAC);;

(* sh_mem_load_byte_with_const[simp] *)
let stackProps_sh_mem_load_byte_with_const = prove
 (`(sh_mem_load_byte r x (state_clock_fupd (K k) y)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_load_byte r x y)`,
  CHEAT_TAC);;

(* sh_mem_store_byte_with_const[simp] *)
let stackProps_sh_mem_store_byte_with_const = prove
 (`(sh_mem_store_byte x y (state_clock_fupd (K k) z)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_store_byte x y z)`,
  CHEAT_TAC);;

(* [local,simp] *)
let sh_mem_op_with_const = prove
 (`(sh_mem_op op x y (state_clock_fupd (K k) z)) = (I ## (\s.
  state_clock_fupd (K k) s)) (sh_mem_op op x y z)`,
  CHEAT_TAC);;

(* word_exp_with_const[simp] *)
let stackProps_word_exp_with_const = prove
 (`!s y k. word_exp (state_clock_fupd (K k) s) y = word_exp s y`,
  CHEAT_TAC);;

(* assign_with_const[simp] *)
let stackProps_assign_with_const = prove
 (`assign x y (state_clock_fupd (K k) s) = OPTION_MAP (\s.
  state_clock_fupd (K k) s) (assign x y s)`,
  CHEAT_TAC);;


(* inst_const *)
let stackProps_inst_const = prove
 (`inst i s = SOME t ==> state_ffi
    t = state_ffi s /\ state_clock
    t = state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ state_code
    t = state_code s /\ be
    t = be s /\ state_gc_fun
    t = state_gc_fun s /\ state_mdomain
    t = state_mdomain s /\ state_sh_mdomain
    t = state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ compile
    t = compile s /\ compile_oracle
    t = compile_oracle s`,
  CHEAT_TAC);;

(* inst_with_const[simp] *)
let stackProps_inst_with_const = prove
 (`inst i (state_clock_fupd (K k) s) = OPTION_MAP (\s.
  state_clock_fupd (K k) s) (inst i s)`,
  CHEAT_TAC);;

(* dec_clock_const[simp] *)
let stackProps_dec_clock_const = prove
 (`state_ffi
      (dec_clock s) = state_ffi s /\ stackSem_state_use_alloc
      (dec_clock z) = stackSem_state_use_alloc z /\
        stackSem_state_use_store
      (dec_clock z) = stackSem_state_use_store z /\
        stackSem_state_use_stack
      (dec_clock z) = stackSem_state_use_stack z /\ stack
      (dec_clock z) = stack z /\ state_store
      (dec_clock z) = state_store z /\ state_code
      (dec_clock z) = state_code z /\ state_data_buffer
      (dec_clock z) = state_data_buffer z /\ state_code_buffer
      (dec_clock z) = state_code_buffer z /\ fp_regs
      (dec_clock z) = fp_regs z /\ be
      (dec_clock z) = be z /\ state_gc_fun
      (dec_clock z) = state_gc_fun z /\ state_memory
      (dec_clock z) = state_memory z /\ state_mdomain
      (dec_clock z) = state_mdomain z /\ state_sh_mdomain
      (dec_clock z) = state_sh_mdomain z /\ stackSem_state_bitmaps
      (dec_clock z) = stackSem_state_bitmaps z /\
        stackSem_state_stack_space
      (dec_clock z) = stackSem_state_stack_space z /\ compile
      (dec_clock z) = compile z /\ compile_oracle
      (dec_clock z) = compile_oracle z`,
  CHEAT_TAC);;


(* [simp] *)
let sh_mem_op_const = prove
 (`sh_mem_op op a r s = (res,t) ==> state_clock
    t = state_clock s /\ stackSem_state_use_alloc
    t = stackSem_state_use_alloc s /\ stackSem_state_use_store
    t = stackSem_state_use_store s /\ stackSem_state_use_stack
    t = stackSem_state_use_stack s /\ state_code
    t = state_code s /\ be
    t = be s /\ state_gc_fun
    t = state_gc_fun s /\ state_mdomain
    t = state_mdomain s /\ state_sh_mdomain
    t = state_sh_mdomain s /\ stackSem_state_bitmaps
    t = stackSem_state_bitmaps s /\ compile
    t = compile s /\ compile_oracle
    t = compile_oracle s`,
  CHEAT_TAC);;

(* evaluate_consts *)
let stackProps_evaluate_consts = prove
 (`!c s r s1.
      evaluate (c,s) = (r,s1) ==> stackSem_state_use_alloc
      s1 = stackSem_state_use_alloc s /\ stackSem_state_use_store
      s1 = stackSem_state_use_store s /\ stackSem_state_use_stack
      s1 = stackSem_state_use_stack s /\ be
      s1 = be s /\ state_gc_fun
      s1 = state_gc_fun s /\ state_mdomain
      s1 = state_mdomain s /\ state_sh_mdomain
      s1 = state_sh_mdomain s /\ compile
      s1 = compile s`,
  CHEAT_TAC);;

let evaluate_code_bitmaps = prove
 (`!c s r s1.
   evaluate (c,s) = (r,s1) ==>
   (?n. compile_oracle
    s1 = misc_shift_seq n (compile_oracle s) /\ state_code
    s1 = FOLDL sptree_union (state_code s) (MAP (fromAList o FST o
      SND) (GENLIST (compile_oracle s) n)) /\ stackSem_state_bitmaps
    s1 = stackSem_state_bitmaps s ++ FLAT (MAP (SND o SND) (GENLIST
      (compile_oracle s) n)))`,
  CHEAT_TAC);;

(* evaluate_mono *)
let stackProps_evaluate_mono = prove
 (`!c s r s1.
   evaluate (c,s) = (r,s1) ==>
   isPREFIX (stackSem_state_bitmaps s) (stackSem_state_bitmaps s1) /\
   subspt (state_code s) (state_code s1)`,
  CHEAT_TAC);;

(* evaluate_io_events_mono *)
let stackProps_evaluate_io_events_mono = prove
 (`!exps s1 res s2.
    evaluate (exps,s1) = (res,s2) ==> ffi_state_io_events (state_ffi
    s1) <<= ffi_state_io_events (state_ffi s2)`,
  CHEAT_TAC);;

let pair_map_eq = prove
 (`(f ## g) p = (x,y) <=> (?q r. p = (q,r) /\ x = (f q) /\ y = (g r))`,
  CHEAT_TAC);;

let bad_fun_return_IMP = prove
 (`bad_fun_return res ==> res = NONE \/ (?n. res = SOME (Break n) \/
  res = SOME (Continue n))`,
  CHEAT_TAC);;

let cont_loop_IMP = prove
 (`cont_loop res ==> res = NONE \/ res = SOME (Continue 0)`,
  CHEAT_TAC);;

(* evaluate_add_clock *)
let stackProps_evaluate_add_clock = prove
 (`!p s r s'.
    evaluate (p,s) = (r,s') /\ ~(r = SOME TimeOut) ==>
    evaluate (p,state_clock_fupd (K (state_clock s + extra)) s) =
      (r,state_clock_fupd (K (state_clock s' + extra)) s')`,
  CHEAT_TAC);;

(* with_clock_ffi *)
let stackProps_with_clock_ffi = prove
 (`state_ffi
      (state_clock_fupd (K k) s) = state_ffi s`,
  CHEAT_TAC);;

(* evaluate_add_clock_io_events_mono *)
let stackProps_evaluate_add_clock_io_events_mono = prove
 (`!e s. ffi_state_io_events (state_ffi
     (SND (evaluate (e,s)))) <<= ffi_state_io_events (state_ffi
     (SND (evaluate (e,state_clock_fupd (K (state_clock s + extra))
       s))))`,
  CHEAT_TAC);;

let clock_neutral_def = cake_define
  `clock_neutral r =
        match r with
          stackLang_Seq p1 p2 -> clock_neutral p1 /\ clock_neutral p2
        | (LocValue _1 _2 _3) -> T
        | (Halt _4) -> T
        | (Inst _5) -> T
        | (Skip) -> T
        | (If _6 _7 _8 p1 p2) -> clock_neutral p1 /\ clock_neutral p2
        | r -> F`;;

(* [local] *)
let inst_clock_neutral = prove
 (`(inst i s = SOME t ==> inst i (state_clock_fupd (K k) s) = SOME
  (state_clock_fupd (K k) t)) /\
     (inst i s = NONE ==> inst i (state_clock_fupd (K k) s) = NONE)`,
  CHEAT_TAC);;

(* [local] *)
let inst_clock_neutral_ffi = prove
 (`(inst i s = SOME t ==> inst i (state_ffi_fupd (K k) s) = SOME
  (state_ffi_fupd (K k) t)) /\
     (inst i s = NONE ==> inst i (state_ffi_fupd (K k) s) = NONE)`,
  CHEAT_TAC);;

let evaluate_clock_neutral = prove
 (`!prog s res t.
      evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      evaluate (prog,state_clock_fupd (K c) s) =
        (res,state_clock_fupd (K c) t)`,
  CHEAT_TAC);;

let evaluate_ffi_neutral = prove
 (`!prog s res t.
      evaluate (prog,s) = (res,t) /\ clock_neutral prog ==>
      evaluate (prog,state_ffi_fupd (K c) s) = (res,state_ffi_fupd
        (K c) t)`,
  CHEAT_TAC);;

let semantics_Terminate_IMP_PREFIX = prove
 (`semantics (start:num) s1 = ffi_Terminate x l ==> isPREFIX
  (ffi_state_io_events (state_ffi s1)) l`,
  CHEAT_TAC);;

let semantics_Diverge_IMP_LPREFIX = prove
 (`semantics (start:num) s1 = ffi_Diverge l ==> LPREFIX (fromList
  (ffi_state_io_events (state_ffi s1))) l`,
  CHEAT_TAC);;

let map_bitmap_length = prove
 (`!a b c x y z.
   map_bitmap a b c = SOME (x,y,z) ==>
   LENGTH c = LENGTH x + LENGTH z /\
   LENGTH x = LENGTH a`,
  CHEAT_TAC);;

let dec_stack_length = prove
 (`!bs enc orig_stack new_stack.
   dec_stack bs enc orig_stack = SOME new_stack ==>
   LENGTH orig_stack = LENGTH new_stack`,
  CHEAT_TAC);;

let stackProps_extract_labels_def = cake_define
  `stackProps_extract_labels x1 =
        match x1 with
          stackLang_Call ret dest h ->
       (match ret with
         NONE -> [] | SOME (ret_handler,_9,l1,l2) ->
         (let ret_rest = stackProps_extract_labels ret_handler in
       (match h with
         NONE -> [(l1,l2)] ++ ret_rest | SOME (prog,l1',l2') ->
         (let h_rest = stackProps_extract_labels prog in
         [(l1,l2); (l1',l2')] ++ ret_rest ++ h_rest))))
        | (Loop s1) -> stackProps_extract_labels s1
        | (Seq s1 s2) ->
       stackProps_extract_labels s1 ++ stackProps_extract_labels s2
        | (If cmp r1 ri e2 e3) ->
       (stackProps_extract_labels e2 ++ stackProps_extract_labels e3)
        | _10 -> []`;;
hol4_overload "extract_labels" "stackProps_extract_labels";;

let find_code_IMP_get_labels = prove
 (`find_code d r code = SOME e ==>
    stackSem_get_labels e SUBSET loc_check code`,
  CHEAT_TAC);;

let addr_ok_def = cake_define
  `addr_ok op (Addr a w) c <=>
   (reg_ok a c /\
    (if op IN {Load,Store,asm_Load32,asm_Store32} then (\c.
      asm_offset_ok 0 (asm_config_addr_offset c)) c w else if op IN
      {asm_Load16,asm_Store16} then (\c. asm_offset_ok 0
      (asm_config_hw_offset c)) c w /\ ~(asm_config_ISA c = Ag32)
      else (\c. asm_offset_ok 0 (asm_config_byte_offset c)) c w))`;;

(* TODO: This is not updated for Install, CBW and DBW *)
(* asm_ok out of stack_names *)
let stack_asm_ok_def = cake_define
  `stack_asm_ok c x2 =
        match x2 with
          ((Inst i):'a stackLang_prog) -> inst_ok i c
        | (stackLang_ShMemOp op r ad) -> reg_ok r c /\ addr_ok op ad
          c
        | (CodeBufferWrite r1 r2) -> r1 < asm_config_reg_count c /\
          r2 < asm_config_reg_count c /\ ~(MEM r1 (asm_config_avoid_regs
          c)) /\ ~(MEM r2 (asm_config_avoid_regs c))
        | (Seq p1 p2) -> stack_asm_ok c p1 /\ stack_asm_ok c p2
        | (If cmp n r p p') -> stack_asm_ok c p /\ stack_asm_ok c p'
        | (Loop p) -> stack_asm_ok c p
        | (Raise n) -> n < asm_config_reg_count c /\ ~(MEM n
          (asm_config_avoid_regs c))
        | (Return n) -> n < asm_config_reg_count c /\ ~(MEM n
          (asm_config_avoid_regs c))
        | (Call r tar h) ->
       (match tar with INR r -> r < asm_config_reg_count c /\ ~(MEM r
         (asm_config_avoid_regs c)) | _11 -> T) /\
       (match r with SOME (p,_12,_13,_14) -> stack_asm_ok c p /\
         (match h with
         SOME (p',_15,_16) -> stack_asm_ok c p' | _17 -> T) | _18 ->
           T)
        | _19 -> T`;;

let reg_name_def = cake_define
  `reg_name r c <=>
   r < asm_config_reg_count c - LENGTH (asm_config_avoid_regs c)`;;

(* inst requirements just before stack_names *)

let reg_imm_name_def = cake_define_list
  [`reg_imm_name b (Reg r) c <=> reg_name r c`;
   `reg_imm_name b (Imm w) c <=> asm_config_valid_imm c b w`];;

let arith_name_def = cake_define
  `arith_name x1 c =
        match (x1,c) with
          (asm_Binop b r1 r2 ri,(c:'a asm_config)) ->
       (asm_config_two_reg_arith c ==> r1 = r2 \/ b = Or /\ ri = Reg
         r2) /\ reg_name r1 c /\
       reg_name r2 c /\ reg_imm_name (INL b) ri c
        | ((Shift l r1 r2 (Imm i)),c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
         reg_name r2 c /\
       (i = (n2w 0) ==> l = Lsl) /\ w2n i < dimindex (:'a)
        | ((Shift l r1 r2 (Reg r3)),c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
        reg_name r2 c /\ reg_name r3 c /\ (asm_config_ISA c = x86_64
          ==> r3 = 4)
        | ((Div r1 r2 r3),c) ->
       (reg_name r1 c /\ reg_name r2 c /\ reg_name r3 c /\
         asm_config_ISA
       c IN {ARMv8,MIPS,RISC_V})
        | ((asm_LongMul r1 r2 r3 r4),c) ->
       reg_name r1 c /\ reg_name r2 c /\ reg_name r3 c /\ reg_name r4
         c /\
       (asm_config_ISA c = x86_64 ==> r1 = 3 /\ r2 = 0 /\ r3 = 0) /\
       (asm_config_ISA c = ARMv7 ==> ~(r1 = r2)) /\
       (asm_config_ISA c = ARMv8 \/ asm_config_ISA c = RISC_V \/
         asm_config_ISA c = Ag32 ==> ~(r1 = r3) /\ ~(r1 = r4))
        | ((asm_LongDiv r1 r2 r3 r4 r5),c) -> asm_config_ISA
       c = x86_64 /\ r1 = 0 /\ r2 = 3 /\ r3 = 3 /\ r4 = 0 /\
       reg_name r5 c
        | ((asm_AddCarry r1 r2 r3 r4),c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
         reg_name r2 c /\
       reg_name r3 c /\ reg_name r4 c /\
       (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1
         = r3) /\ ~(r1 = r4))
        | ((asm_AddOverflow r1 r2 r3 r4),c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
         reg_name r2 c /\
       reg_name r3 c /\ reg_name r4 c /\
       (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==> ~(r1
         = r3))
        | ((asm_SubOverflow r1 r2 r3 r4),c) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
         reg_name r2 c /\
       reg_name r3 c /\ reg_name r4 c /\
       (asm_config_ISA c = MIPS \/ asm_config_ISA c = RISC_V ==>
         ~(r1 = r3))`;;

(* We could actually almost use fp_ok, except this needs to check reg_ok for
   some registers as well *)
let fp_name_def = cake_define_list
  [`fp_name (FPLess r d1 d2) (c:'a asm_config) <=>
          reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_name (FPLessEqual r d1 d2) (c:'a asm_config) <=>
          reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_name (FPEqual r d1 d2) (c:'a asm_config) <=>
          reg_name r c /\ fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_name (FPAbs d1 d2) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\
            fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_name (FPNeg d1 d2) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (~(d1 = d2))) /\
            fp_reg_ok d1 c /\ fp_reg_ok d2 c`;
   `fp_name (FPSqrt d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c /\
  fp_reg_ok d2 c`;
   `fp_name (FPAdd d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_name (FPSub d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_name (FPMul d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_name (FPDiv d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_two_reg_arith c ==> (d1 = d2)) /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_name (FPFma d1 d2 d3) (c:'a asm_config) <=>
          (asm_config_ISA c = ARMv7) /\
          2 < asm_config_fp_reg_count c /\
          fp_reg_ok d1 c /\ fp_reg_ok d2 c /\ fp_reg_ok d3 c`;
   `fp_name (FPMov d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c /\
  fp_reg_ok d2 c`;
   `fp_name (FPMovToReg r1 r2 d) (c:'a asm_config) <=>
          reg_name r1 c /\ ((dimindex (:'a) = 32) ==> ~(r1 = r2) /\
            reg_name r2 c) /\
          fp_reg_ok d c`;
   `fp_name (FPMovFromReg d r1 r2) (c:'a asm_config) <=>
          reg_name r1 c /\ ((dimindex (:'a) = 32) ==> ~(r1 = r2) /\
            reg_name r2 c) /\
          fp_reg_ok d c`;
   `fp_name (FPToInt d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c /\
  fp_reg_ok d2 c`;
   `fp_name (FPFromInt d1 d2) (c:'a asm_config) <=> fp_reg_ok d1 c
  /\ fp_reg_ok d2 c`];;

let addr_name_def = cake_define
  `addr_name m (Addr r w) c <=>
   reg_name r c /\
   (if m IN {Load,Store,asm_Load32,asm_Store32} then (\c.
     asm_offset_ok 0 (asm_config_addr_offset c)) c w else if m IN
     {asm_Load16,asm_Store16} then (\c. asm_offset_ok 0
     (asm_config_hw_offset c)) c w /\ ~(asm_config_ISA c = Ag32) else
     (\c. asm_offset_ok 0 (asm_config_byte_offset c)) c w)`;;

let inst_name_def = cake_define
  `inst_name c x2 =
        match x2 with
          asm_Const r w -> reg_name r c
        | (asm_Mem m r a) -> reg_name r c /\ addr_name m a c
        | (Arith x) -> arith_name x c
        | (asm_FP f) -> fp_name f c
        | _20 -> T`;;

let stack_asm_name_def = cake_define
  `stack_asm_name c x2 =
        match x2 with
          ((Inst i):'a stackLang_prog) -> inst_name c i
        | (OpCurrHeap b r1 r2) ->
       (asm_config_two_reg_arith c ==> r1 = r2) /\ reg_name r1 c /\
         reg_name r2 c
        | (stackLang_ShMemOp op r a) -> reg_name r c /\ addr_name op
          a c
        | (CodeBufferWrite r1 r2) -> reg_name r1 c /\ reg_name r2 c
        | (DataBufferWrite r1 r2) -> reg_name r1 c /\ reg_name r2 c
        | (Seq p1 p2) -> stack_asm_name c p1 /\ stack_asm_name c p2
        | (If cmp n r p p') -> stack_asm_name c p /\ stack_asm_name c
          p'
        | (Loop p) -> stack_asm_name c p
        | (Raise n) -> reg_name n c
        | (Return n) -> reg_name n c
        | (Call r tar h) ->
       (match tar with INR r -> reg_name r c | _21 -> T) /\
       (match r with SOME (p,_22,_23,_24) -> stack_asm_name c p /\
         (match h with
         SOME (p',_25,_26) -> stack_asm_name c p' | _27 -> T) | _28
           -> T)
        | _29 -> T`;;

let fixed_names_def = cake_define
  `fixed_names names c =
   (if asm_config_ISA c = x86_64 then
     tlookup names 3 = 2 /\
     tlookup names 4 = 1 /\
     tlookup names 0 = 0 else T)`;;

let stack_asm_remove_def = cake_define
  `stack_asm_remove c x2 =
        match x2 with
          ((Get n s):'a stackLang_prog) -> reg_name n c
        | (OpCurrHeap binop v src) -> reg_name v c /\ reg_name src c
        | (Set s n) -> reg_name n c
        | (stackLang_StackStore n n0) -> reg_name n c
        | (stackLang_StackStoreAny n n0) -> reg_name n c /\ reg_name
          n0 c
        | (stackLang_StackLoad n n0) -> reg_name n c
        | (stackLang_StackLoadAny n n0) -> reg_name n c /\ reg_name
          n0 c
        | (stackLang_StackGetSize n) -> reg_name n c
        | (stackLang_StackSetSize n) -> reg_name n c
        | (stackLang_BitmapLoad n n0) -> reg_name n c /\ reg_name n0
          c
        | (StoreConsts n n0 _30) -> reg_name n c /\ reg_name n0 c
        | (Seq p1 p2) -> stack_asm_remove c p1 /\ stack_asm_remove c
          p2
        | (If cmp n r p p') -> stack_asm_remove c p /\
          stack_asm_remove c p'
        | (Loop p) -> stack_asm_remove c p
        | (Call r tar h) ->
       (match r with SOME (p,_31,_32,_33) -> stack_asm_remove c p /\
         (match h with
         SOME (p',_34,_35) -> stack_asm_remove c p' | _36 -> T) | _37
           -> T)
        | _38 -> T`;;

(* Various syntactic properties required for correctness of the stackLang passes
  All of these are trivially preserved from word_to_stack until the pass that
  they are used.
*)

(* stack_alloc requires that Allocs have a fixed argument
   TODO: this can also be a semantic check...
*)

let alloc_arg_def = cake_define
  `alloc_arg x1 =
        match x1 with
          stackLang_Alloc v -> (v = 1)
        | ((Seq p1 p2):'a stackLang_prog) ->
        alloc_arg p1 /\ alloc_arg p2
        | ((If c r ri p1 p2):'a stackLang_prog) ->
        alloc_arg p1 /\ alloc_arg p2
        | (Loop p1) ->
        alloc_arg p1
        | (Call x1 _39 x2) ->
        (match x1 with SOME (y,r,_40,_41) -> alloc_arg y | NONE -> T)
          /\
        (match x2 with SOME (y,_42,_43) -> alloc_arg y | NONE -> T)
        | _44 -> T`;;

(* stack_remove requires that all register arguments are bounded by k *)

let _ = size_thms "wordLang_exp";;
(* HOL4 stackPropsScript.sml:1027-1031: the tactic that proves the
   termination *)
let reg_bound_exp_def = cake_define_wf
  `MEASURE ((wordLang_exp_size ARB) o FST)`
  `reg_bound_exp x1 k =
        match x1 with
          wordLang_Var n -> n < k
        | (Load e) -> reg_bound_exp e k
        | (Shift _45 e1 e2) -> reg_bound_exp e1 k /\ reg_bound_exp e2
          k
        | (wordLang_Lookup _46) -> F
        | (wordLang_Op _47 es) -> EVERY (\e. reg_bound_exp e k) es
        | _48 -> T`;;

let reg_bound_inst_def = cake_define
  `reg_bound_inst x1 k =
        match x1 with
          asm_Mem _49 n (Addr a _50) -> n < k /\ a < k
        | (Const n _51) -> n < k
        | (Arith (asm_Shift _52 n r2 ri)) -> r2 < k /\ n < k /\
          (match ri with Reg r -> r < k | _53 -> T)
        | (Arith (asm_Binop _54 n r2 ri)) -> r2 < k /\ n < k /\
          (match ri with Reg r1 -> r1 < k | _55 -> T)
        | (Arith (asm_Div r1 r2 r3)) -> r1 < k /\ r2 < k /\ r3 < k
        | (Arith (asm_AddCarry r1 r2 r3 r4)) -> r1 < k /\ r2 < k /\
          r3 < k /\ r4 < k
        | (Arith (asm_AddOverflow r1 r2 r3 r4)) -> r1 < k /\ r2 < k
          /\ r3 < k /\ r4 < k
        | (Arith (asm_SubOverflow r1 r2 r3 r4)) -> r1 < k /\ r2 < k
          /\ r3 < k /\ r4 < k
        | (Arith (asm_LongMul r1 r2 r3 r4)) -> r1 < k /\ r2 < k /\ r3
          < k /\ r4 < k
        | (Arith (asm_LongDiv r1 r2 r3 r4 r5)) -> r1 < k /\ r2 < k /\
          r3 < k /\ r4 < k /\ r5 < k
        | (asm_FP (FPLess r f1 f2)) -> r < k
        | (asm_FP (FPLessEqual r f1 f2)) -> r < k
        | (asm_FP (FPEqual r f1 f2)) -> r < k
        | (asm_FP (FPMovToReg r1 r2 d)) -> r1 < k /\ r2 < k
        | (asm_FP (FPMovFromReg d r1 r2)) -> r1 < k /\ r2 < k
        | _56 -> T`;;

let reg_bound_def = cake_define
  `reg_bound x1 k =
        match x1 with
          stackLang_Halt v1 ->
        v1 < k
        | (Raise v1) ->
        v1 < k
        | (Get v1 n) ->
        v1 < k
        | (OpCurrHeap op v1 v2) ->
        v1 < k /\ v2 < k
        | (Set n v1) ->
        v1 < k /\ ~(n = BitmapBase)
        | (LocValue v1 l1 l2) ->
        v1 < k
        | (StoreConsts t1 t2 _57) ->
        3 < k /\ t1 < k /\ t2 < k
        | (Return v1) ->
        v1 < k
        | (stackLang_JumpLower v1 v2 dest) ->
        v1 < k /\ v2 < k
        | ((Seq p1 p2):'a stackLang_prog) ->
        reg_bound p1 k /\ reg_bound p2 k
        | ((If c r ri p1 p2):'a stackLang_prog) ->
        r < k /\ (match ri with Reg n -> n < k | _58 -> T) /\
        reg_bound p1 k /\ reg_bound p2 k
        | (Loop p1) ->
        reg_bound p1 k
        | (Halt n) -> n < k
        | (FFI ffi_index ptr' len' ptr2' len2' ret') ->
        ptr' < k /\ len' < k /\ ptr2' < k /\ len2' < k /\ ret' < k
        | (Call x1 dest x2) ->
        (match dest with INR i -> i < k | _59 -> T) /\
        (match x1 with NONE -> T | SOME (y,r,_60,_61) -> reg_bound y
          k /\ r < k /\
                             (match x2 with SOME (y,_62,_63) ->
                               reg_bound y k | NONE -> T))
        | (Install ptr len dptr dlen ret) ->
       ptr < k /\ len < k /\ dptr < k /\ dlen < k /\ ret < k
        | (stackLang_ShMemOp op r (Addr a _64)) -> r < k /\ a < k
        | (CodeBufferWrite r1 r2) ->
       r1 < k /\ r2 < k
        | (DataBufferWrite r1 r2) ->
       r1 < k /\ r2 < k
        | (stackLang_BitmapLoad r v) -> r < k /\ v < k
        | (Inst i) -> reg_bound_inst i k
        | (stackLang_StackStore r _65) -> r < k
        | (stackLang_StackSetSize r) -> r < k
        | (stackLang_StackGetSize r) -> r < k
        | (stackLang_StackLoad r n) -> r < k
        | (stackLang_StackLoadAny r r2) -> r < k /\ r2 < k
        | (stackLang_StackStore r n) -> r < k
        | (stackLang_StackStoreAny r r2) -> r < k /\ r2 < k
        | _66 -> T`;;

(* Finally, stack_to_lab requires correct arguments for Call/FFI/Install calls *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let call_args_def = cake_define_cheat CHEAT_TAC
  `call_args x1 ptr len ptr2 len2 ret =
        match x1 with
          ((Seq p1 p2):'a stackLang_prog) ->
        call_args p1 ptr len ptr2 len2 ret /\
        call_args p2 ptr len ptr2 len2 ret
        | ((If c r ri p1 p2):'a stackLang_prog) ->
        call_args p1 ptr len ptr2 len2 ret /\
        call_args p2 ptr len ptr2 len2 ret
        | (Loop p1) ->
        call_args p1 ptr len ptr2 len2 ret
        | (Halt n) -> (n = ptr)
        | (FFI ffi_index ptr' len' ptr2' len2' ret') ->
        ptr' = ptr /\ len' = len /\ ptr2' = ptr2 /\ len2' = len2 /\
          ret' = ret
        | (Call x1 _67 x2) ->
        (match x1 with NONE -> T | SOME (y,r,_68,_69) ->
             call_args y ptr len ptr2 len2 ret /\ r = ret /\
             (match x2 with SOME (y,_70,_71) -> call_args y ptr len
               ptr2 len2 ret | NONE -> T))
        | (Install ptr' len' _72 _73 ret') ->
        ptr' = ptr /\ len' = len /\ ret' = ret
        | _74 -> T`;;

(* TODO: remove "stack_" prefix from these functions *)

let stack_get_handler_labels_def = cake_define
  `stack_get_handler_labels n x2 =
        match x2 with
          stackLang_Call r d h ->
       (match r with SOME (x,_75,_76) -> stack_get_handler_labels n x
         UNION
         (match h with SOME (x,l1,l2) -> (if l1 = n then {(l1,l2)}
           else {}) UNION (stack_get_handler_labels n x) | _77 -> {}) |
           _78 -> {})
        | (Seq p1 p2) -> stack_get_handler_labels n p1 UNION
          stack_get_handler_labels n p2
        | (If _79 _80 _81 p1 p2) -> stack_get_handler_labels n p1
          UNION stack_get_handler_labels n p2
        | (Loop p) -> stack_get_handler_labels n p
        | _82 -> {}`;;

let stackProps_get_code_labels_def = cake_define
  `stackProps_get_code_labels x1 =
        match x1 with
          stackLang_Call r d h ->
       (match d with INL x -> {(x,0)} | _83 -> {}) UNION
       (match r with SOME (x,_84,_85) -> stackProps_get_code_labels x
         | _86 -> {}) UNION
       (match h with SOME (x,_87,_88) -> stackProps_get_code_labels x
         | _89 -> {})
        | (Seq p1 p2) -> stackProps_get_code_labels p1 UNION
          stackProps_get_code_labels p2
        | (If _90 _91 _92 p1 p2) -> stackProps_get_code_labels p1
          UNION stackProps_get_code_labels p2
        | (Loop p) -> stackProps_get_code_labels p
        | (stackLang_JumpLower _93 _94 t) -> {(t,0)}
        | (stackLang_RawCall t) -> {(t,1)}
        | (LocValue _95 l1 l2) -> {(l1,l2)}
        | (StoreConsts _96 _97 (SOME l)) -> {(l,0)}
        | _98 -> {}`;;
hol4_overload "get_code_labels" "stackProps_get_code_labels";;

(* elabs gives a set of existing code labels *)
let stack_good_code_labels_def = cake_define
  `stack_good_code_labels p elabs <=>
   BIGUNION (IMAGE stackProps_get_code_labels (set_of_list (MAP SND
     p))) SUBSET
   BIGUNION (set_of_list (MAP (\(n,pp). stack_get_handler_labels n
     pp) p)) UNION
   IMAGE (\n. n,0) (set_of_list (MAP FST p)) UNION IMAGE (\n. n,0)
     elabs UNION
   IMAGE (\n. n,1) (set_of_list (MAP FST p)) UNION IMAGE (\n. n,1)
     elabs`;;

let stack_good_handler_labels_def = cake_define
  `stack_good_handler_labels p <=>
   restrict_nonzero (BIGUNION (IMAGE stackProps_get_code_labels
     (set_of_list (MAP SND p)))) SUBSET
   BIGUNION (set_of_list (MAP (\(n,pp). stack_get_handler_labels n
     pp) p)) UNION
   IMAGE (\n. n,1) (set_of_list (MAP FST p))`;;

let stackProps_no_install_def = cake_define
  `stackProps_no_install x1 =
        match x1 with
          stackLang_Call r d h ->
       ((match r with SOME (x,_99,_100) -> stackProps_no_install x |
         _101 -> T) /\
        (match h with SOME (x,_102,_103) -> stackProps_no_install x |
          _104 -> T))
        | (Seq p1 p2) -> (stackProps_no_install p1 /\
          stackProps_no_install p2)
        | (If _105 _106 _107 p1 p2) -> (stackProps_no_install p1 /\
          stackProps_no_install p2)
        | (Loop p) -> stackProps_no_install p
        | (Install _108 _109 _110 _111 _112) -> F
        | _113 -> T`;;
hol4_overload "no_install" "stackProps_no_install";;

let no_shmemop_def = cake_define
  `no_shmemop x1 =
        match x1 with
          stackLang_Call r d h ->
       ((match r with SOME (x,_114,_115) -> no_shmemop x | _116 -> T)
         /\
        (match h with SOME (x,_117,_118) -> no_shmemop x | _119 ->
          T))
        | (Seq p1 p2) -> (no_shmemop p1 /\ no_shmemop p2)
        | (If _120 _121 _122 p1 p2) -> (no_shmemop p1 /\ no_shmemop
          p2)
        | (Loop p) -> no_shmemop p
        | (stackLang_ShMemOp _123 _124 _125) -> F
        | _126 -> T`;;

(* and the accessors of those fields are overloaded again *)
let _ = unhide_overloads ();;
