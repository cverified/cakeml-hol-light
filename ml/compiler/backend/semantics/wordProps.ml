(* ======================================================== *)
(*  wordProps: ported from HOL4's
    compiler/backend/semantics/wordPropsScript.sml
    A proof theory, with 10 definitions and 197 theorems.  Needed by
    17 files of the port.  *)
(* ======================================================== *)

(*
  Properties about wordLang and its semantics
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "wordProps"
  ["asm"; "backendProps"; "mllist"; "reg_alloc"; "wordConvs";
   "wordLang"; "wordSem"];;

let _ = do_list hide_constant ["Term"; "comp"; "precondition"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["code_buffer","code_buffer";
   "compile","backend_compile";
   "compile","bvi_let_compile";
   "compile","bvi_to_data_compile";
   "compile","bvl_const_compile";
   "compile","bvl_handle_compile";
   "compile","bvl_to_bvi_compile";
   "compile","clos_annotate_compile";
   "compile","clos_call_compile";
   "compile","clos_fvs_compile";
   "compile","clos_known_compile";
   "compile","clos_mti_compile";
   "compile","clos_to_bvl_compile";
   "compile","compiler_compile";
   "compile","data_live_compile";
   "compile","data_space_compile";
   "compile","data_to_word_compile";
   "compile","flat_to_clos_compile";
   "compile","lab_to_target_compile";
   "compile","source_to_flat_compile";
   "compile","source_to_source_compile";
   "compile","stack_alloc_compile";
   "compile","stack_names_compile";
   "compile","stack_rawcall_compile";
   "compile","stack_remove_compile";
   "compile","stack_to_lab_compile";
   "compile","word_bignum_compile";
   "compile","word_to_stack_compile";
   "compile","word_to_word_compile";
   "data_buffer","data_buffer"];;

(* HOL4 wordPropsScript.sml:10: an overload that the source brings to
   the front: Set, written out as wordLang_Set *)

(*
Main lemmas:
0) Clock lemmas (add_clock, dec_clock, IO monotonicity)
1) Code table constancy across eval
2) Swapping stack for one with identical values (but different keys)
3) Thms to handle the permutation oracle
4) Effect of extra locals (locals_rel)
*)

(*TODO remove *)

(*TODO move*)
let domain_fromAList_toAList = prove
 (`domain (fromAList (toAList l)) = domain l`,
  CHEAT_TAC);;

(* TODO: move *)
let mem_list_rearrange = prove
 (`!ls x f. MEM x (list_rearrange f ls) <=> MEM x ls`,
  CHEAT_TAC);;

(* HOL4 wordPropsScript.sml:43-45: ML code, not ported *)

(* HOL4 wordPropsScript.sml:47-49: the ML values that the definitions
   below antiquote *)

let PERM_list_rearrange = prove
 (`!f xs. ALL_DISTINCT xs ==> PERM xs (list_rearrange f xs)`,
  CHEAT_TAC);;

let PERM_ALL_DISTINCT_MAP = prove
 (`!xs ys. PERM xs ys ==>
            ALL_DISTINCT (MAP f xs) ==>
            ALL_DISTINCT (MAP f ys) /\ (!x. MEM x ys <=> MEM x xs)`,
  CHEAT_TAC);;

let ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME = prove
 (`ALL_DISTINCT (MAP FST xs) /\ MEM (x,y) xs ==> ALOOKUP xs x = SOME y`,
  CHEAT_TAC);;

(* -- *)
(*drulel takes a list and tries to apply drule
*)
(* HOL4 wordPropsScript.sml:85: ML code, not ported *)
(* HOL4 wordPropsScript.sml:86: code that the source has in a comment *)
(* HOL4 wordPropsScript.sml:87: ML code, not ported *)
(* Clock lemmas *)

(* HOL4 wordPropsScript.sml:90-96: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

(*helps with existence proofs
?l'. (s with locals := l) = (s with locals := l')*)
(*TODO does not work when given a goal like
?k'. (s with <|locals := l; clock := k|>) = (s with <|locals := l, clock := k |>)
*)
let state_const = prove
 (`((wordSem_state_locals_fupd (K l) s) = (wordSem_state_locals_fupd (K
  l') s) <=> l = l') /\
   ((wordSem_state_permute_fupd (K p) s) =
     (wordSem_state_permute_fupd (K p') s) <=> p = p') /\
   ((wordSem_state_clock_fupd (K clk) s) = (wordSem_state_clock_fupd
     (K clk') s) <=> clk = clk') /\
   ((wordSem_state_stack_fupd (K xs) s) = (wordSem_state_stack_fupd
     (K xs') s) <=> xs = xs')`,
  CHEAT_TAC);;
add_simp state_const;;

let PAIR_MAP_EQ_PAIR = prove
 (`(f ## g) p = (a,b) <=> (?x y. p = (x,y) /\ f x = a /\ g y = b)`,
  CHEAT_TAC);;
add_simp PAIR_MAP_EQ_PAIR;;

(*TODO Weaken this simplification
What that is needed to be pulled down is when
f is a record update like (λs. s with clock := k)
*)
(* OPTION_CASE_OPTION_MAP *)
let wordProps_OPTION_CASE_OPTION_MAP = prove
 (`(option_CASE (OPTION_MAP f a) e g) = option_CASE a e (\x. g (f x))`,
  CHEAT_TAC);;
add_simp wordProps_OPTION_CASE_OPTION_MAP;;

(*USEFUL to clean up proofs with the previous lemma*)
let OPTION_CASE_MAP = prove
 (`option_CASE x NONE (\x. SOME (f x)) = OPTION_MAP f x`,
  CHEAT_TAC);;

(******CONST LEMMAS *****)
let get_var_with_const = prove
 (`wordSem_get_var x (wordSem_state_locals_size_fupd (K ls) y) =
  wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_fp_regs_fupd (K fp) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_store_fupd (K store) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (stack_fupd (K xs) y) = wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_stack_limit_fupd (K sl) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_stack_max_fupd (K sm) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_stack_size_fupd (K ssize) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_memory_fupd (K m) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_mdomain_fupd (K md) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_sh_mdomain_fupd (K smd) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_permute_fupd (K p) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_compile_fupd (K c) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_compile_oracle_fupd (K co) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_code_buffer_fupd (K cb) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_data_buffer_fupd (K db) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_gc_fun_fupd (K g) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_handler_fupd (K hd) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (state_clock_fupd (K clk) y) = wordSem_get_var x
     y /\
   wordSem_get_var x (wordSem_state_termdep_fupd (K tdep) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_code_fupd (K cd) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (wordSem_state_be_fupd (K b) y) =
     wordSem_get_var x y /\
   wordSem_get_var x (state_ffi_fupd (K ffi) y) = wordSem_get_var x
     y`,
  CHEAT_TAC);;
add_simp get_var_with_const;;

let get_vars_with_const = prove
 (`wordSem_get_vars x (wordSem_state_locals_size_fupd (K ls) y) =
  wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_fp_regs_fupd (K fp) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_store_fupd (K store) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (stack_fupd (K xs) y) = wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_stack_limit_fupd (K sl) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_stack_max_fupd (K sm) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_stack_size_fupd (K ssize) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_memory_fupd (K m) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_mdomain_fupd (K md) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_sh_mdomain_fupd (K smd) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_permute_fupd (K p) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_compile_fupd (K c) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_compile_oracle_fupd (K co) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_code_buffer_fupd (K cb) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_data_buffer_fupd (K db) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_gc_fun_fupd (K g) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_handler_fupd (K hd) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (state_clock_fupd (K clk) y) = wordSem_get_vars
     x y /\
   wordSem_get_vars x (wordSem_state_termdep_fupd (K tdep) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_code_fupd (K cd) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (wordSem_state_be_fupd (K b) y) =
     wordSem_get_vars x y /\
   wordSem_get_vars x (state_ffi_fupd (K ffi) y) = wordSem_get_vars
     x y`,
  CHEAT_TAC);;
add_simp get_vars_with_const;;

(* set_var_const *)
let wordProps_set_var_const = prove
 (`wordSem_state_locals_size
      (wordSem_set_var x y z) = wordSem_state_locals_size z /\
        wordSem_state_fp_regs
      (wordSem_set_var x y z) = wordSem_state_fp_regs z /\
        wordSem_state_store
      (wordSem_set_var x y z) = wordSem_state_store z /\ stack
      (wordSem_set_var x y z) = stack z /\ wordSem_state_stack_limit
      (wordSem_set_var x y z) = wordSem_state_stack_limit z /\
        wordSem_state_stack_max
      (wordSem_set_var x y z) = wordSem_state_stack_max z /\
        wordSem_state_stack_size
      (wordSem_set_var x y z) = wordSem_state_stack_size z /\
        wordSem_state_memory
      (wordSem_set_var x y z) = wordSem_state_memory z /\
        wordSem_state_mdomain
      (wordSem_set_var x y z) = wordSem_state_mdomain z /\
        wordSem_state_sh_mdomain
      (wordSem_set_var x y z) = wordSem_state_sh_mdomain z /\
        wordSem_state_permute
      (wordSem_set_var x y z) = wordSem_state_permute z /\
        wordSem_state_compile
      (wordSem_set_var x y z) = wordSem_state_compile z /\
        wordSem_state_compile_oracle
      (wordSem_set_var x y z) = wordSem_state_compile_oracle z /\
        wordSem_state_code_buffer
      (wordSem_set_var x y z) = wordSem_state_code_buffer z /\
        wordSem_state_data_buffer
      (wordSem_set_var x y z) = wordSem_state_data_buffer z /\
        wordSem_state_gc_fun
      (wordSem_set_var x y z) = wordSem_state_gc_fun z /\
        wordSem_state_handler
      (wordSem_set_var x y z) = wordSem_state_handler z /\
        state_clock
      (wordSem_set_var x y z) = state_clock z /\
        wordSem_state_termdep
      (wordSem_set_var x y z) = wordSem_state_termdep z /\
        wordSem_state_code
      (wordSem_set_var x y z) = wordSem_state_code z /\
        wordSem_state_be
      (wordSem_set_var x y z) = wordSem_state_be z /\ state_ffi
      (wordSem_set_var x y z) = state_ffi z`,
  CHEAT_TAC);;
add_simp wordProps_set_var_const;;

(* set_var_with_const *)
let wordProps_set_var_with_const = prove
 (`wordSem_set_var x y (wordSem_state_locals_size_fupd (K ls) z) =
  wordSem_state_locals_size_fupd (K ls) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_fp_regs_fupd (K fp) z) =
     wordSem_state_fp_regs_fupd (K fp) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_store_fupd (K store) z) =
     wordSem_state_store_fupd (K store) (wordSem_set_var x y z) /\
   wordSem_set_var x y (stack_fupd (K xs) z) = stack_fupd (K xs)
     (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_stack_limit_fupd (K sl) z) =
     wordSem_state_stack_limit_fupd (K sl) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_stack_max_fupd (K sm) z) =
     wordSem_state_stack_max_fupd (K sm) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_stack_size_fupd (K ssize) z) =
     wordSem_state_stack_size_fupd (K ssize) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_memory_fupd (K m) z) =
     wordSem_state_memory_fupd (K m) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_mdomain_fupd (K md) z) =
     wordSem_state_mdomain_fupd (K md) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_sh_mdomain_fupd (K smd) z) =
     wordSem_state_sh_mdomain_fupd (K smd) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_permute_fupd (K p) z) =
     wordSem_state_permute_fupd (K p) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_compile_fupd (K c) z) =
     wordSem_state_compile_fupd (K c) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_compile_oracle_fupd (K co) z) =
     wordSem_state_compile_oracle_fupd (K co) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_code_buffer_fupd (K cb) z) =
     wordSem_state_code_buffer_fupd (K cb) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_data_buffer_fupd (K db) z) =
     wordSem_state_data_buffer_fupd (K db) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_gc_fun_fupd (K g) z) =
     wordSem_state_gc_fun_fupd (K g) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_handler_fupd (K hd) z) =
     wordSem_state_handler_fupd (K hd) (wordSem_set_var x y z) /\
   wordSem_set_var x y (state_clock_fupd (K clk) z) =
     state_clock_fupd (K clk) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_termdep_fupd (K tdep) z) =
     wordSem_state_termdep_fupd (K tdep) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_code_fupd (K cd) z) =
     wordSem_state_code_fupd (K cd) (wordSem_set_var x y z) /\
   wordSem_set_var x y (wordSem_state_be_fupd (K b) z) =
     wordSem_state_be_fupd (K b) (wordSem_set_var x y z) /\
   wordSem_set_var x y (state_ffi_fupd (K ffi) z) = state_ffi_fupd
     (K ffi) (wordSem_set_var x y z)`,
  CHEAT_TAC);;
add_simp wordProps_set_var_with_const;;

let unset_var_const = prove
 (`wordSem_state_locals_size
      (wordSem_unset_var x z) = wordSem_state_locals_size z /\
        wordSem_state_fp_regs
      (wordSem_unset_var x z) = wordSem_state_fp_regs z /\
        wordSem_state_store
      (wordSem_unset_var x z) = wordSem_state_store z /\ stack
      (wordSem_unset_var x z) = stack z /\ wordSem_state_stack_limit
      (wordSem_unset_var x z) = wordSem_state_stack_limit z /\
        wordSem_state_stack_max
      (wordSem_unset_var x z) = wordSem_state_stack_max z /\
        wordSem_state_stack_size
      (wordSem_unset_var x z) = wordSem_state_stack_size z /\
        wordSem_state_memory
      (wordSem_unset_var x z) = wordSem_state_memory z /\
        wordSem_state_mdomain
      (wordSem_unset_var x z) = wordSem_state_mdomain z /\
        wordSem_state_sh_mdomain
      (wordSem_unset_var x z) = wordSem_state_sh_mdomain z /\
        wordSem_state_permute
      (wordSem_unset_var x z) = wordSem_state_permute z /\
        wordSem_state_compile
      (wordSem_unset_var x z) = wordSem_state_compile z /\
        wordSem_state_compile_oracle
      (wordSem_unset_var x z) = wordSem_state_compile_oracle z /\
        wordSem_state_code_buffer
      (wordSem_unset_var x z) = wordSem_state_code_buffer z /\
        wordSem_state_data_buffer
      (wordSem_unset_var x z) = wordSem_state_data_buffer z /\
        wordSem_state_gc_fun
      (wordSem_unset_var x z) = wordSem_state_gc_fun z /\
        wordSem_state_handler
      (wordSem_unset_var x z) = wordSem_state_handler z /\
        state_clock
      (wordSem_unset_var x z) = state_clock z /\
        wordSem_state_termdep
      (wordSem_unset_var x z) = wordSem_state_termdep z /\
        wordSem_state_code
      (wordSem_unset_var x z) = wordSem_state_code z /\
        wordSem_state_be
      (wordSem_unset_var x z) = wordSem_state_be z /\ state_ffi
      (wordSem_unset_var x z) = state_ffi z`,
  CHEAT_TAC);;
add_simp unset_var_const;;

let unset_var_with_const = prove
 (`wordSem_unset_var x (wordSem_state_locals_size_fupd (K ls) z) =
  wordSem_state_locals_size_fupd (K ls) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_fp_regs_fupd (K fp) z) =
     wordSem_state_fp_regs_fupd (K fp) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_store_fupd (K store) z) =
     wordSem_state_store_fupd (K store) (wordSem_unset_var x z) /\
   wordSem_unset_var x (stack_fupd (K xs) z) = stack_fupd (K xs)
     (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_stack_limit_fupd (K sl) z) =
     wordSem_state_stack_limit_fupd (K sl) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_stack_max_fupd (K sm) z) =
     wordSem_state_stack_max_fupd (K sm) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_stack_size_fupd (K ssize) z) =
     wordSem_state_stack_size_fupd (K ssize) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_memory_fupd (K m) z) =
     wordSem_state_memory_fupd (K m) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_mdomain_fupd (K md) z) =
     wordSem_state_mdomain_fupd (K md) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_sh_mdomain_fupd (K smd) z) =
     wordSem_state_sh_mdomain_fupd (K smd) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_permute_fupd (K p) z) =
     wordSem_state_permute_fupd (K p) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_compile_fupd (K c) z) =
     wordSem_state_compile_fupd (K c) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_compile_oracle_fupd (K co) z) =
     wordSem_state_compile_oracle_fupd (K co) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_code_buffer_fupd (K cb) z) =
     wordSem_state_code_buffer_fupd (K cb) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_data_buffer_fupd (K db) z) =
     wordSem_state_data_buffer_fupd (K db) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_gc_fun_fupd (K g) z) =
     wordSem_state_gc_fun_fupd (K g) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_handler_fupd (K hd) z) =
     wordSem_state_handler_fupd (K hd) (wordSem_unset_var x z) /\
   wordSem_unset_var x (state_clock_fupd (K clk) z) =
     state_clock_fupd (K clk) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_termdep_fupd (K tdep) z) =
     wordSem_state_termdep_fupd (K tdep) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_code_fupd (K cd) z) =
     wordSem_state_code_fupd (K cd) (wordSem_unset_var x z) /\
   wordSem_unset_var x (wordSem_state_be_fupd (K b) z) =
     wordSem_state_be_fupd (K b) (wordSem_unset_var x z) /\
   wordSem_unset_var x (state_ffi_fupd (K ffi) z) = state_ffi_fupd
     (K ffi) (wordSem_unset_var x z)`,
  CHEAT_TAC);;
add_simp unset_var_with_const;;

(* set_vars_const *)
let wordProps_set_vars_const = prove
 (`wordSem_state_locals_size
      (wordSem_set_vars x y z) = wordSem_state_locals_size z /\
        wordSem_state_fp_regs
      (wordSem_set_vars x y z) = wordSem_state_fp_regs z /\
        wordSem_state_store
      (wordSem_set_vars x y z) = wordSem_state_store z /\ stack
      (wordSem_set_vars x y z) = stack z /\ wordSem_state_stack_limit
      (wordSem_set_vars x y z) = wordSem_state_stack_limit z /\
        wordSem_state_stack_max
      (wordSem_set_vars x y z) = wordSem_state_stack_max z /\
        wordSem_state_stack_size
      (wordSem_set_vars x y z) = wordSem_state_stack_size z /\
        wordSem_state_memory
      (wordSem_set_vars x y z) = wordSem_state_memory z /\
        wordSem_state_mdomain
      (wordSem_set_vars x y z) = wordSem_state_mdomain z /\
        wordSem_state_sh_mdomain
      (wordSem_set_vars x y z) = wordSem_state_sh_mdomain z /\
        wordSem_state_permute
      (wordSem_set_vars x y z) = wordSem_state_permute z /\
        wordSem_state_compile
      (wordSem_set_vars x y z) = wordSem_state_compile z /\
        wordSem_state_compile_oracle
      (wordSem_set_vars x y z) = wordSem_state_compile_oracle z /\
        wordSem_state_code_buffer
      (wordSem_set_vars x y z) = wordSem_state_code_buffer z /\
        wordSem_state_data_buffer
      (wordSem_set_vars x y z) = wordSem_state_data_buffer z /\
        wordSem_state_gc_fun
      (wordSem_set_vars x y z) = wordSem_state_gc_fun z /\
        wordSem_state_handler
      (wordSem_set_vars x y z) = wordSem_state_handler z /\
        state_clock
      (wordSem_set_vars x y z) = state_clock z /\
        wordSem_state_termdep
      (wordSem_set_vars x y z) = wordSem_state_termdep z /\
        wordSem_state_code
      (wordSem_set_vars x y z) = wordSem_state_code z /\
        wordSem_state_be
      (wordSem_set_vars x y z) = wordSem_state_be z /\ state_ffi
      (wordSem_set_vars x y z) = state_ffi z`,
  CHEAT_TAC);;
add_simp wordProps_set_vars_const;;

(* set_vars_with_const *)
let wordProps_set_vars_with_const = prove
 (`wordSem_set_vars x y (wordSem_state_locals_size_fupd (K ls) z) =
  wordSem_state_locals_size_fupd (K ls) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_fp_regs_fupd (K fp) z) =
     wordSem_state_fp_regs_fupd (K fp) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_store_fupd (K store) z) =
     wordSem_state_store_fupd (K store) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (stack_fupd (K xs) z) = stack_fupd (K xs)
     (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_stack_limit_fupd (K sl) z) =
     wordSem_state_stack_limit_fupd (K sl) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_stack_max_fupd (K sm) z) =
     wordSem_state_stack_max_fupd (K sm) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_stack_size_fupd (K ssize) z) =
     wordSem_state_stack_size_fupd (K ssize) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_memory_fupd (K m) z) =
     wordSem_state_memory_fupd (K m) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_mdomain_fupd (K md) z) =
     wordSem_state_mdomain_fupd (K md) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_sh_mdomain_fupd (K smd) z) =
     wordSem_state_sh_mdomain_fupd (K smd) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_permute_fupd (K p) z) =
     wordSem_state_permute_fupd (K p) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_compile_fupd (K c) z) =
     wordSem_state_compile_fupd (K c) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_compile_oracle_fupd (K co) z)
     = wordSem_state_compile_oracle_fupd (K co) (wordSem_set_vars x y z)
     /\
   wordSem_set_vars x y (wordSem_state_code_buffer_fupd (K cb) z) =
     wordSem_state_code_buffer_fupd (K cb) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_data_buffer_fupd (K db) z) =
     wordSem_state_data_buffer_fupd (K db) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_gc_fun_fupd (K g) z) =
     wordSem_state_gc_fun_fupd (K g) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_handler_fupd (K hd) z) =
     wordSem_state_handler_fupd (K hd) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (state_clock_fupd (K clk) z) =
     state_clock_fupd (K clk) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_termdep_fupd (K tdep) z) =
     wordSem_state_termdep_fupd (K tdep) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_code_fupd (K cd) z) =
     wordSem_state_code_fupd (K cd) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (wordSem_state_be_fupd (K b) z) =
     wordSem_state_be_fupd (K b) (wordSem_set_vars x y z) /\
   wordSem_set_vars x y (state_ffi_fupd (K ffi) z) = state_ffi_fupd
     (K ffi) (wordSem_set_vars x y z)`,
  CHEAT_TAC);;
add_simp wordProps_set_vars_with_const;;

let get_store_with_const = prove
 (`wordSem_get_store x (wordSem_state_locals_fupd (K l) y) =
  wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_locals_size_fupd (K ls) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_fp_regs_fupd (K fp) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (stack_fupd (K xs) y) = wordSem_get_store x y
     /\
   wordSem_get_store x (wordSem_state_stack_limit_fupd (K sl) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_stack_max_fupd (K sm) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_stack_size_fupd (K ssize) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_memory_fupd (K m) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_mdomain_fupd (K md) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_sh_mdomain_fupd (K smd) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_permute_fupd (K p) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_compile_fupd (K c) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_compile_oracle_fupd (K co) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_code_buffer_fupd (K cb) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_data_buffer_fupd (K db) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_gc_fun_fupd (K g) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_handler_fupd (K hd) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (state_clock_fupd (K clk) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_termdep_fupd (K tdep) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_code_fupd (K cd) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (wordSem_state_be_fupd (K b) y) =
     wordSem_get_store x y /\
   wordSem_get_store x (state_ffi_fupd (K ffi) y) =
     wordSem_get_store x y`,
  CHEAT_TAC);;
add_simp get_store_with_const;;

let set_store_const = prove
 (`wordSem_state_locals
      (wordSem_set_store x y z) = wordSem_state_locals z /\
        wordSem_state_locals_size
      (wordSem_set_store x y z) = wordSem_state_locals_size z /\
        wordSem_state_fp_regs
      (wordSem_set_store x y z) = wordSem_state_fp_regs z /\ stack
      (wordSem_set_store x y z) = stack z /\
        wordSem_state_stack_limit
      (wordSem_set_store x y z) = wordSem_state_stack_limit z /\
        wordSem_state_stack_max
      (wordSem_set_store x y z) = wordSem_state_stack_max z /\
        wordSem_state_stack_size
      (wordSem_set_store x y z) = wordSem_state_stack_size z /\
        wordSem_state_memory
      (wordSem_set_store x y z) = wordSem_state_memory z /\
        wordSem_state_mdomain
      (wordSem_set_store x y z) = wordSem_state_mdomain z /\
        wordSem_state_sh_mdomain
      (wordSem_set_store x y z) = wordSem_state_sh_mdomain z /\
        wordSem_state_permute
      (wordSem_set_store x y z) = wordSem_state_permute z /\
        wordSem_state_compile
      (wordSem_set_store x y z) = wordSem_state_compile z /\
        wordSem_state_compile_oracle
      (wordSem_set_store x y z) = wordSem_state_compile_oracle z /\
        wordSem_state_code_buffer
      (wordSem_set_store x y z) = wordSem_state_code_buffer z /\
        wordSem_state_data_buffer
      (wordSem_set_store x y z) = wordSem_state_data_buffer z /\
        wordSem_state_gc_fun
      (wordSem_set_store x y z) = wordSem_state_gc_fun z /\
        wordSem_state_handler
      (wordSem_set_store x y z) = wordSem_state_handler z /\
        state_clock
      (wordSem_set_store x y z) = state_clock z /\
        wordSem_state_termdep
      (wordSem_set_store x y z) = wordSem_state_termdep z /\
        wordSem_state_code
      (wordSem_set_store x y z) = wordSem_state_code z /\
        wordSem_state_be
      (wordSem_set_store x y z) = wordSem_state_be z /\ state_ffi
      (wordSem_set_store x y z) = state_ffi z`,
  CHEAT_TAC);;
add_simp set_store_const;;

let set_store_with_const = prove
 (`wordSem_set_store x y (wordSem_state_locals_fupd (K l) z) =
  wordSem_state_locals_fupd (K l) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_locals_size_fupd (K ls) z) =
     wordSem_state_locals_size_fupd (K ls) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_fp_regs_fupd (K fp) z) =
     wordSem_state_fp_regs_fupd (K fp) (wordSem_set_store x y z) /\
   wordSem_set_store x y (stack_fupd (K xs) z) = stack_fupd (K xs)
     (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_stack_limit_fupd (K sl) z) =
     wordSem_state_stack_limit_fupd (K sl) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_stack_max_fupd (K sm) z) =
     wordSem_state_stack_max_fupd (K sm) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_stack_size_fupd (K ssize) z)
     = wordSem_state_stack_size_fupd (K ssize) (wordSem_set_store x y z)
     /\
   wordSem_set_store x y (wordSem_state_memory_fupd (K m) z) =
     wordSem_state_memory_fupd (K m) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_mdomain_fupd (K md) z) =
     wordSem_state_mdomain_fupd (K md) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_sh_mdomain_fupd (K smd) z) =
     wordSem_state_sh_mdomain_fupd (K smd) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_permute_fupd (K p) z) =
     wordSem_state_permute_fupd (K p) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_compile_fupd (K c) z) =
     wordSem_state_compile_fupd (K c) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_compile_oracle_fupd (K co) z)
     = wordSem_state_compile_oracle_fupd (K co) (wordSem_set_store x y
     z) /\
   wordSem_set_store x y (wordSem_state_code_buffer_fupd (K cb) z) =
     wordSem_state_code_buffer_fupd (K cb) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_data_buffer_fupd (K db) z) =
     wordSem_state_data_buffer_fupd (K db) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_gc_fun_fupd (K g) z) =
     wordSem_state_gc_fun_fupd (K g) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_handler_fupd (K hd) z) =
     wordSem_state_handler_fupd (K hd) (wordSem_set_store x y z) /\
   wordSem_set_store x y (state_clock_fupd (K clk) z) =
     state_clock_fupd (K clk) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_termdep_fupd (K tdep) z) =
     wordSem_state_termdep_fupd (K tdep) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_code_fupd (K cd) z) =
     wordSem_state_code_fupd (K cd) (wordSem_set_store x y z) /\
   wordSem_set_store x y (wordSem_state_be_fupd (K b) z) =
     wordSem_state_be_fupd (K b) (wordSem_set_store x y z) /\
   wordSem_set_store x y (state_ffi_fupd (K ffi) z) =
     state_ffi_fupd (K ffi) (wordSem_set_store x y z)`,
  CHEAT_TAC);;
add_simp set_store_with_const;;


(* push_env_const *)
let wordProps_push_env_const = prove
 (`state_clock
      (wordSem_push_env x y z) = state_clock z /\
        wordSem_state_memory
      (wordSem_push_env x y z) = wordSem_state_memory z /\
        wordSem_state_store
      (wordSem_push_env x y z) = wordSem_state_store z /\
        wordSem_state_handler
      (wordSem_push_env x NONE z) = wordSem_state_handler z /\
        state_ffi
      (wordSem_push_env x y z) = state_ffi z /\ wordSem_state_termdep
      (wordSem_push_env x y z) = wordSem_state_termdep z /\
        wordSem_state_data_buffer
      (wordSem_push_env x y z) = wordSem_state_data_buffer z /\
        wordSem_state_code_buffer
      (wordSem_push_env x y z) = wordSem_state_code_buffer z /\
        wordSem_state_compile
      (wordSem_push_env x y z) = wordSem_state_compile z /\
        wordSem_state_compile_oracle
      (wordSem_push_env x y z) = wordSem_state_compile_oracle z /\
        wordSem_state_mdomain
      (wordSem_push_env x y z) = wordSem_state_mdomain z /\
        wordSem_state_sh_mdomain
      (wordSem_push_env x y z) = wordSem_state_sh_mdomain z /\
        wordSem_state_gc_fun
      (wordSem_push_env x y z) = wordSem_state_gc_fun z /\
        wordSem_state_be
      (wordSem_push_env x y z) = wordSem_state_be z /\
        wordSem_state_fp_regs
      (wordSem_push_env x y z) = wordSem_state_fp_regs z /\
        wordSem_state_code
      (wordSem_push_env x y z) = wordSem_state_code z /\
        wordSem_state_stack_limit
      (wordSem_push_env x y z) = wordSem_state_stack_limit z /\
        wordSem_state_stack_size
      (wordSem_push_env x y z) = wordSem_state_stack_size z`,
  CHEAT_TAC);;
add_simp wordProps_push_env_const;;

(* push_env_with_const *)
let wordProps_push_env_with_const = prove
 (`(wordSem_push_env x y (state_clock_fupd (K k) z) = state_clock_fupd
  (K k) (wordSem_push_env x y z)) /\
   (wordSem_push_env x y (wordSem_state_compile_fupd (K c) z) =
     wordSem_state_compile_fupd (K c) (wordSem_push_env x y z)) /\
   (wordSem_push_env x y (wordSem_state_compile_oracle_fupd (K co) z)
     = wordSem_state_compile_oracle_fupd (K co) (wordSem_push_env x y
     z)) /\
   (wordSem_push_env x y (wordSem_state_code_fupd (K code) z) =
     wordSem_state_code_fupd (K code) (wordSem_push_env x y z)) /\
   (wordSem_push_env x y (wordSem_state_termdep_fupd (K termdep) z) =
     wordSem_state_termdep_fupd (K termdep) (wordSem_push_env x y z)) /\
   (wordSem_push_env x y (wordSem_state_locals_fupd (K l) z) =
     wordSem_state_locals_fupd (K l) (wordSem_push_env x y z))`,
  CHEAT_TAC);;
add_simp wordProps_push_env_with_const;;

(* pop_env_const *)
let wordProps_pop_env_const = prove
 (`wordSem_pop_env x = SOME y ==> state_clock
   y = state_clock x /\ state_ffi
   y = state_ffi x /\ wordSem_state_be
   y = wordSem_state_be x /\ wordSem_state_compile
   y = wordSem_state_compile x /\ wordSem_state_compile_oracle
   y = wordSem_state_compile_oracle x /\ wordSem_state_memory
   y = wordSem_state_memory x /\ wordSem_state_mdomain
   y = wordSem_state_mdomain x /\ wordSem_state_sh_mdomain
   y = wordSem_state_sh_mdomain x /\ wordSem_state_store
   y = wordSem_state_store x /\ wordSem_state_fp_regs
   y = wordSem_state_fp_regs x /\ wordSem_state_gc_fun
   y = wordSem_state_gc_fun x /\ wordSem_state_termdep
   y = wordSem_state_termdep x /\ wordSem_state_permute
   y = wordSem_state_permute x /\ wordSem_state_data_buffer
   y = wordSem_state_data_buffer x /\ wordSem_state_code_buffer
   y = wordSem_state_code_buffer x /\ wordSem_state_code
   y = wordSem_state_code x /\ wordSem_state_stack_limit
   y = wordSem_state_stack_limit x /\ wordSem_state_stack_max
   y = wordSem_state_stack_max x /\ wordSem_state_stack_size
   y = wordSem_state_stack_size x`,
  CHEAT_TAC);;

(* pop_env_with_const *)
let wordProps_pop_env_with_const = prove
 (`wordSem_pop_env (state_clock_fupd (K k) z) = OPTION_MAP (\s.
  wordSem_state_clock_fupd (K k) s) (wordSem_pop_env z) /\
   wordSem_pop_env (wordSem_state_compile_fupd (K c) z) = OPTION_MAP
     (\s. wordSem_state_compile_fupd (K c) s) (wordSem_pop_env z) /\
   wordSem_pop_env (wordSem_state_compile_oracle_fupd (K co) z) =
     OPTION_MAP (\s. wordSem_state_compile_oracle_fupd (K co) s)
     (wordSem_pop_env z) /\
   wordSem_pop_env (wordSem_state_code_fupd (K code) z) = OPTION_MAP
     (\s. wordSem_state_code_fupd (K code) s) (wordSem_pop_env z) /\
   wordSem_pop_env (wordSem_state_termdep_fupd (K termdep) z) =
     OPTION_MAP (\s. wordSem_state_termdep_fupd (K termdep) s)
     (wordSem_pop_env z) /\
   wordSem_pop_env (wordSem_state_permute_fupd (K perm) z) =
     OPTION_MAP (\s. wordSem_state_permute_fupd (K perm) s)
     (wordSem_pop_env z) /\
   wordSem_pop_env (wordSem_state_locals_fupd (K l) z) =
     wordSem_pop_env z /\
   wordSem_pop_env (wordSem_state_locals_size_fupd (K ls) z) =
     wordSem_pop_env z`,
  CHEAT_TAC);;
add_simp wordProps_pop_env_with_const;;

(*FIXME dupe*)
(*code and gc_fun are unchanged across eval*)
let pop_env_code_gc_fun_clock = prove
 (`wordSem_pop_env r = SOME x ==> wordSem_state_code
   r = wordSem_state_code x /\ wordSem_state_code_buffer
   r = wordSem_state_code_buffer x /\ wordSem_state_data_buffer
   r = wordSem_state_data_buffer x /\ wordSem_state_gc_fun
   r = wordSem_state_gc_fun x /\ state_clock
   r = state_clock x /\ wordSem_state_be
   r = wordSem_state_be x /\ wordSem_state_mdomain
   r = wordSem_state_mdomain x /\ wordSem_state_sh_mdomain
   r = wordSem_state_sh_mdomain x /\ wordSem_state_compile
   r = wordSem_state_compile x /\ wordSem_state_compile_oracle
   r = wordSem_state_compile_oracle x /\ wordSem_state_stack_limit
   r = wordSem_state_stack_limit x /\ wordSem_state_stack_max
   r = wordSem_state_stack_max x /\ wordSem_state_stack_size
   r = wordSem_state_stack_size x`,
  CHEAT_TAC);;

(* call_env_const *)
let wordProps_call_env_const = prove
 (`wordSem_state_store
      (wordSem_call_env x ss y) = wordSem_state_store y /\
        wordSem_state_termdep
      (wordSem_call_env x ss y) = wordSem_state_termdep y /\
        state_clock
      (wordSem_call_env x ss y) = state_clock y /\
        wordSem_state_handler
      (wordSem_call_env x ss y) = wordSem_state_handler y /\ stack
      (wordSem_call_env x ss y) = stack y /\
        wordSem_state_compile_oracle
      (wordSem_call_env x ss y) = wordSem_state_compile_oracle y /\
        wordSem_state_compile
      (wordSem_call_env x ss y) = wordSem_state_compile y /\
        wordSem_state_be
      (wordSem_call_env x ss y) = wordSem_state_be y /\
        wordSem_state_memory
      (wordSem_call_env x ss y) = wordSem_state_memory y /\
        wordSem_state_mdomain
      (wordSem_call_env x ss y) = wordSem_state_mdomain y /\
        wordSem_state_sh_mdomain
      (wordSem_call_env x ss y) = wordSem_state_sh_mdomain y /\
        wordSem_state_gc_fun
      (wordSem_call_env x ss y) = wordSem_state_gc_fun y /\ state_ffi
      (wordSem_call_env x ss y) = state_ffi y /\ wordSem_state_code
      (wordSem_call_env x ss y) = wordSem_state_code y /\
        wordSem_state_code_buffer
      (wordSem_call_env x ss y) = wordSem_state_code_buffer y /\
        wordSem_state_data_buffer
      (wordSem_call_env x ss y) = wordSem_state_data_buffer y /\
        wordSem_state_stack_limit
      (wordSem_call_env x ss y) = wordSem_state_stack_limit y /\
        wordSem_state_stack_size
      (wordSem_call_env x ss y) = wordSem_state_stack_size y`,
  CHEAT_TAC);;
add_simp wordProps_call_env_const;;

(* call_env_with_const *)
let wordProps_call_env_with_const = prove
 (`wordSem_call_env x ss (wordSem_state_locals_fupd (K l) y) =
  wordSem_call_env x ss y /\
   wordSem_call_env x ss (state_clock_fupd (K k) y) =
     state_clock_fupd (K k) (wordSem_call_env x ss y) /\
   wordSem_call_env x ss (wordSem_state_termdep_fupd (K termdep) y) =
     wordSem_state_termdep_fupd (K termdep) (wordSem_call_env x ss y) /\
   wordSem_call_env x ss (wordSem_state_compile_fupd (K c) y) =
     wordSem_state_compile_fupd (K c) (wordSem_call_env x ss y) /\
   wordSem_call_env x ss (wordSem_state_compile_oracle_fupd (K co) y)
     = wordSem_state_compile_oracle_fupd (K co) (wordSem_call_env x ss
     y) /\
   wordSem_call_env x ss (wordSem_state_code_fupd (K code) y) =
     wordSem_state_code_fupd (K code) (wordSem_call_env x ss y) /\
   wordSem_call_env x ss (wordSem_state_handler_fupd (K k) y) =
     wordSem_state_handler_fupd (K k) (wordSem_call_env x ss y) /\
   wordSem_call_env x ss (wordSem_state_permute_fupd (K perm) y) =
     wordSem_state_permute_fupd (K perm) (wordSem_call_env x ss y)`,
  CHEAT_TAC);;
add_simp wordProps_call_env_with_const;;

let flush_state_const = prove
 (`state_clock
      (wordSem_flush_state b y) = state_clock y /\
        wordSem_state_compile_oracle
      (wordSem_flush_state b y) = wordSem_state_compile_oracle y /\
        wordSem_state_compile
      (wordSem_flush_state b y) = wordSem_state_compile y /\
        wordSem_state_be
      (wordSem_flush_state b y) = wordSem_state_be y /\
        wordSem_state_gc_fun
      (wordSem_flush_state b y) = wordSem_state_gc_fun y /\ state_ffi
      (wordSem_flush_state b y) = state_ffi y /\ wordSem_state_code
      (wordSem_flush_state b y) = wordSem_state_code y /\
        wordSem_state_code_buffer
      (wordSem_flush_state b y) = wordSem_state_code_buffer y /\
        wordSem_state_data_buffer
      (wordSem_flush_state b y) = wordSem_state_data_buffer y /\
        wordSem_state_stack_limit
      (wordSem_flush_state b y) = wordSem_state_stack_limit y /\
        wordSem_state_stack_size
      (wordSem_flush_state b y) = wordSem_state_stack_size y /\ stack
      (wordSem_flush_state F y) = stack y`,
  CHEAT_TAC);;
add_simp flush_state_const;;

let flush_state_with_const = prove
 (`wordSem_flush_state b (wordSem_state_locals_fupd (K l) y) =
  wordSem_flush_state b y /\
   wordSem_flush_state b (wordSem_state_locals_size_fupd (K ls) y) =
     wordSem_flush_state b y /\
   wordSem_flush_state T (stack_fupd (K xs) y) = wordSem_flush_state
     T y /\
   wordSem_flush_state b (wordSem_state_permute_fupd (K p) y) =
     wordSem_state_permute_fupd (K p) (wordSem_flush_state b y) /\
   wordSem_flush_state b (wordSem_state_stack_max_fupd (K sm) y) =
     wordSem_state_stack_max_fupd (K sm) (wordSem_flush_state b y) /\
   wordSem_flush_state b (state_clock_fupd (K k) y) =
     state_clock_fupd (K k) (wordSem_flush_state b y)`,
  CHEAT_TAC);;
add_simp flush_state_with_const;;

let has_space_with_const = prove
 (`wordSem_has_space x (state_clock_fupd (K k) y) = wordSem_has_space x
  y /\
   wordSem_has_space x (wordSem_state_compile_fupd (K c) y) =
     wordSem_has_space x y /\
   wordSem_has_space x (wordSem_state_compile_oracle_fupd (K co) y) =
     wordSem_has_space x y /\
   wordSem_has_space x (wordSem_state_code_fupd (K code) y) =
     wordSem_has_space x y /\
   wordSem_has_space x (wordSem_state_termdep_fupd (K termdep) y) =
     wordSem_has_space x y /\
   wordSem_has_space x (wordSem_state_locals_fupd (K l) y) =
     wordSem_has_space x y /\
   wordSem_has_space x (wordSem_state_locals_size_fupd (K ls) y) =
     wordSem_has_space x y /\
   wordSem_has_space x (stack_fupd (K xs) y) = wordSem_has_space x
     y`,
  CHEAT_TAC);;
add_simp has_space_with_const;;

let gc_const = prove
 (`wordSem_gc x = SOME y ==> state_clock
   y = state_clock x /\ state_ffi
   y = state_ffi x /\ wordSem_state_code
   y = wordSem_state_code x /\ wordSem_state_be
   y = wordSem_state_be x /\ wordSem_state_code_buffer
   y = wordSem_state_code_buffer x /\ wordSem_state_data_buffer
   y = wordSem_state_data_buffer x /\ wordSem_state_compile
   y = wordSem_state_compile x /\ wordSem_state_handler
   y = wordSem_state_handler x /\ wordSem_state_compile_oracle
   y = wordSem_state_compile_oracle x /\ wordSem_state_locals_size
   y = wordSem_state_locals_size x /\ wordSem_state_stack_limit
   y = wordSem_state_stack_limit x /\ wordSem_state_stack_max
   y = wordSem_state_stack_max x /\ wordSem_state_stack_size
   y = wordSem_state_stack_size x`,
  CHEAT_TAC);;

let gc_with_const = prove
 (`wordSem_gc (state_clock_fupd (K k) x) = OPTION_MAP (\s.
  wordSem_state_clock_fupd (K k) s) (wordSem_gc x) /\
   wordSem_gc (wordSem_state_compile_fupd (K c) x) = OPTION_MAP (\s.
     wordSem_state_compile_fupd (K c) s) (wordSem_gc x) /\
   wordSem_gc (wordSem_state_compile_oracle_fupd (K co) x) =
     OPTION_MAP (\s. wordSem_state_compile_oracle_fupd (K co) s)
     (wordSem_gc x) /\
   wordSem_gc (wordSem_state_code_fupd (K code) x) = OPTION_MAP (\s.
     wordSem_state_code_fupd (K code) s) (wordSem_gc x) /\
   wordSem_gc (wordSem_state_permute_fupd (K perm) x) = OPTION_MAP
     (\s. wordSem_state_permute_fupd (K perm) s) (wordSem_gc x) /\
   wordSem_gc (wordSem_state_termdep_fupd (K t) x) = OPTION_MAP (\s.
     wordSem_state_termdep_fupd (K t) s) (wordSem_gc x) /\
   wordSem_gc (wordSem_state_locals_fupd (K l) x) = OPTION_MAP (\s.
     wordSem_state_locals_fupd (K l) s) (wordSem_gc x) /\
   wordSem_gc (wordSem_state_locals_size_fupd (K ls) x) =
     OPTION_MAP (\s. wordSem_state_locals_size_fupd (K ls) s)
     (wordSem_gc x)`,
  CHEAT_TAC);;
add_simp gc_with_const;;

let alloc_const = prove
 (`wordSem_alloc c names s = (r,s') ==> state_clock
   s' = wordSem_state_clock s /\ state_ffi
   s' = wordSem_state_ffi s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_size
   s' = wordSem_state_stack_size s`,
  CHEAT_TAC);;

(*TODO merge*)

let alloc_code_gc_fun_const = prove
 (`wordSem_alloc x names s = (res,t) ==> wordSem_state_code
   t = wordSem_state_code s /\ wordSem_state_code_buffer
   t = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   t = wordSem_state_data_buffer s /\ wordSem_state_gc_fun
   t = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   t = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   t = wordSem_state_sh_mdomain s /\ wordSem_state_be
   t = wordSem_state_be s /\ wordSem_state_compile
   t = wordSem_state_compile s /\ wordSem_state_compile_oracle
   t = wordSem_state_compile_oracle s /\ wordSem_state_stack_limit
   t = wordSem_state_stack_limit s /\ wordSem_state_stack_size
   t = wordSem_state_stack_size s`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let alloc_with_const = prove
 (cake_as_vars (fun () ->
    `wordSem_alloc c names (wordSem_state_clock_fupd (K k) s) = (I ##
  (\s. wordSem_state_clock_fupd (K k) s)) (wordSem_alloc c names s) /\
     wordSem_alloc c names (wordSem_state_termdep_fupd (K t) s) =
       (I ## (\s. wordSem_state_termdep_fupd (K t) s)) (wordSem_alloc c
       names s) /\
     wordSem_alloc c names (wordSem_state_code_fupd (K code) s) =
       (I ## (\s. wordSem_state_code_fupd (K code) s)) (wordSem_alloc c
       names s) /\
     wordSem_alloc c names (wordSem_state_compile_oracle_fupd (K
       compile_oracle) s) = (I ## (\s. wordSem_state_compile_oracle_fupd
       (K compile_oracle) s)) (wordSem_alloc c names s) /\
     wordSem_alloc c names (wordSem_state_compile_fupd (K comp)
       s) = (I ## (\s. wordSem_state_compile_fupd (K comp) s))
       (wordSem_alloc c names s)`),
  CHEAT_TAC);;
add_simp alloc_with_const;;

let get_fp_var_with_const = prove
 (`wordSem_get_fp_var x (wordSem_state_locals_fupd (K l) y) =
  wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_locals_size_fupd (K ls) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_store_fupd (K store) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (stack_fupd (K xs) y) = wordSem_get_fp_var x
     y /\
   wordSem_get_fp_var x (wordSem_state_stack_limit_fupd (K sl) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_stack_max_fupd (K sm) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_stack_size_fupd (K ssize) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_memory_fupd (K m) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_mdomain_fupd (K md) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_sh_mdomain_fupd (K smd) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_permute_fupd (K p) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_compile_fupd (K c) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_compile_oracle_fupd (K co) y)
     = wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_code_buffer_fupd (K cb) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_data_buffer_fupd (K db) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_gc_fun_fupd (K g) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_handler_fupd (K hd) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (state_clock_fupd (K clk) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_termdep_fupd (K tdep) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_code_fupd (K cd) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (wordSem_state_be_fupd (K b) y) =
     wordSem_get_fp_var x y /\
   wordSem_get_fp_var x (state_ffi_fupd (K ffi) y) =
     wordSem_get_fp_var x y`,
  CHEAT_TAC);;
add_simp get_fp_var_with_const;;

let set_fp_var_const = prove
 (`wordSem_state_locals
      (wordSem_set_fp_var x y z) = wordSem_state_locals z /\
        wordSem_state_locals_size
      (wordSem_set_fp_var x y z) = wordSem_state_locals_size z /\
        wordSem_state_store
      (wordSem_set_fp_var x y z) = wordSem_state_store z /\ stack
      (wordSem_set_fp_var x y z) = stack z /\
        wordSem_state_stack_limit
      (wordSem_set_fp_var x y z) = wordSem_state_stack_limit z /\
        wordSem_state_stack_max
      (wordSem_set_fp_var x y z) = wordSem_state_stack_max z /\
        wordSem_state_stack_size
      (wordSem_set_fp_var x y z) = wordSem_state_stack_size z /\
        wordSem_state_memory
      (wordSem_set_fp_var x y z) = wordSem_state_memory z /\
        wordSem_state_mdomain
      (wordSem_set_fp_var x y z) = wordSem_state_mdomain z /\
        wordSem_state_sh_mdomain
      (wordSem_set_fp_var x y z) = wordSem_state_sh_mdomain z /\
        wordSem_state_permute
      (wordSem_set_fp_var x y z) = wordSem_state_permute z /\
        wordSem_state_compile
      (wordSem_set_fp_var x y z) = wordSem_state_compile z /\
        wordSem_state_compile_oracle
      (wordSem_set_fp_var x y z) = wordSem_state_compile_oracle z /\
        wordSem_state_code_buffer
      (wordSem_set_fp_var x y z) = wordSem_state_code_buffer z /\
        wordSem_state_data_buffer
      (wordSem_set_fp_var x y z) = wordSem_state_data_buffer z /\
        wordSem_state_gc_fun
      (wordSem_set_fp_var x y z) = wordSem_state_gc_fun z /\
        wordSem_state_handler
      (wordSem_set_fp_var x y z) = wordSem_state_handler z /\
        state_clock
      (wordSem_set_fp_var x y z) = state_clock z /\
        wordSem_state_termdep
      (wordSem_set_fp_var x y z) = wordSem_state_termdep z /\
        wordSem_state_code
      (wordSem_set_fp_var x y z) = wordSem_state_code z /\
        wordSem_state_be
      (wordSem_set_fp_var x y z) = wordSem_state_be z /\ state_ffi
      (wordSem_set_fp_var x y z) = state_ffi z`,
  CHEAT_TAC);;
add_simp set_fp_var_const;;

let set_fp_var_with_const = prove
 (`wordSem_set_fp_var x y (wordSem_state_locals_fupd (K l) z) =
  wordSem_state_locals_fupd (K l) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_locals_size_fupd (K ls) z) =
     wordSem_state_locals_size_fupd (K ls) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_store_fupd (K store) z) =
     wordSem_state_store_fupd (K store) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (stack_fupd (K xs) z) = stack_fupd (K xs)
     (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_stack_limit_fupd (K sl) z) =
     wordSem_state_stack_limit_fupd (K sl) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_stack_max_fupd (K sm) z) =
     wordSem_state_stack_max_fupd (K sm) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_stack_size_fupd (K ssize) z)
     = wordSem_state_stack_size_fupd (K ssize) (wordSem_set_fp_var x y
     z) /\
   wordSem_set_fp_var x y (wordSem_state_memory_fupd (K m) z) =
     wordSem_state_memory_fupd (K m) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_mdomain_fupd (K md) z) =
     wordSem_state_mdomain_fupd (K md) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_sh_mdomain_fupd (K smd) z) =
     wordSem_state_sh_mdomain_fupd (K smd) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_permute_fupd (K p) z) =
     wordSem_state_permute_fupd (K p) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_compile_fupd (K c) z) =
     wordSem_state_compile_fupd (K c) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_compile_oracle_fupd (K co)
     z) = wordSem_state_compile_oracle_fupd (K co) (wordSem_set_fp_var x
     y z) /\
   wordSem_set_fp_var x y (wordSem_state_code_buffer_fupd (K cb) z) =
     wordSem_state_code_buffer_fupd (K cb) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_data_buffer_fupd (K db) z) =
     wordSem_state_data_buffer_fupd (K db) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_gc_fun_fupd (K g) z) =
     wordSem_state_gc_fun_fupd (K g) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_handler_fupd (K hd) z) =
     wordSem_state_handler_fupd (K hd) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (state_clock_fupd (K clk) z) =
     state_clock_fupd (K clk) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_termdep_fupd (K tdep) z) =
     wordSem_state_termdep_fupd (K tdep) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_code_fupd (K cd) z) =
     wordSem_state_code_fupd (K cd) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (wordSem_state_be_fupd (K b) z) =
     wordSem_state_be_fupd (K b) (wordSem_set_fp_var x y z) /\
   wordSem_set_fp_var x y (state_ffi_fupd (K ffi) z) =
     state_ffi_fupd (K ffi) (wordSem_set_fp_var x y z)`,
  CHEAT_TAC);;
add_simp set_fp_var_with_const;;

let mem_load_with_const = prove
 (`wordSem_mem_load x (wordSem_state_locals_fupd (K l) y) =
  wordSem_mem_load x y /\
   wordSem_mem_load x (wordSem_state_termdep_fupd (K td) y) =
     wordSem_mem_load x y /\
   wordSem_mem_load x (state_clock_fupd (K k) y) = wordSem_mem_load x
     y /\
   wordSem_mem_load x (stack_fupd (K xs) y) = wordSem_mem_load x y /\
   wordSem_mem_load x (wordSem_state_permute_fupd (K perm) y) =
     wordSem_mem_load x y /\
   wordSem_mem_load x (wordSem_state_code_fupd (K c) y) =
     wordSem_mem_load x y /\
   wordSem_mem_load x (wordSem_state_compile_oracle_fupd (K co) y) =
     wordSem_mem_load x y /\
   wordSem_mem_load x (wordSem_state_compile_fupd (K cc) y) =
     wordSem_mem_load x y`,
  CHEAT_TAC);;
add_simp mem_load_with_const;;

let mem_store_const = prove
 (`wordSem_mem_store x y z = SOME a ==> wordSem_state_locals
   a = wordSem_state_locals z /\ state_clock
   a = state_clock z /\ wordSem_state_be
   a = wordSem_state_be z /\ wordSem_state_gc_fun
   a = wordSem_state_gc_fun z /\ wordSem_state_mdomain
   a = wordSem_state_mdomain z /\ wordSem_state_sh_mdomain
   a = wordSem_state_sh_mdomain z /\ state_ffi
   a = state_ffi z /\ wordSem_state_handler
   a = wordSem_state_handler z /\ wordSem_state_code
   a = wordSem_state_code z /\ wordSem_state_code_buffer
   a = wordSem_state_code_buffer z /\ wordSem_state_data_buffer
   a = wordSem_state_data_buffer z /\ wordSem_state_compile
   a = wordSem_state_compile z /\ wordSem_state_compile_oracle
   a = wordSem_state_compile_oracle z /\ stack
   a = stack z /\ wordSem_state_locals_size
   a = wordSem_state_locals_size z /\ wordSem_state_stack_limit
   a = wordSem_state_stack_limit z /\ wordSem_state_stack_max
   a = wordSem_state_stack_max z /\ wordSem_state_stack_size
   a = wordSem_state_stack_size z`,
  CHEAT_TAC);;


let mem_store_with_const = prove
 (`wordSem_mem_store x z (wordSem_state_locals_fupd (K l) y) =
  OPTION_MAP (\s. wordSem_state_locals_fupd (K l) s) (wordSem_mem_store
  x z y) /\
   wordSem_mem_store x z (state_clock_fupd (K k) y) = OPTION_MAP (\s.
     wordSem_state_clock_fupd (K k) s) (wordSem_mem_store x z y) /\
   wordSem_mem_store x z (wordSem_state_code_fupd (K code) y) =
     OPTION_MAP (\s. wordSem_state_code_fupd (K code) s)
     (wordSem_mem_store x z y) /\
   wordSem_mem_store x z (wordSem_state_compile_fupd (K c) y) =
     OPTION_MAP (\s. wordSem_state_compile_fupd (K c) s)
     (wordSem_mem_store x z y) /\
   wordSem_mem_store x z (wordSem_state_compile_oracle_fupd (K co) y)
     = OPTION_MAP (\s. wordSem_state_compile_oracle_fupd (K co) s)
     (wordSem_mem_store x z y) /\
   wordSem_mem_store x z (wordSem_state_permute_fupd (K perm) y) =
     OPTION_MAP (\s. wordSem_state_permute_fupd (K perm) s)
     (wordSem_mem_store x z y) /\
   wordSem_mem_store x z (stack_fupd (K xs) y) = OPTION_MAP (\s.
     wordSem_state_stack_fupd (K xs) s) (wordSem_mem_store x z y)`,
  CHEAT_TAC);;
add_simp mem_store_with_const;;

let word_exp_with_const = prove
 (`!x y.
   wordSem_word_exp (state_clock_fupd (K k) x) y = wordSem_word_exp x
     y /\
   wordSem_word_exp (stack_fupd (K xs) x) y = wordSem_word_exp x y /\
   wordSem_word_exp (wordSem_state_permute_fupd (K perm) x) y =
     wordSem_word_exp x y /\
   wordSem_word_exp (wordSem_state_termdep_fupd (K termdep) x) y =
     wordSem_word_exp x y /\
   wordSem_word_exp (wordSem_state_code_fupd (K c) x) y =
     wordSem_word_exp x y /\
   wordSem_word_exp (wordSem_state_compile_oracle_fupd (K co) x) y =
     wordSem_word_exp x y /\
   wordSem_word_exp (wordSem_state_compile_fupd (K cc) x) y =
     wordSem_word_exp x y`,
  CHEAT_TAC);;
add_simp word_exp_with_const;;

let assign_const_full = prove
 (`wordSem_assign x y z = SOME a ==> wordSem_state_code
   a = wordSem_state_code z /\ wordSem_state_code_buffer
   a = wordSem_state_code_buffer z /\ wordSem_state_data_buffer
   a = wordSem_state_data_buffer z /\ wordSem_state_compile
   a = wordSem_state_compile z /\ wordSem_state_compile_oracle
   a = wordSem_state_compile_oracle z /\ state_clock
   a = state_clock z /\ state_ffi
   a = state_ffi z /\ wordSem_state_handler
   a = wordSem_state_handler z /\ stack
   a = stack z /\ wordSem_state_locals_size
   a = wordSem_state_locals_size z /\ wordSem_state_stack_limit
   a = wordSem_state_stack_limit z /\ wordSem_state_stack_max
   a = wordSem_state_stack_max z /\ wordSem_state_stack_size
   a = wordSem_state_stack_size z`,
  CHEAT_TAC);;

let assign_const = prove
 (`wordSem_assign x y z = SOME a ==> state_clock
   a = state_clock z /\ state_ffi
   a = state_ffi z`,
  CHEAT_TAC);;

let assign_with_const = prove
 (`wordSem_assign x y (state_clock_fupd (K k) z) = OPTION_MAP (\s.
  wordSem_state_clock_fupd (K k) s) (wordSem_assign x y z) /\
   wordSem_assign x y (wordSem_state_code_fupd (K code) z) =
     OPTION_MAP (\s. wordSem_state_code_fupd (K code) s) (wordSem_assign
     x y z) /\
   wordSem_assign x y (wordSem_state_compile_fupd (K c) z) =
     OPTION_MAP (\s. wordSem_state_compile_fupd (K c) s) (wordSem_assign
     x y z) /\
   wordSem_assign x y (wordSem_state_compile_oracle_fupd (K co) z) =
     OPTION_MAP (\s. wordSem_state_compile_oracle_fupd (K co) s)
     (wordSem_assign x y z) /\
   wordSem_assign x y (wordSem_state_permute_fupd (K perm) z) =
     OPTION_MAP (\s. wordSem_state_permute_fupd (K perm) s)
     (wordSem_assign x y z) /\
   wordSem_assign x y (stack_fupd (K xs) z) = OPTION_MAP (\s.
     wordSem_state_stack_fupd (K xs) s) (wordSem_assign x y z)`,
  CHEAT_TAC);;
add_simp assign_with_const;;

let inst_with_const = prove
 (`wordSem_inst i (wordSem_state_clock_fupd (K k) s) = OPTION_MAP (\s.
  wordSem_state_clock_fupd (K k) s) (wordSem_inst i s) /\
   wordSem_inst i (wordSem_state_code_fupd (K code) s) = OPTION_MAP
     (\s. wordSem_state_code_fupd (K code) s) (wordSem_inst i s) /\
   wordSem_inst i (wordSem_state_compile_fupd (K c) s) = OPTION_MAP
     (\s. wordSem_state_compile_fupd (K c) s) (wordSem_inst i s) /\
   wordSem_inst i (wordSem_state_compile_oracle_fupd (K co) s) =
     OPTION_MAP (\s. wordSem_state_compile_oracle_fupd (K co) s)
     (wordSem_inst i s) /\
   wordSem_inst i (wordSem_state_permute_fupd (K perm) s) =
     OPTION_MAP (\s. wordSem_state_permute_fupd (K perm) s)
     (wordSem_inst i s) /\
   wordSem_inst i (wordSem_state_stack_fupd (K xs) s) = OPTION_MAP
     (\s. wordSem_state_stack_fupd (K xs) s) (wordSem_inst i s)`,
  CHEAT_TAC);;
add_simp inst_with_const;;

let inst_const_full = prove
 (`wordSem_inst i s = SOME s' ==> wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ state_clock
   s' = wordSem_state_clock s /\ state_ffi
   s' = wordSem_state_ffi s /\ wordSem_state_handler
   s' = wordSem_state_handler s /\ stack
   s' = wordSem_state_stack s /\ wordSem_state_locals_size
   s' = wordSem_state_locals_size s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s /\ wordSem_state_stack_size
   s' = wordSem_state_stack_size s`,
  CHEAT_TAC);;

(*FIXME dupe*)
(* [local] *)
let inst_code_gc_fun_const = prove
 (`wordSem_inst i s = SOME t ==> wordSem_state_code
      s = wordSem_state_code t /\ wordSem_state_gc_fun s =
        wordSem_state_gc_fun t /\ wordSem_state_sh_mdomain s =
        wordSem_state_sh_mdomain t /\ wordSem_state_mdomain s =
        wordSem_state_mdomain t /\
      wordSem_state_be s = wordSem_state_be t /\
        wordSem_state_compile s = wordSem_state_compile t /\
        wordSem_state_stack_size s = wordSem_state_stack_size t /\
        wordSem_state_stack_limit s = wordSem_state_stack_limit t`,
  CHEAT_TAC);;

let inst_const = prove
 (`wordSem_inst i s = SOME s' ==> state_clock
   s' = wordSem_state_clock s /\ state_ffi
   s' = wordSem_state_ffi s`,
  CHEAT_TAC);;

let jump_exc_const = prove
 (`wordSem_jump_exc s = SOME (s',y) ==> wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_gc_fun
   s' = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   s' = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   s' = wordSem_state_sh_mdomain s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ state_clock
   s' = wordSem_state_clock s /\ state_ffi
   s' = wordSem_state_ffi s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s /\ wordSem_state_stack_size
   s' = wordSem_state_stack_size s`,
  CHEAT_TAC);;

(* jump_exc_with_const *)
let wordProps_jump_exc_with_const = prove
 (`wordSem_jump_exc (wordSem_state_clock_fupd (K k) s) = OPTION_MAP
  (\(s,t). (wordSem_state_clock_fupd (K k) s,t)) (wordSem_jump_exc s) /\
   wordSem_jump_exc (wordSem_state_permute_fupd (K perm) s) =
     OPTION_MAP (\(s,t). (wordSem_state_permute_fupd (K perm) s,t))
     (wordSem_jump_exc s)`,
  CHEAT_TAC);;
add_simp wordProps_jump_exc_with_const;;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let get_var_imm_with_const = prove
 (cake_as_vars (fun () ->
    `wordSem_get_var_imm x (state_clock_fupd (K k) y) =
  wordSem_get_var_imm x y /\
     wordSem_get_var_imm x (wordSem_state_code_fupd (K code) y) =
       wordSem_get_var_imm x y /\
     wordSem_get_var_imm x (wordSem_state_compile_fupd (K compile)
       y) = wordSem_get_var_imm x y /\
     wordSem_get_var_imm x (wordSem_state_compile_oracle_fupd (K
       compile_oracle) y) = wordSem_get_var_imm x y /\
     wordSem_get_var_imm x (wordSem_state_termdep_fupd (K td) y) =
       wordSem_get_var_imm x y /\
     wordSem_get_var_imm x (wordSem_state_stack_fupd (K xs) y) =
       wordSem_get_var_imm x y /\
     wordSem_get_var_imm x (wordSem_state_permute_fupd (K perm)
       y) = wordSem_get_var_imm x y`),
  CHEAT_TAC);;
add_simp get_var_imm_with_const;;

(* dec_clock_const *)
let wordProps_dec_clock_const = prove
 (`wordSem_state_locals
      (wordSem_dec_clock s) = wordSem_state_locals s /\
        wordSem_state_locals_size
      (wordSem_dec_clock s) = wordSem_state_locals_size s /\
        wordSem_state_fp_regs
      (wordSem_dec_clock s) = wordSem_state_fp_regs s /\
        wordSem_state_store
      (wordSem_dec_clock s) = wordSem_state_store s /\ stack
      (wordSem_dec_clock s) = wordSem_state_stack s /\
        wordSem_state_stack_limit
      (wordSem_dec_clock s) = wordSem_state_stack_limit s /\
        wordSem_state_stack_max
      (wordSem_dec_clock s) = wordSem_state_stack_max s /\
        wordSem_state_stack_size
      (wordSem_dec_clock s) = wordSem_state_stack_size s /\
        wordSem_state_memory
      (wordSem_dec_clock s) = wordSem_state_memory s /\
        wordSem_state_mdomain
      (wordSem_dec_clock s) = wordSem_state_mdomain s /\
        wordSem_state_sh_mdomain
      (wordSem_dec_clock s) = wordSem_state_sh_mdomain s /\
        wordSem_state_permute
      (wordSem_dec_clock s) = wordSem_state_permute s /\
        wordSem_state_compile
      (wordSem_dec_clock s) = wordSem_state_compile s /\
        wordSem_state_compile_oracle
      (wordSem_dec_clock s) = wordSem_state_compile_oracle s /\
        wordSem_state_code_buffer
      (wordSem_dec_clock s) = wordSem_state_code_buffer s /\
        wordSem_state_data_buffer
      (wordSem_dec_clock s) = wordSem_state_data_buffer s /\
        wordSem_state_gc_fun
      (wordSem_dec_clock s) = wordSem_state_gc_fun s /\
        wordSem_state_handler
      (wordSem_dec_clock s) = wordSem_state_handler s /\
        wordSem_state_termdep
      (wordSem_dec_clock s) = wordSem_state_termdep s /\
        wordSem_state_code
      (wordSem_dec_clock s) = wordSem_state_code s /\
      (wordSem_state_be (wordSem_dec_clock s) <=> wordSem_state_be s)
        /\ state_ffi
      (wordSem_dec_clock s) = wordSem_state_ffi s /\ state_clock
      (wordSem_dec_clock (wordSem_state_locals_fupd (K locs) s)) =
        state_clock (wordSem_dec_clock s) /\ state_clock
      (wordSem_dec_clock (wordSem_state_permute_fupd (K p) s)) =
        state_clock (wordSem_dec_clock s)`,
  CHEAT_TAC);;
add_simp wordProps_dec_clock_const;;

let sh_mem_set_var_const = prove
 (`sh_mem_set_var r v s = (x,s') ==> state_clock
   s' = wordSem_state_clock s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_gc_fun
   s' = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   s' = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   s' = wordSem_state_sh_mdomain s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_permute
   s' = wordSem_state_permute s /\ wordSem_state_handler
   s' = wordSem_state_handler s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s /\
   (r = NONE ==> state_ffi s' = wordSem_state_ffi s) /\
   (r = SOME (FFI_final outcome) ==> state_ffi s' = wordSem_state_ffi
     s) /\
   (r = NONE ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (r = SOME (FFI_return f l) ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (r = NONE ==> wordSem_state_stack_max s' = wordSem_state_stack_max
     s) /\
   (r = SOME (FFI_return f l) ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (r = NONE ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s) /\
   (r = SOME (FFI_return f l) ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s)`,
  CHEAT_TAC);;

let sh_mem_store_const = prove
 (`wordSem_sh_mem_store ad v s = (res,s') ==> state_clock
   s' = wordSem_state_clock s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_gc_fun
   s' = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   s' = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   s' = wordSem_state_sh_mdomain s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_permute
   s' = wordSem_state_permute s /\ wordSem_state_handler
   s' = wordSem_state_handler s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s /\
   (res = SOME wordSem_Error ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = NONE ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s)`,
  CHEAT_TAC);;

let sh_mem_store_byte_const = prove
 (`wordSem_sh_mem_store_byte ad v s = (res,s') ==> state_clock
   s' = wordSem_state_clock s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_gc_fun
   s' = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   s' = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   s' = wordSem_state_sh_mdomain s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_permute
   s' = wordSem_state_permute s /\ wordSem_state_handler
   s' = wordSem_state_handler s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s /\
   (res = SOME wordSem_Error ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = NONE ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s)`,
  CHEAT_TAC);;

let sh_mem_store16_const = prove
 (`wordSem_sh_mem_store16 ad v s = (res,s') ==> state_clock
   s' = wordSem_state_clock s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_gc_fun
   s' = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   s' = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   s' = wordSem_state_sh_mdomain s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_permute
   s' = wordSem_state_permute s /\ wordSem_state_handler
   s' = wordSem_state_handler s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s /\
   (res = SOME wordSem_Error ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = NONE ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s)`,
  CHEAT_TAC);;

let sh_mem_store32_const = prove
 (`wordSem_sh_mem_store32 ad v s = (res,s') ==> state_clock
   s' = wordSem_state_clock s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_gc_fun
   s' = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   s' = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   s' = wordSem_state_sh_mdomain s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_permute
   s' = wordSem_state_permute s /\ wordSem_state_handler
   s' = wordSem_state_handler s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s /\
   (res = SOME wordSem_Error ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_locals_size s' =
     wordSem_state_locals_size s) /\
   (res = NONE ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_max s' =
     wordSem_state_stack_max s) /\
   (res = NONE ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s) /\
   (res = SOME wordSem_Error ==> wordSem_state_stack_size s' =
     wordSem_state_stack_size s)`,
  CHEAT_TAC);;

let share_inst_const = prove
 (`share_inst op v c s = (res,s') ==> wordSem_state_be
   s' = wordSem_state_be s /\ wordSem_state_gc_fun
   s' = wordSem_state_gc_fun s /\ wordSem_state_mdomain
   s' = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   s' = wordSem_state_sh_mdomain s /\ wordSem_state_code
   s' = wordSem_state_code s /\ wordSem_state_code_buffer
   s' = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   s' = wordSem_state_data_buffer s /\ wordSem_state_compile
   s' = wordSem_state_compile s /\ wordSem_state_compile_oracle
   s' = wordSem_state_compile_oracle s /\ wordSem_state_permute
   s' = wordSem_state_permute s /\ state_clock
   s' = wordSem_state_clock s /\ wordSem_state_handler
   s' = wordSem_state_handler s /\ wordSem_state_stack_limit
   s' = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   s' = wordSem_state_stack_max s`,
  CHEAT_TAC);;

(*TODO use PAIRMAP and deal with breakage*)
let sh_mem_set_var_with_const = prove
 (`sh_mem_set_var res v (wordSem_state_permute_fupd (K p) s) =
   (I ## (\s. wordSem_state_permute_fupd (K p) s)) (sh_mem_set_var
     res v s) /\
   sh_mem_set_var res v (wordSem_state_clock_fupd (K k) s) =
   (I ## (\s. wordSem_state_clock_fupd (K k) s)) (sh_mem_set_var
     res v s)`,
  CHEAT_TAC);;
add_simp sh_mem_set_var_with_const;;

let sh_mem_load_with_const = prove
 (`wordSem_sh_mem_load a (wordSem_state_locals_fupd (K l) s) =
  wordSem_sh_mem_load a s /\
   wordSem_sh_mem_load a (wordSem_state_permute_fupd (K p) s) =
     wordSem_sh_mem_load a s /\
   wordSem_sh_mem_load a (wordSem_state_clock_fupd (K k) s) =
     wordSem_sh_mem_load a s /\
   wordSem_sh_mem_load a (wordSem_state_stack_fupd (K xs) s) =
     wordSem_sh_mem_load a s`,
  CHEAT_TAC);;
add_simp sh_mem_load_with_const;;

let sh_mem_load_byte_with_const = prove
 (`wordSem_sh_mem_load_byte a (wordSem_state_locals_fupd (K l) s) =
  wordSem_sh_mem_load_byte a s /\
   wordSem_sh_mem_load_byte a (wordSem_state_permute_fupd (K p) s) =
     wordSem_sh_mem_load_byte a s /\
   wordSem_sh_mem_load_byte a (wordSem_state_clock_fupd (K k) s) =
     wordSem_sh_mem_load_byte a s /\
   wordSem_sh_mem_load_byte a (wordSem_state_stack_fupd (K xs) s) =
     wordSem_sh_mem_load_byte a s`,
  CHEAT_TAC);;
add_simp sh_mem_load_byte_with_const;;

let sh_mem_load16_with_const = prove
 (`wordSem_sh_mem_load16 a (wordSem_state_locals_fupd (K l) s) =
  wordSem_sh_mem_load16 a s /\
   wordSem_sh_mem_load16 a (wordSem_state_permute_fupd (K p) s) =
     wordSem_sh_mem_load16 a s /\
   wordSem_sh_mem_load16 a (wordSem_state_clock_fupd (K k) s) =
     wordSem_sh_mem_load16 a s /\
   wordSem_sh_mem_load16 a (wordSem_state_stack_fupd (K xs) s) =
     wordSem_sh_mem_load16 a s`,
  CHEAT_TAC);;
add_simp sh_mem_load16_with_const;;

let sh_mem_load32_with_const = prove
 (`wordSem_sh_mem_load32 a (wordSem_state_locals_fupd (K l) s) =
  wordSem_sh_mem_load32 a s /\
   wordSem_sh_mem_load32 a (wordSem_state_permute_fupd (K p) s) =
     wordSem_sh_mem_load32 a s /\
   wordSem_sh_mem_load32 a (wordSem_state_clock_fupd (K k) s) =
     wordSem_sh_mem_load32 a s /\
   wordSem_sh_mem_load32 a (wordSem_state_stack_fupd (K xs) s) =
     wordSem_sh_mem_load32 a s`,
  CHEAT_TAC);;
add_simp sh_mem_load32_with_const;;

let sh_mem_store_with_const = prove
 (`wordSem_sh_mem_store a w (wordSem_state_permute_fupd (K p) s) =
   (I ## (\s. wordSem_state_permute_fupd (K p) s))
     (wordSem_sh_mem_store a w s) /\
   wordSem_sh_mem_store a w (wordSem_state_clock_fupd (K k) s) =
   (I ## (\s. wordSem_state_clock_fupd (K k) s))
     (wordSem_sh_mem_store a w s)`,
  CHEAT_TAC);;
add_simp sh_mem_store_with_const;;

let sh_mem_store_byte_with_const = prove
 (`wordSem_sh_mem_store_byte a w (wordSem_state_permute_fupd (K p) s) =
   (I ## (\s. wordSem_state_permute_fupd (K p) s))
     (wordSem_sh_mem_store_byte a w s) /\
   wordSem_sh_mem_store_byte a w (wordSem_state_clock_fupd (K k) s) =
   (I ## (\s. wordSem_state_clock_fupd (K k) s))
     (wordSem_sh_mem_store_byte a w s)`,
  CHEAT_TAC);;
add_simp sh_mem_store_byte_with_const;;

let sh_mem_store16_with_const = prove
 (`wordSem_sh_mem_store16 a w (wordSem_state_permute_fupd (K p) s) =
   (I ## (\s. wordSem_state_permute_fupd (K p) s))
     (wordSem_sh_mem_store16 a w s) /\
   wordSem_sh_mem_store16 a w (wordSem_state_clock_fupd (K k) s) =
   (I ## (\s. wordSem_state_clock_fupd (K k) s))
     (wordSem_sh_mem_store16 a w s)`,
  CHEAT_TAC);;
add_simp sh_mem_store16_with_const;;

let sh_mem_store32_with_const = prove
 (`wordSem_sh_mem_store32 a w (wordSem_state_permute_fupd (K p) s) =
   (I ## (\s. wordSem_state_permute_fupd (K p) s))
     (wordSem_sh_mem_store32 a w s) /\
   wordSem_sh_mem_store32 a w (wordSem_state_clock_fupd (K k) s) =
   (I ## (\s. wordSem_state_clock_fupd (K k) s))
     (wordSem_sh_mem_store32 a w s)`,
  CHEAT_TAC);;
add_simp sh_mem_store32_with_const;;

let share_inst_with_const = prove
 (`share_inst op v c (wordSem_state_permute_fupd (K p) s) =
   (I ## (\s. wordSem_state_permute_fupd (K p) s)) (share_inst op v c
     s) /\
   share_inst op v c (wordSem_state_clock_fupd (K k) s) =
   (I ## (\s. wordSem_state_clock_fupd (K k) s)) (share_inst op v c
     s)`,
  CHEAT_TAC);;
add_simp share_inst_with_const;;

let cut_state_with_const = prove
 (`wordSem_cut_state x (state_clock_fupd (K k) z) = OPTION_MAP (\s.
  wordSem_state_clock_fupd (K k) s) (wordSem_cut_state x z) /\
   wordSem_cut_state x (wordSem_state_code_fupd (K code) z) =
     OPTION_MAP (\s. wordSem_state_code_fupd (K code) s)
     (wordSem_cut_state x z) /\
   wordSem_cut_state x (wordSem_state_compile_fupd (K c) z) =
     OPTION_MAP (\s. wordSem_state_compile_fupd (K c) s)
     (wordSem_cut_state x z) /\
   wordSem_cut_state x (wordSem_state_compile_oracle_fupd (K co) z) =
     OPTION_MAP (\s. wordSem_state_compile_oracle_fupd (K co) s)
     (wordSem_cut_state x z) /\
   wordSem_cut_state x (wordSem_state_permute_fupd (K perm) z) =
     OPTION_MAP (\s. wordSem_state_permute_fupd (K perm) s)
     (wordSem_cut_state x z) /\
   wordSem_cut_state x (stack_fupd (K xs) z) = OPTION_MAP (\s.
     wordSem_state_stack_fupd (K xs) s) (wordSem_cut_state x z)`,
  CHEAT_TAC);;
add_simp cut_state_with_const;;

let cut_state_const = prove
 (`wordSem_cut_state x s = SOME s' ==>
   (?l. s' = wordSem_state_locals_fupd (K l) s)`,
  CHEAT_TAC);;

(* TODO: generated names *)

(* HOL4 wordPropsScript.sml:1303-1309: the ML values that the
   definitions below antiquote *)

(* HOL4 wordPropsScript.sml:1311-1325: a theorem whose statement the
   port cannot state yet: evaluate_clock_const *)

(* HOL4 wordPropsScript.sml:1327-1332: the ML values that the
   definitions below antiquote *)

(* HOL4 wordPropsScript.sml:1334-1345: a theorem whose statement the
   port cannot state yet: evaluate_clock_with_const *)

(******CONST LEMMAS END *****)

(*TODO complete for all get set variaents *)
let get_var_set_store = prove
 (`wordSem_get_var v1 (wordSem_set_store v2 x s) = wordSem_get_var v1
  s`,
  CHEAT_TAC);;
add_simp get_var_set_store;;

let get_var_set_fp_var = prove
 (`wordSem_get_var v1 (wordSem_set_fp_var v2 x s) = wordSem_get_var v1
  s`,
  CHEAT_TAC);;
add_simp get_var_set_fp_var;;

let get_var_set_var = prove
 (`wordSem_get_var v1 (wordSem_set_var v2 x s) = (if v1 = v2 then SOME
  x else wordSem_get_var v1 s)`,
  CHEAT_TAC);;

let get_store_set_store = prove
 (`wordSem_get_store v1 (wordSem_set_store v2 x s) = (if v1 = v2 then
  SOME x else wordSem_get_store v1 s)`,
  CHEAT_TAC);;

let get_fp_var_set_fp_var = prove
 (`wordSem_get_fp_var v1 (wordSem_set_fp_var v2 x s) = (if v1 = v2
  then SOME x else wordSem_get_fp_var v1 s)`,
  CHEAT_TAC);;

(* Standard add clock lemma for FBS *)
(* evaluate_add_clock *)
let wordProps_evaluate_add_clock = prove
 (`!p s r s'.
     wordSem_evaluate (p,s) = (r,s') /\ ~(r = SOME wordSem_TimeOut)
       ==>
     wordSem_evaluate (p,wordSem_state_clock_fupd (K
       (wordSem_state_clock s + extra)) s) = (r,state_clock_fupd (K
       (state_clock s' + extra)) s')`,
  CHEAT_TAC);;

(* HOL4 wordPropsScript.sml:1436-1441: ML code, not ported *)

(* This lemma is interesting in wordLang because of the use of MustTerminate

   To remove MustTerminate, we need to inject an exact number of clock ticks
   corresponding to the ticks used in the MustTerminate block

   The number of clock ticks is fixed for any program, and can be characterized by st.clock - rst.clock *)

let with_locals_same_clock = prove
 (`wordSem_state_clock_fupd (K (wordSem_state_clock s))
  (wordSem_state_locals_fupd (K l)
     s) = wordSem_state_locals_fupd (K l)
     s`,
  CHEAT_TAC);;
add_simp with_locals_same_clock;;

(* [local] *)
let cont_loop_not_timeout = prove
 (`wordSem_cont_loop res ==> ~(res = SOME wordSem_TimeOut)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_add_clock_body = prove
 (`wordSem_evaluate (c,s) = (res,s') /\ wordSem_cont_loop res ==>
   (!extra.
     wordSem_evaluate (c,wordSem_state_clock_fupd (K
       (wordSem_state_clock s + extra)) s) =
     (res,state_clock_fupd (K (state_clock s' + extra)) s'))`,
  CHEAT_TAC);;

let evaluate_dec_clock = prove
 (`!prog st res rst.
   wordSem_evaluate (prog,st) = (res,rst) ==>
   wordSem_evaluate (prog,state_clock_fupd (K (state_clock st -
     state_clock rst)) st) = (res,state_clock_fupd (K 0) rst)`,
  CHEAT_TAC);;

(* IO and clock monotonicity *)

(* evaluate_io_events_mono *)
let wordProps_evaluate_io_events_mono = prove
 (`!exps s1 res s2.
    wordSem_evaluate (exps,s1) = (res,s2) ==> ffi_state_io_events
      (wordSem_state_ffi
    s1) <<= ffi_state_io_events (wordSem_state_ffi s2)`,
  CHEAT_TAC);;

(* [local] *)
let SND_alt_def = prove
 (`SND c = (\(a,b). b) c`,
  CHEAT_TAC);;

(*TODO This format of is really weird can this be changed?*)
(* evaluate_add_clock_io_events_mono *)
let wordProps_evaluate_add_clock_io_events_mono = prove
 (`!exps s extra. ffi_state_io_events (state_ffi
    (SND (wordSem_evaluate (exps,s)))) <<= ffi_state_io_events
      (state_ffi
    (SND (wordSem_evaluate (exps,wordSem_state_clock_fupd (K
      (wordSem_state_clock s + extra)) s))))`,
  CHEAT_TAC);;

let evaluate_consts = prove
 (`!xs s1 vs s2.
     wordSem_evaluate (xs,s1) = (vs,s2) ==> wordSem_state_gc_fun
     s1 = wordSem_state_gc_fun s2 /\ wordSem_state_mdomain
     s1 = wordSem_state_mdomain s2 /\ wordSem_state_sh_mdomain
     s1 = wordSem_state_sh_mdomain s2 /\ wordSem_state_be
     s1 = wordSem_state_be s2 /\ wordSem_state_compile
     s1 = wordSem_state_compile s2 /\ wordSem_state_stack_limit
     // s1.stack_size = s2.stack_size ∧
     s1 = wordSem_state_stack_limit s2`,
  CHEAT_TAC);;

(* TODO: monotonicity *)

(* -- *)

let get_vars_length_lemma = prove
 (`!ls s y. wordSem_get_vars ls s = SOME y ==>
           LENGTH y = LENGTH ls`,
  CHEAT_TAC);;

(**)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stack_size_eq = prove
 (cake_as_vars (fun () ->
    `(stack_size (CONS (StackFrame n _5 _6 NONE) stack) = OPTION_MAP2
  (+) n (stack_size stack)) /\
     (stack_size (CONS (StackFrame n _7 _8 (SOME handler)) stack) =
        OPTION_MAP2 (+) (OPTION_MAP ((+) 3) n) (stack_size stack))
          /\
     (stack_size [] = SOME 1)`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stack_size_eq2 = prove
 (cake_as_vars (fun () ->
    `(stack_size (CONS sfrm stack) =
       OPTION_MAP2 (+) (stack_size_frame sfrm) (stack_size stack))
         /\
     (stack_size [] = SOME 1)`),
  CHEAT_TAC);;

(*--Stack Swap Lemma--*)

(*Stacks look the same to the GC except for the keys (e.g. recoloured and in order)*)
let s_frame_val_eq_def = new_definition
  `s_frame_val_eq x1 x2 =
        match (x1,x2) with
          (StackFrame n ls1 ls NONE,StackFrame n' ls1' ls' NONE) ->
        MAP SND ls = MAP SND ls' /\ n = n'
        | ((StackFrame n ls1 ls (SOME y)),(StackFrame n' ls1' ls'
          (SOME y'))) ->
        MAP SND ls = MAP SND ls' /\ y = y' /\ n = n'
        | (_9,_10) -> F`;;

let s_frame_val_eq_def2 = prove
 (`(
      s_frame_val_eq (StackFrame n ls0 ls y) (StackFrame n' ls0'
        ls' y') <=> MAP SND ls = MAP SND ls' /\ y = y' /\ n = n')`,
  CHEAT_TAC);;

let _ = size_thms "stack_frame";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let s_val_eq_def,s_val_eq_ind = define_wf
  `MEASURE (\(x0,x1).      list_size (stack_frame_size (\x. 0)) x0 +
    list_size (stack_frame_size (\x. 0)) x1)`
  [`s_val_eq x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | ((CONS x xs),(CONS y ys)) -> (s_val_eq xs ys /\
                              s_frame_val_eq x y)
        | (_11,_12) -> F`];;

(*Stacks look the same except for the values of the GC-ed cutsets (e.g. result of gc)*)
let s_frame_key_eq_def = new_definition
  `s_frame_key_eq x1 x2 =
        match (x1,x2) with
          (StackFrame n ls0 ls NONE,StackFrame n' ls0' ls' NONE) ->
            MAP FST ls = MAP FST ls' /\ ls0 = ls0' /\ n = n'
        | ((StackFrame n ls0 ls (SOME y)),(StackFrame n' ls0' ls'
          (SOME y'))) -> MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 =
          ls0' /\ n = n'
        | (_13,_14) -> F`;;

let s_frame_key_eq_def2 = prove
 (`(
      s_frame_key_eq (StackFrame n ls0 ls y) (StackFrame n' ls0'
        ls' y') <=> MAP FST ls = MAP FST ls' /\ y = y' /\ ls0 = ls0'
        /\ n = n')`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let s_key_eq_def,s_key_eq_ind = define_wf
  `MEASURE (\(x0,x1).      list_size (stack_frame_size (\x. 0)) x0 +
    list_size (stack_frame_size (\x. 0)) x1)`
  [`s_key_eq x1 x2 =
        match (x1,x2) with
          ([],[]) -> T
        | ((CONS x xs),(CONS y ys)) -> (s_key_eq xs ys /\
                              s_frame_key_eq x y)
        | (_15,_16) -> F`];;

let s_key_eq_def2 = prove
 (`!l1 l2.
   s_key_eq l1 l2 = ALL2 s_frame_key_eq l1 l2`,
  CHEAT_TAC);;

let s_val_eq_def2 = prove
 (`!l1 l2.
   s_val_eq l1 l2 = ALL2 s_frame_val_eq l1 l2`,
  CHEAT_TAC);;

(*Reflexive*)
let s_frame_key_eq_refl = prove
 (`!ls. s_frame_key_eq ls ls = T`,
  CHEAT_TAC);;

let s_frame_val_eq_refl = prove
 (`!ls. s_frame_val_eq ls ls = T`,
  CHEAT_TAC);;

let s_key_eq_refl = prove
 (`!ls. s_key_eq ls ls = T`,
  CHEAT_TAC);;

let s_val_eq_refl = prove
 (`!ls. s_val_eq ls ls = T`,
  CHEAT_TAC);;

(*transitive*)
(* [local] *)
let s_frame_key_eq_trans = prove
 (`!a b c. s_frame_key_eq a b /\ s_frame_key_eq b c ==>
             s_frame_key_eq a c`,
  CHEAT_TAC);;

let s_key_eq_trans = prove
 (`!a b c. s_key_eq a b /\ s_key_eq b c ==>
            s_key_eq a c`,
  CHEAT_TAC);;

(* [local] *)
let s_frame_val_eq_trans = prove
 (`!a b c. s_frame_val_eq a b /\ s_frame_val_eq b c ==>
             s_frame_val_eq a c`,
  CHEAT_TAC);;

let s_val_eq_trans = prove
 (`!a b c. s_val_eq a b /\ s_val_eq b c ==>
             s_val_eq a c`,
  CHEAT_TAC);;


(*Symmetric*)
(* [local] *)
let s_frame_key_eq_sym = prove
 (`!a b. s_frame_key_eq a b <=> s_frame_key_eq b a`,
  CHEAT_TAC);;


let s_key_eq_sym = prove
 (`!a b. s_key_eq a b <=> s_key_eq b a`,
  CHEAT_TAC);;

(* [local] *)
let s_frame_val_eq_sym = prove
 (`!a b. s_frame_val_eq a b <=> s_frame_val_eq b a`,
  CHEAT_TAC);;

let s_val_eq_sym = prove
 (`!a b. s_val_eq a b <=> s_val_eq b a`,
  CHEAT_TAC);;

(* [local] *)
let s_frame_val_and_key_eq = prove
 (`!s t. s_frame_val_eq s t /\ s_frame_key_eq s t ==> s = t`,
  CHEAT_TAC);;

let LIST_REL_CONJ2 = prove
 (`ALL2 (\a b. P a b /\ Q a b) l1 l2 <=>
   ALL2 P l1 l2 /\ ALL2 Q l1 l2`,
  CHEAT_TAC);;

let s_val_and_key_eq = prove
 (`!s t. s_val_eq s t /\ s_key_eq s t ==> s = t`,
  CHEAT_TAC);;

(* [local] *)
let dec_stack_stack_key_eq = prove
 (`!wl st st'. wordSem_dec_stack wl st = SOME st' ==> s_key_eq st st'`,
  CHEAT_TAC);;

(*gc preserves the stack_key relation*)
let gc_s_key_eq = prove
 (`!s x. wordSem_gc s = SOME x ==> s_key_eq (wordSem_state_stack s)
  (stack x)`,
  CHEAT_TAC);;

(* [local] *)
let s_val_eq_enc_stack = prove
 (`!st st'. s_val_eq st st' ==> wordSem_enc_stack st =
  wordSem_enc_stack st'`,
  CHEAT_TAC);;

(* [local] *)
let s_val_eq_dec_stack = prove
 (`!q st st' x. s_val_eq st st' /\ wordSem_dec_stack q st = SOME x ==>
     (?y. wordSem_dec_stack q st' = SOME y /\ s_val_eq x y)`,
  CHEAT_TAC);;

(*gc succeeds on all stacks related by stack_val and there are relations
  in the result*)
let gc_s_val_eq = prove
 (`!s x st y. s_val_eq (wordSem_state_stack s) st /\
             wordSem_gc s = SOME y ==>
      (?z. wordSem_gc (wordSem_state_stack_fupd (K st) s) = SOME
        (stack_fupd (K z) y) /\
          s_val_eq (stack y) z /\ s_key_eq z st)`,
  CHEAT_TAC);;

(*Slightly more general theorem allows the unused locals to be differnt*)
let gc_s_val_eq_word_state = prove
 (`!s tlocs tstack y.
          s_val_eq (wordSem_state_stack s) tstack /\
          wordSem_gc s = SOME y ==>
    (?zlocs zstack.
          wordSem_gc (wordSem_state_locals_fupd (K tlocs)
            (wordSem_state_stack_fupd (K tstack) s)) =
          SOME (wordSem_state_locals_fupd (K zlocs) (stack_fupd (K
            zstack) y)) /\
          s_val_eq (stack y) zstack /\ s_key_eq zstack tstack)`,
  CHEAT_TAC);;

(*Most generalised gc_s_val_eq*)
let gc_s_val_eq_gen = prove
 (`!s t s'. wordSem_state_gc_fun
   s = wordSem_state_gc_fun t /\ wordSem_state_memory
   s = wordSem_state_memory t /\ wordSem_state_mdomain
   s = wordSem_state_mdomain t /\ wordSem_state_store
   s = wordSem_state_store t /\
   s_val_eq (wordSem_state_stack s) (stack t) /\
     wordSem_state_stack_size
   s = wordSem_state_stack_size t /\ wordSem_state_stack_max
   s = wordSem_state_stack_max t /\ wordSem_state_stack_limit
   s = wordSem_state_stack_limit t /\
   wordSem_gc s = SOME s' ==>
   (?t'.
   wordSem_gc t = SOME t' /\
   s_val_eq (stack s') (stack t') /\
   s_key_eq (stack t) (stack t') /\ wordSem_state_memory
   t' = wordSem_state_memory s' /\ wordSem_state_store
   t' = wordSem_state_store s' /\ wordSem_state_stack_size
   t' = wordSem_state_stack_size s' /\ wordSem_state_stack_max
   t' = wordSem_state_stack_max s' /\ wordSem_state_stack_limit
   t' = wordSem_state_stack_limit s')`,
  CHEAT_TAC);;

(*pushing and popping maintain the stack_key relation*)
let push_env_pop_env_s_key_eq = prove
 (`!x b s t. s_key_eq (stack (wordSem_push_env x b s)) (stack t) ==>
       (?n l ls opt. stack
              t = CONS (StackFrame n (toAList (FST x)) l opt) ls /\
              (?y. (wordSem_pop_env t = SOME y /\
                wordSem_state_locals
                   y = sptree_union (fromAList l) (fromAList (toAList
                     (FST x))) /\
                   (domain (SND x)) UNION (domain (FST x)) = domain
                     (wordSem_state_locals y) /\
                   s_key_eq (wordSem_state_stack s) (stack y))))`,
  CHEAT_TAC);;

(* [local] *)
let get_vars_stack_swap = prove
 (`!l s t. wordSem_state_locals s = wordSem_state_locals t ==>
     wordSem_get_vars l s = wordSem_get_vars l t`,
  CHEAT_TAC);;


let s_val_eq_length = prove
 (`!s t. s_val_eq s t ==> LENGTH s = LENGTH t`,
  CHEAT_TAC);;

let s_key_eq_length = prove
 (`!s t. s_key_eq s t ==> LENGTH s = LENGTH t`,
  CHEAT_TAC);;

(* [local] *)
let s_val_eq_APPEND = prove
 (`!s t x y. (s_val_eq s t /\ s_val_eq x y) ==> s_val_eq (APPEND s x)
  (APPEND t y)`,
  CHEAT_TAC);;

(* [local] *)
let s_val_eq_REVERSE = prove
 (`!s t. s_val_eq s t ==> s_val_eq (REVERSE s) (REVERSE t)`,
  CHEAT_TAC);;

(* [local] *)
let s_val_eq_TAKE = prove
 (`!s t n. s_val_eq s t ==> s_val_eq (TAKE n s) (TAKE n t)`,
  CHEAT_TAC);;

(* [local] *)
let s_val_eq_LASTN = prove
 (`!s t n.
     s_val_eq s t ==> s_val_eq (LASTN n s) (LASTN n t)`,
  CHEAT_TAC);;

(* [local] *)
let s_key_eq_APPEND = prove
 (`!s t x y. (s_key_eq s t /\ s_key_eq x y) ==> s_key_eq (APPEND s x)
  (APPEND t y)`,
  CHEAT_TAC);;

(* [local] *)
let s_key_eq_REVERSE = prove
 (`!s t. s_key_eq s t ==> s_key_eq (REVERSE s) (REVERSE t)`,
  CHEAT_TAC);;

(* [local] *)
let s_key_eq_TAKE = prove
 (`!s t n. s_key_eq s t ==> s_key_eq (TAKE n s) (TAKE n t)`,
  CHEAT_TAC);;

(* [local] *)
let s_key_eq_LASTN = prove
 (`!s t n.
     s_key_eq s t ==> s_key_eq (LASTN n s) (LASTN n t)`,
  CHEAT_TAC);;

let s_key_eq_tail = prove
 (`!a b c d. s_key_eq (CONS a b) (CONS c d) ==> s_key_eq b d`,
  CHEAT_TAC);;

(* [local] *)
let s_val_eq_tail = prove
 (`!a b c d. s_val_eq (CONS a b) (CONS c d) ==> s_val_eq b d`,
  CHEAT_TAC);;

(* [local] *)
let s_key_eq_LASTN_exists = prove
 (`!s t n m e0 e y xs.
     s_key_eq s t /\
     LASTN n s = CONS (StackFrame m e0 e (SOME y)) xs ==> (?e' ls.
         LASTN n t = CONS (StackFrame m e0 e' (SOME y)) ls /\
         MAP FST e' = MAP FST e /\ s_key_eq xs ls)`,
  CHEAT_TAC);;

let s_val_eq_LASTN_exists = prove
 (`!s t n m e0 e y xs.
    s_val_eq s t /\
   LASTN n s = CONS (StackFrame m e0 e (SOME y)) xs ==> (?e0' e' ls.
       LASTN n t = CONS (StackFrame m e0' e' (SOME y)) ls /\
       MAP SND e' = MAP SND e /\ s_val_eq xs ls)`,
  CHEAT_TAC);;

let LASTN_LENGTH_cond = prove
 (`!n xs. n = LENGTH xs ==> LASTN n xs = xs`,
  CHEAT_TAC);;

(* [local] *)
let handler_eq = prove
 (`wordSem_state_handler_fupd (K (wordSem_state_handler x))
     x = x`,
  CHEAT_TAC);;

let s_val_eq_stack_size = prove
 (`!xs ys.
    s_val_eq xs ys ==>
    stack_size xs = stack_size ys`,
  CHEAT_TAC);;


let s_key_eq_stack_size = prove
 (`!xs ys. s_key_eq xs ys ==> stack_size xs = stack_size ys`,
  CHEAT_TAC);;

let s_val_append_eq_stack_size = prove
 (`!stk stk' frm. s_val_eq stk stk' ==>
     stack_size (CONS frm stk) = stack_size (CONS frm stk')`,
  CHEAT_TAC);;

(* Stack swap theorem for evaluate *)
(* evaluate_stack_swap *)
let wordProps_evaluate_stack_swap = prove
 (`!c s.
     match wordSem_evaluate (c,s) with (SOME wordSem_Error,s1) -> T |
       (SOME (wordSem_FinalFFI e),s1) -> wordSem_state_stack s1 = [] /\
       wordSem_state_locals s1 = LN /\
                            (!xs. s_val_eq (wordSem_state_stack s) xs
                              ==>
                              wordSem_evaluate
                                (c,wordSem_state_stack_fupd (K xs) s) =
                              (SOME (wordSem_FinalFFI e),s1)) | (SOME
                                wordSem_TimeOut,s1) ->
                                wordSem_state_stack s1 = [] /\
                                wordSem_state_locals s1 = LN /\
                            (!xs. s_val_eq (wordSem_state_stack s) xs
                              ==>
                              wordSem_evaluate
                                (c,wordSem_state_stack_fupd (K xs) s) =
                              (SOME wordSem_TimeOut,s1)) | (SOME
                                wordSem_NotEnoughSpace,s1) ->
                                wordSem_state_stack s1 = [] /\
                                wordSem_state_locals s1 = LN /\
                              (!xs. s_val_eq (wordSem_state_stack s)
                                xs ==>
                              wordSem_evaluate
                                (c,wordSem_state_stack_fupd (K xs) s) =
                              (SOME wordSem_NotEnoughSpace,s1)) | (
        // for both errors,
        // the stack and locs should also be [] so the swapped stack
        // result should be exactly the same
        SOME (wordSem_Exception x y),s1) ->
           (wordSem_state_handler s < LENGTH (wordSem_state_stack s))
             /\
           (
            // precondition for jump_exc
            ?e0 e n ls m lss.
               (LASTN (wordSem_state_handler s + 1)
                 (wordSem_state_stack s) = CONS (StackFrame m e0 e (SOME
                 n)) ls) /\
               Abbrev (m = wordSem_state_locals_size s1) /\
               (MAP FST e = MAP FST lss /\ wordSem_state_locals
                  s1 = sptree_union (fromAList lss) (fromAList e0))
                    /\
               (s_key_eq (wordSem_state_stack s1) ls) /\
                 (wordSem_state_handler s1 = (match n with (a,b,c) ->
                 a)) /\
               (!xs e0' e' ls'.
                          (LASTN (wordSem_state_handler s + 1) xs =
                            CONS (StackFrame m e0' e' (SOME n)) ls') /\
                          (s_val_eq (wordSem_state_stack s) xs) ==>
                          // this implies n=n' and m=m' and MAP SND e0' = MAP SND e0
                          (?st locs.
                          (wordSem_evaluate
                            (c,wordSem_state_stack_fupd (K xs) s) =
                             (SOME (wordSem_Exception x
                               y),wordSem_state_locals_fupd (K locs)
                               (wordSem_state_handler_fupd (K (match n
                               with (a,b,c) -> a))
                               (wordSem_state_stack_fupd (K st)
                              s1))) /\
                           (?lss'. MAP FST e' = MAP FST lss' /\
                              locs = sptree_union (fromAList lss')
                                (fromAList e0') /\
                              MAP SND lss = MAP SND lss') /\
                           s_val_eq (wordSem_state_stack s1) st /\
                             s_key_eq ls' st)))) | (
        // NONE, SOME Result cases
        res,s1) -> (s_key_eq (wordSem_state_stack s)
          (wordSem_state_stack s1)) /\ (wordSem_state_handler s1 =
          wordSem_state_handler s) /\
                   (!xs. s_val_eq (wordSem_state_stack s) xs ==>
                         (?st. wordSem_evaluate
                           (c,wordSem_state_stack_fupd (K xs) s) =
                              (res,wordSem_state_stack_fupd (K st)
                                s1) /\
                              s_val_eq (wordSem_state_stack s1) st /\
                              s_key_eq xs st))`,
  CHEAT_TAC);;

(*--Stack Swap Lemma DONE--*)

(*--Permute Swap Lemma--*)
(*For any target result permute, we can find an initial permute such that the
  final permute is equal to the target *)
let permute_swap_lemma = prove
 (`!prog st perm.
   let (res,rst) = wordSem_evaluate (prog,st) in
     ~(res = SOME wordSem_Error) ==>
     // Note: actually provable without this assum, but this is simpler
     (?perm'. wordSem_evaluate (prog,wordSem_state_permute_fupd (K
       perm') st) =
     (res,wordSem_state_permute_fupd (K perm) rst))`,
  CHEAT_TAC);;

(* Locals extend lemma *)
let locals_rel_def = new_definition
  `locals_rel temp (s:('a word_loc) spt) t <=> (!x. x < temp ==>
  sptree_lookup x s = sptree_lookup x t)`;;

let the_words_EVERY_IS_SOME = prove
 (`!ls x.
   the_words ls = SOME x ==>
   ALL IS_SOME ls`,
  CHEAT_TAC);;

let locals_rel_get_vars = prove
 (`!ls vs.
   wordSem_get_vars ls st = SOME vs /\
   ALL (\x. x < temp) ls /\
   locals_rel temp (wordSem_state_locals st) loc ==>
   wordSem_get_vars ls (wordSem_state_locals_fupd (K loc) st) =
     SOME vs`,
  CHEAT_TAC);;

let locals_rel_alist_insert = prove
 (`!ls vs s t.
   locals_rel temp s t /\
   ALL (\x. x < temp) ls ==>
   locals_rel temp (alist_insert ls vs s) (alist_insert ls vs t)`,
  CHEAT_TAC);;

let locals_rel_get_var = prove
 (`r < temp /\
   wordSem_get_var r st = SOME x /\
   locals_rel temp (wordSem_state_locals st) loc ==>
   wordSem_get_var r (wordSem_state_locals_fupd (K loc) st) = SOME
     x`,
  CHEAT_TAC);;

let locals_rel_get_var_simp = prove
 (`r < temp /\
   locals_rel temp (wordSem_state_locals st) loc ==>
   wordSem_get_var r (wordSem_state_locals_fupd (K loc) st) =
     wordSem_get_var r st`,
  CHEAT_TAC);;

let locals_rel_get_vars_simp = prove
 (`ALL (\x. x < temp) l /\
   locals_rel temp (wordSem_state_locals st) loc ==>
   wordSem_get_vars l (wordSem_state_locals_fupd (K loc) st) =
     wordSem_get_vars l st`,
  CHEAT_TAC);;

let locals_rel_get_var_imm = prove
 (`every_var_imm (\x. x < temp) r /\
   wordSem_get_var_imm r st = SOME x /\
   locals_rel temp (wordSem_state_locals st) loc ==>
   wordSem_get_var_imm r (wordSem_state_locals_fupd (K loc) st) =
     SOME x`,
  CHEAT_TAC);;

let locals_rel_get_var_imm_simp = prove
 (`every_var_imm (\x. x < temp) r /\
   locals_rel temp (wordSem_state_locals st) loc ==>
   wordSem_get_var_imm r (wordSem_state_locals_fupd (K loc) st) =
     wordSem_get_var_imm r st`,
  CHEAT_TAC);;

let locals_rel_word_exp = prove
 (`!s exp w.
     every_var_exp (\x. x < temp) exp /\
     wordSem_word_exp s exp = SOME w /\
     locals_rel temp (wordSem_state_locals s) loc ==>
     wordSem_word_exp (wordSem_state_locals_fupd (K loc) s) exp =
       SOME w`,
  CHEAT_TAC);;

let locals_rel_word_exp_simp = prove
 (`!s exp w.
     every_var_exp (\x. x < temp) exp /\
     locals_rel temp (wordSem_state_locals s) loc ==>
     wordSem_word_exp (wordSem_state_locals_fupd (K loc) s) exp =
       wordSem_word_exp s exp`,
  CHEAT_TAC);;

(* [local] *)
let locals_rel_set_var = prove
 (`!n s t.
   locals_rel temp s t ==>
   locals_rel temp (sptree_insert n v s) (sptree_insert n v t)`,
  CHEAT_TAC);;

(* [local] *)
let locals_rel_delete = prove
 (`!n s t.
   locals_rel temp s t ==>
   locals_rel temp (sptree_delete n s) (sptree_delete n t)`,
  CHEAT_TAC);;

let locals_rel_cut_envs = prove
 (`locals_rel temp loc loc' /\
   every_name (\x. x < temp) names /\
   cut_envs names loc = SOME x ==>
   cut_envs names loc' = SOME x`,
  CHEAT_TAC);;

let locals_rel_cut_env = prove
 (`locals_rel temp loc loc' /\
   every_name (\x. x < temp) names /\
   wordSem_cut_env names loc = SOME x ==>
   wordSem_cut_env names loc' = SOME x`,
  CHEAT_TAC);;

(*Extra temporaries not mentioned in program
  do not affect evaluation
  TODO: theorem statement needs to be changed *)
let locals_rel_evaluate_thm = prove
 (`!prog st res rst loc temp.
     wordSem_evaluate (prog,st) = (res,rst) /\ ~(res = SOME
       wordSem_Error) /\
     wordLang_every_var (\x. x < temp) prog /\
     locals_rel temp (wordSem_state_locals st) loc ==>
     (?loc'.
       wordSem_evaluate (prog,wordSem_state_locals_fupd (K loc) st) =
         (res,wordSem_state_locals_fupd (K loc') rst) /\
       (match res with NONE -> locals_rel temp
         (wordSem_state_locals rst) loc' | SOME (wordLang_Break _17)
         -> locals_rel temp (wordSem_state_locals rst) loc' | SOME
         (wordLang_Continue _18) -> locals_rel temp
         (wordSem_state_locals rst) loc' | SOME _19 ->
         wordSem_state_locals rst = loc'))`,
  CHEAT_TAC);;

(* HOL4 wordPropsScript.sml:3622-3627: a proof *)

(* HOL4 wordPropsScript.sml:3629-3642: a proof *)

(* HOL4 wordPropsScript.sml:3644-3650: a proof *)

(* HOL4 wordPropsScript.sml:3652-3666: a proof *)

(* HOL4 wordPropsScript.sml:3668-3697: a proof *)

(* HOL4 wordPropsScript.sml:3699-3709: a proof *)

(* HOL4 wordPropsScript.sml:3711-3716: a proof *)

(* HOL4 wordPropsScript.sml:3718-3737: a proof *)

(* HOL4 wordPropsScript.sml:3739-3748: a proof *)

(* HOL4 wordPropsScript.sml:3750-3758: a proof *)

(* HOL4 wordPropsScript.sml:3760-3766: a proof *)

(* HOL4 wordPropsScript.sml:3768-3773: a proof *)

(* HOL4 wordPropsScript.sml:3775-3783: a proof *)

(* HOL4 wordPropsScript.sml:3785-3791: a proof *)

(* HOL4 wordPropsScript.sml:3793-3806: a proof *)

(* HOL4 wordPropsScript.sml:3808-3810: a proof *)

(* HOL4 wordPropsScript.sml:3812-3814: a proof *)

(* HOL4 wordPropsScript.sml:3816-3820: a proof *)

(* HOL4 wordPropsScript.sml:3822-3826: a proof *)

(* HOL4 wordPropsScript.sml:3828-3831: a proof *)

(* HOL4 wordPropsScript.sml:3833-3838: a proof *)

(* HOL4 wordPropsScript.sml:3840-3844: a proof *)

(* HOL4 wordPropsScript.sml:3846-3849: a proof *)

(* HOL4 wordPropsScript.sml:3851-3853: a proof *)

(* HOL4 wordPropsScript.sml:3855-3859: a proof *)

(* HOL4 wordPropsScript.sml:3861-3865: a proof *)

(* HOL4 wordPropsScript.sml:3867: a proof *)

let gc_fun_ok_def = new_definition
  `gc_fun_ok (f:('a word_loc) list#('a word->'a word_loc)#('a
  word->bool)#(store_name,'a word_loc)fmap->(('a word_loc) list#('a
  word->'a word_loc)#(store_name,'a word_loc)fmap) option) =
     (!wl m d s wl1 m1 s1.
       Handler IN FDOM s /\
       (f (wl,m,d,s \\ Handler) = SOME (wl1,m1,s1)) ==>
       (LENGTH wl = LENGTH wl1) /\
       ~(Handler IN FDOM s1) /\
       (f (wl,m,d,s) = SOME (wl1,m1,s1 |+ (Handler,FAPPLY s
         Handler))))`;;

let push_env_dec_clock_stack = prove
 (`wordSem_state_stack_max
     (wordSem_push_env y opt (wordSem_dec_clock t)) =
       wordSem_state_stack_max
     (wordSem_push_env y opt t) /\ stack
     (wordSem_push_env y opt (wordSem_dec_clock t)) = stack
     (wordSem_push_env y opt t)`,
  CHEAT_TAC);;

let set_store_stack_max_greater_bound = prove
 (`!v x s t. wordSem_set_store v x s = t /\
   option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack s))
     (wordSem_state_locals_size s)) (wordSem_state_stack_max s) ==>
      option_le (OPTION_MAP2 (+) (stack_size (stack t))
        (wordSem_state_locals_size t)) (wordSem_state_stack_max t)`,
  CHEAT_TAC);;

let stack_size_some_at_least_one = prove
 (`!stk sz. stack_size stk = SOME sz ==> 1 <= sz`,
  CHEAT_TAC);;

let push_call_option_le_stack_max_preserved = prove
 (`!args sz env handler s.
   option_le
     (OPTION_MAP2 (+)
        (stack_size (stack (wordSem_call_env args sz
          (wordSem_push_env env handler s)))) (wordSem_state_locals_size
        (wordSem_call_env args sz (wordSem_push_env env handler s))))
          (wordSem_state_stack_max
    (wordSem_call_env args sz (wordSem_push_env env handler s)))`,
  CHEAT_TAC);;


let pop_env_option_le_stack_max_preserved = prove
 (`!s t.
     option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack s))
       (wordSem_state_locals_size s)) (wordSem_state_stack_max s) /\
     wordSem_pop_env s = SOME t ==>
       option_le (OPTION_MAP2 (+) (stack_size (stack t))
         (wordSem_state_locals_size t)) (wordSem_state_stack_max t)`,
  CHEAT_TAC);;


let dec_stack_stack_size_some_not_none = prove
 (`!xs stk stk' x. wordSem_dec_stack xs stk = SOME stk' /\ stack_size
  stk = SOME x ==> ~(stack_size stk' = NONE)`,
  CHEAT_TAC);;


let dec_stack_stack_size_not_none_not_none = prove
 (`!xs stk stk'. wordSem_dec_stack xs stk = SOME stk' /\ ~(stack_size
  stk = NONE) ==> ~(stack_size stk' = NONE)`,
  CHEAT_TAC);;


let dec_stack_stack_size_some_leq = prove
 (`!xs stk stk' x y. wordSem_dec_stack xs stk = SOME stk' /\
     stack_size stk = SOME x /\
     stack_size stk' = SOME y ==>
       y <= x`,
  CHEAT_TAC);;


let flush_state_option_le_stack_max_preserved = prove
 (`!s p.
      option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack s))
        (wordSem_state_locals_size s)) (wordSem_state_stack_max s) ==>
      (let t = wordSem_flush_state p s in
        option_le
          (OPTION_MAP2 (+) (stack_size (stack t))
            (wordSem_state_locals_size
              t)) (wordSem_state_stack_max t))`,
  CHEAT_TAC);;


let LASTN_stack_size_SOME = prove
 (`!n stack' stack' x.
   LASTN n stack' = stack' /\
   stack_size stack' = SOME x /\ n <= LENGTH stack' ==>
   (?y. stack_size stack' = SOME y /\ y <= x)`,
  CHEAT_TAC);;

(*I'm pretty sure this is defined somewhere else too
MOVE THIS to backend props.*)
let OPTION_MAP2_ADD_0 = prove
 (`OPTION_MAP2 (+) m (SOME 0) = m /\
   OPTION_MAP2 (+) (SOME 0) m = m`,
  CHEAT_TAC);;

(* [local] *)
let option_le_stack_size_nil = prove
 (`option_le (stack_size []) (OPTION_MAP2 (+) (stack_size xs) opt)`,
  CHEAT_TAC);;

let evaluate_option_le_stack_max_preserved = prove
 (`!p s r t. wordSem_evaluate (p,s) = (r,t) /\
      option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack s))
        (wordSem_state_locals_size s)) (wordSem_state_stack_max s) ==>
      option_le (OPTION_MAP2 (+) (stack_size (stack t))
        (wordSem_state_locals_size t)) (wordSem_state_stack_max t)`,
  CHEAT_TAC);;

let push_env_stack_max_eq = prove
 (`wordSem_state_stack_max
     (wordSem_push_env env handler s) =
     OPTION_MAP2 MAX (wordSem_state_stack_max s)
       (stack_size (stack (wordSem_push_env env handler s)))`,
  CHEAT_TAC);;
(* [local] *)
let call_env_option_le_stack_max = prove
 (`option_le (wordSem_state_stack_max s) (wordSem_state_stack_max
  (wordSem_call_env args1 ss s))`,
  CHEAT_TAC);;
(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let call_push_env_option_le_stack_max = prove
 (cake_as_vars (fun () ->
    `option_le (wordSem_state_stack_max s) (wordSem_state_stack_max
       (wordSem_call_env args1 ss (wordSem_push_env envs handler
         s)))`),
  CHEAT_TAC);;

let evaluate_stack_max_le = prove
 (`!c s1 res s2.
   wordSem_evaluate (c,s1) = (res,s2) ==>
   option_le (wordSem_state_stack_max s1) (wordSem_state_stack_max
     s2)`,
  CHEAT_TAC);;

let evaluate_stack_max = prove
 (`!c s1 res s2.
   wordSem_evaluate (c,s1) = (res,s2) ==>
   (match wordSem_state_stack_max s1 with
     NONE -> wordSem_state_stack_max s2 = NONE | SOME stack_max ->
       the stack_max (wordSem_state_stack_max s2) >= stack_max)`,
  CHEAT_TAC);;

let evaluate_stack_max_IS_SOME = prove
 (`!c s1 res s2.
     wordSem_evaluate (c,s1) = (res,s2) /\ IS_SOME
       (wordSem_state_stack_max s2) ==>
     IS_SOME (wordSem_state_stack_max s1)`,
  CHEAT_TAC);;

(* evaluate_stack_limit *)
let wordProps_evaluate_stack_limit = prove
 (`!c s1 res s2.
   wordSem_evaluate (c,s1) = (res,s2) ==> wordSem_state_stack_limit
   s2 = wordSem_state_stack_limit s1`,
  CHEAT_TAC);;

let evaluate_stack_limit_stack_max_eq = prove
 (`!c s1 res s2.
   wordSem_evaluate (c,s1) = (res,s2) /\ the
     (wordSem_state_stack_limit s1) (wordSem_state_stack_max s1) >=
     wordSem_state_stack_limit s1 ==>
   the (wordSem_state_stack_limit s2) (wordSem_state_stack_max s2)
     >= wordSem_state_stack_limit s2`,
  CHEAT_TAC);;

let evaluate_stack_limit_stack_max = prove
 (`!c s1 res s2.
   wordSem_evaluate (c,s1) = (res,s2) /\ the
     (wordSem_state_stack_limit s1 + 1) (wordSem_state_stack_max s1) >
     wordSem_state_stack_limit s1 ==>
   the (wordSem_state_stack_limit s2 + 1) (wordSem_state_stack_max
     s2) > wordSem_state_stack_limit s2`,
  CHEAT_TAC);;

let wordProps_inc_clock_def = new_definition
  `wordProps_inc_clock n (t:('a,'c,'ffi)wordSem_state) =
  wordSem_state_clock_fupd (K (wordSem_state_clock t + n)) t`;;

let inc_clock_0 = prove
 (`!t. wordProps_inc_clock 0 t = t`,
  CHEAT_TAC);;
add_simp inc_clock_0;;

let inc_clock_inc_clock = prove
 (`!t. wordProps_inc_clock n (wordProps_inc_clock m t) =
  wordProps_inc_clock (n + m) t`,
  CHEAT_TAC);;
add_simp inc_clock_inc_clock;;

let evaluate_call_push_dec_option_le_stack_max = prove
 (`!p args sz env handler s res t ck.
     wordSem_evaluate (p,wordSem_call_env args sz
                (wordSem_push_env env handler (wordSem_dec_clock
                  (wordSem_state_clock_fupd (K ck) s)))) = (res,t) ==>
     option_le (wordSem_state_stack_max (wordSem_call_env args sz
       (wordSem_push_env env handler s))) (wordSem_state_stack_max t)`,
  CHEAT_TAC);;

let evaluate_stack_max_only_grows = prove
 (`!p s r t ck r' t'.
      wordSem_evaluate (p,s) = (r,t) /\
      wordSem_evaluate (p,wordProps_inc_clock ck s) = (r',t') ==>
        option_le (wordSem_state_stack_max t)
          (wordSem_state_stack_max t')`,
  CHEAT_TAC);;

let evaluate_code_only_grows = prove
 (`!p s r t. wordSem_evaluate (p,s) = (r,t) ==> subspt
  (wordSem_state_code s) (wordSem_state_code t)`,
  CHEAT_TAC);;

let evaluate_NONE_stack_size_const = prove
 (`!p s t. wordSem_evaluate (p,s) = (NONE,t) ==>
           stack_size (stack t) = stack_size (wordSem_state_stack
             s)`,
  CHEAT_TAC);;

let env_to_list_lookup_equiv = prove
 (`env_to_list y f = (q,r) ==>
    (!n. ALOOKUP q n = sptree_lookup n y) /\
    (!x1 x2. MEM (x1,x2) q ==> sptree_lookup x1 y = SOME x2)`,
  CHEAT_TAC);;

let env_to_list_ALL_DISTINCT = prove
 (`env_to_list y perm = (vs,other) ==> ALL_DISTINCT (MAP FST vs)`,
  CHEAT_TAC);;

let env_to_list_ALL_DISTINCT_FST = prove
 (`ALL_DISTINCT (MAP FST (FST (env_to_list y perm)))`,
  CHEAT_TAC);;

let no_alloc_code_def = new_definition
  `no_alloc_code (code:(num#'a wordLang_prog) spt) <=>
   (!k n p. sptree_lookup k code = SOME (n,p) ==> no_alloc p)`;;

let no_alloc_find_code = prove
 (`!code dest args lsize args1 expr ps.
     wordSem_find_code dest args code lsize = SOME (args1,expr,ps) /\
     no_alloc_code code ==>
     no_alloc expr`,
  CHEAT_TAC);;

let no_install_code_def = new_definition
  `no_install_code (code:(num#'a wordLang_prog) spt) <=>
       (!k n p. sptree_lookup k code = SOME (n,p) ==>
         wordConvs_no_install p)`;;

let no_install_find_code = prove
 (`!code dest args lsize args1 expr ps.
   no_install_code code /\ wordSem_find_code dest args code lsize =
     SOME (args1,expr,ps) ==> wordConvs_no_install expr`,
  CHEAT_TAC);;

let no_install_evaluate_const_code = prove
 (`!prog s result s1.
     wordSem_evaluate (prog,s) = (result,s1) /\
     wordConvs_no_install prog /\ no_install_code
       (wordSem_state_code s) ==> wordSem_state_code s =
       wordSem_state_code s1`,
  CHEAT_TAC);;

let get_code_labels_not_created = prove
 (`!p x. (x IN wordConvs_get_code_labels p) <=>
   (~(not_created_subprogs (\sp. ~(sp = (wordLang_Call NONE (SOME
     x) [] NONE)) /\ ~(sp = wordLang_LocValue 0 x)) p))`,
  CHEAT_TAC);;

let no_mt_code_def = new_definition
  `no_mt_code (code:(num#'a wordLang_prog) spt) <=>
   (!k n p. sptree_lookup k code = SOME (n,p) ==> no_mt p)`;;

let no_mt_find_code = prove
 (`!code dest args lsize args1 expr ps.
     wordSem_find_code dest args code lsize = SOME (args1,expr,ps) /\
     no_mt_code code ==>
     no_mt expr`,
  CHEAT_TAC);;


(*** permute_swap for no_install & no_alloc ***)

(* HOL4 wordPropsScript.sml:4792-4795: the overload PERM_STACK, which
   the port expands *)
let PERM_fromAList = prove
 (`!l1 l2.
     PERM l1 l2 /\
     ALL_DISTINCT (MAP FST l1) ==>
     fromAList l1 = fromAList l2`,
  CHEAT_TAC);;

let stack_size_perm = prove
 (`!l1 l2.
   ALL2 (\s1 s2. match (s1,s2) with
                              (StackFrame ss l env h,StackFrame ss'
                                l' env' h') ->
                              ss = ss' /\ h = h' /\ l = l' /\ PERM
                                env env' /\ ALL_DISTINCT (MAP FST env))
                                l1 l2 ==>
   stack_size l1 = stack_size l2`,
  CHEAT_TAC);;

let env_to_list_PERM = prove
 (`PERM (FST (env_to_list env perm)) (FST (env_to_list env perm'))`,
  CHEAT_TAC);;

let permute_swap_lemma2 = prove
 (`!prog st perm stack'.
   let (res,rst) = wordSem_evaluate (prog,st) in
     ~(res = SOME wordSem_Error) /\ no_alloc_code (wordSem_state_code
       st) /\ no_alloc prog /\
     no_install_code (wordSem_state_code st) /\ wordConvs_no_install
       prog /\
     ALL2 (\s1 s2. match (s1,s2) with
                              (StackFrame ss l env h,StackFrame ss'
                                l' env' h') ->
                              ss = ss' /\ h = h' /\ l = l' /\ PERM
                                env env' /\ ALL_DISTINCT (MAP FST env))
                                stack' (stack st) ==>
     (?perm' stack'.
       wordSem_evaluate (prog,stack_fupd (K stack')
         (wordSem_state_permute_fupd (K perm) st)) = (res,stack_fupd (K
         stack') (wordSem_state_permute_fupd (K perm') rst)) /\
       ALL2 (\s1 s2. match (s1,s2) with
                              (StackFrame ss l env h,StackFrame ss'
                                l' env' h') ->
                              ss = ss' /\ h = h' /\ l = l' /\ PERM
                                env env' /\ ALL_DISTINCT (MAP FST
                                env)) stack' (stack rst))`,
  CHEAT_TAC);;

(* HOL4 wordPropsScript.sml:5146-5166: a proof *)

(* HOL4 wordPropsScript.sml:5168: a proof *)

let permute_swap_lemma3 = prove
 (`!prog st perm stack'.
   let (res,rst) = wordSem_evaluate (prog,st) in
     ~(res = SOME wordSem_Error) /\ no_alloc_code (wordSem_state_code
       st) /\ no_alloc prog /\
     no_install_code (wordSem_state_code st) /\ wordConvs_no_install
       prog /\
     ALL (\st. match st with StackFrame _20 _21 vs handler ->
       ALL_DISTINCT (MAP FST vs)) (stack st) ==>
     (?perm' stack'.
       wordSem_evaluate (prog,wordSem_state_permute_fupd (K perm) st)
         = (res,stack_fupd (K stack') (wordSem_state_permute_fupd (K
         perm') rst)) /\
       ALL2 (\s1 s2. match (s1,s2) with
                              (StackFrame ss l env h,StackFrame ss'
                                l' env' h') ->
                              ss = ss' /\ h = h' /\ l = l' /\ PERM
                                env env' /\ ALL_DISTINCT (MAP FST
                                env)) stack' (stack rst))`,
  CHEAT_TAC);;

let word_cmp_Word_Word = prove
 (`wordSem_word_cmp cmp (wordLang_Word c) (wordLang_Word c') = SOME
  (wordSem_word_cmp cmp c c')`,
  CHEAT_TAC);;
add_simp word_cmp_Word_Word;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["Term";
   "comp";
   "precondition"];;

(* and the interface *)
let _ = unhide_overloads ();;
