(* ======================================================== *)
(*  closProps: ported from HOL4's
    compiler/backend/semantics/closPropsScript.sml
    A proof theory, with 35 definitions and 200 theorems.  Needed by
    14 files of the port.  *)
(* ======================================================== *)

(*
  Properties about closLang and its semantics
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/indexedLists.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["comp"];;

cake_hide_consts
  ["compile","backend_compile";
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
   "compile","word_to_word_compile"];;

let closProps_with_same_clock = cake_theorem "with_same_clock[simp]"
  (fun () ->
    `closSem_state_clock_fupd (K (closSem_state_clock s))
        (s:('c,'ffi)closSem_state) = s`)
  CHEAT_TAC;;

let closProps_dec_clock_code = cake_theorem "dec_clock_code"
  (fun () ->
    `closSem_state_code
        (closSem_dec_clock x y) = closSem_state_code y`)
  CHEAT_TAC;;

let closProps_dec_clock_ffi = cake_theorem "dec_clock_ffi"
  (fun () ->
    `state_ffi
        (closSem_dec_clock x y) = state_ffi y`)
  CHEAT_TAC;;

let dec_clock_compile_oracle =
  cake_theorem "dec_clock_compile_oracle[simp]"
  (fun () ->
    `closSem_state_compile_oracle
        (closSem_dec_clock n s) = closSem_state_compile_oracle s`)
  CHEAT_TAC;;

let dec_clock_compile = cake_theorem "dec_clock_compile[simp]"
  (fun () ->
    `closSem_state_compile
        (closSem_dec_clock n s) = closSem_state_compile s`)
  CHEAT_TAC;;

let list_to_v_EVERY_APPEND = cake_theorem "list_to_v_EVERY_APPEND"
  (fun () ->
    `!(x:closSem_v) y xs ys.
       v_to_list x = SOME xs /\
       v_to_list y = SOME ys /\
       (!t l. P (closSem_Block t l) <=> EVERY P l) /\
       P x /\ P y ==>
         P (list_to_v (xs ++ ys))`)
  CHEAT_TAC;;

let forall_sum = cake_theorem "forall_sum[local]"
  (fun () ->
    `(!x. P x) <=> (!a. P (INL a)) /\ (!b. P (INR b))`)
  CHEAT_TAC;;

let evaluate_better_ind = cake_theorem "evaluate_better_ind"
  (fun () ->
    `(!xs s1.
       (!ys s2. state_clock s2 <= closSem_state_clock s1 /\
         (state_clock s2 = closSem_state_clock s1 ==>
         closSem_exp3_alt_size ys < closSem_exp3_alt_size xs) ==> P1 ys
         s2) ==>
       (!args s2. state_clock s2 <= closSem_state_clock s1 /\
         (state_clock s2 = closSem_state_clock s1 ==> LENGTH args <
         closSem_exp3_alt_size xs) ==> P2 args s2) ==>
       P1 xs s1) /\
     (!args s1.
       (!ys s2. state_clock s2 <= closSem_state_clock s1 /\
         (state_clock s2 = closSem_state_clock s1 ==>
         closSem_exp3_alt_size ys < LENGTH args) ==> P1 ys s2) ==>
       (!args' s2. state_clock s2 <= closSem_state_clock s1 /\
         (state_clock s2 = closSem_state_clock s1 ==> LENGTH args' <
         LENGTH args) ==> P2 args' s2) ==>
       P2 args s1) ==>
     (!(xs:closLang_exp list) (s1:('c,'ffi)closSem_state). P1 xs
       s1) /\
     (!(args:closSem_v list) (s1:('c,'ffi)closSem_state). P2 args
       s1)`)
  CHEAT_TAC;;

let ref_rel_def = cake_define
  `closProps_ref_rel R x2 x3 =
        match (x2,x3) with
          (closSem_ValueArray vs,closSem_ValueArray ws) -> LIST_REL R
            vs ws
        | ((closSem_ByteArray as),(closSem_ByteArray bs)) -> as = bs
        | ((Thunk ma a),(Thunk mb b)) -> ma = mb /\ R a b
        | (_1,_2) -> F`;;
hol4_overload "ref_rel" "closProps_ref_rel";;

let ref_rel_simp = cake_theorem "ref_rel_simp[simp]"
  (fun () ->
    `(closProps_ref_rel R (closSem_ValueArray vs) y <=> (?ws. y =
  closSem_ValueArray ws /\ LIST_REL R vs ws)) /\
     (closProps_ref_rel R (closSem_ByteArray bs) y <=> y =
       closSem_ByteArray bs) /\
     (closProps_ref_rel R (Thunk m a) y <=> (?b. y = Thunk m b /\
       R a b))`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:158-161: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let code_locs_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`code_locs [] = []`;
   `code_locs (x :: y :: xs) =
         (let c1 = code_locs [x] in
         let c2 = code_locs (y :: xs) in
           c1 ++ c2)`;
   `code_locs [(Var _4 v:closLang_exp)] = []`;
   `code_locs [(If _6 x1 x2 x3:closLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs [x2] in
         let c3 = code_locs [x3] in
           c1 ++ c2 ++ c3)`;
   `code_locs [(Let _8 xs x2:closLang_exp)] =
         (let c1 = code_locs xs in
         let c2 = code_locs [x2] in
           c1 ++ c2)`;
   `code_locs [(Raise _10 x1:closLang_exp)] =
         code_locs [x1]`;
   `code_locs [(closLang_Tick _12 x1:closLang_exp)] =
         code_locs [x1]`;
   `code_locs [(closLang_Op _14 op xs:closLang_exp)] =
         code_locs xs`;
   `code_locs [(App _16 loc_opt x1 xs:closLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs xs in
             c1 ++ c2)`;
   `code_locs [closLang_Fn _17 loc_opt vs num_args x1] =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let c1 = code_locs [x1] in
           c1 ++ [loc])`;
   `code_locs [(Letrec _19 loc_opt vs fns x1:closLang_exp)] =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let c1 = code_locs (MAP SND fns) in
         let c2 = code_locs [x1] in
         c1 ++ GENLIST (\n. loc + 2 * n) (LENGTH fns) ++ c2)`;
   `code_locs [(Handle _21 x1 x2:closLang_exp)] =
         (let c1 = code_locs [x1] in
         let c2 = code_locs [x2] in
           c1 ++ c2)`;
   `code_locs [(closLang_Call _23 ticks dest xs:closLang_exp)] =
         code_locs xs`];;

let code_locs_cons = cake_theorem "code_locs_cons"
  (fun () ->
    `!x xs. code_locs (x :: xs) = code_locs [x] ++ code_locs xs`)
  CHEAT_TAC;;

let code_locs_append = cake_theorem "code_locs_append"
  (fun () ->
    `!l1 l2. code_locs (l1 ++ l2) = code_locs l1 ++ code_locs l2`)
  CHEAT_TAC;;

let code_locs_map = cake_theorem "code_locs_map"
  (fun () ->
    `!xs f. code_locs (MAP f xs) = FLAT (MAP (\x. code_locs [f x]) xs)`)
  CHEAT_TAC;;

let BIGUNION_MAP_code_locs_SND_SND =
  cake_theorem "BIGUNION_MAP_code_locs_SND_SND"
  (fun () ->
    `BIGUNION (set_of_list (MAP (set_of_list o code_locs o (\x. [SND
  (SND x)])) xs)) =
      set_of_list (code_locs (MAP (SND o SND) xs))`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* HOL4 closPropsScript.sml:229-232: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let contains_App_SOME_def = cake_define_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
  `contains_App_SOME max_app x2 =
        match x2 with
          [] -> F
        | (x :: y :: xs) ->
        contains_App_SOME max_app [x] \/
        contains_App_SOME max_app (y :: xs)
        | [(Var _25 v:closLang_exp)] -> F
        | [If _26 x1 x2 x3] ->
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app [x2] \/
        contains_App_SOME max_app [x3]
        | [Let _27 xs x2] ->
        contains_App_SOME max_app [x2] \/
        contains_App_SOME max_app xs
        | [Raise _28 x1] ->
        contains_App_SOME max_app [x1]
        | [closLang_Tick _29 x1] ->
        contains_App_SOME max_app [x1]
        | [closLang_Op _30 (ThunkOp ForceThunk) xs] ->
        max_app < 1 \/
        contains_App_SOME max_app xs
        | [closLang_Op _31 op xs] ->
        contains_App_SOME max_app xs
        | [App _32 loc_opt x1 x2] ->
        IS_SOME loc_opt \/ max_app < LENGTH x2 \/
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app x2
        | [closLang_Fn _33 loc vs num_args x1] ->
        contains_App_SOME max_app [x1]
        | [Letrec _34 loc vs fns x1] ->
        contains_App_SOME max_app (MAP SND fns) \/
        contains_App_SOME max_app [x1]
        | [Handle _35 x1 x2] ->
        contains_App_SOME max_app [x1] \/
        contains_App_SOME max_app [x2]
        | [closLang_Call _36 ticks dest xs] ->
        contains_App_SOME max_app xs`;;

let contains_App_SOME_EXISTS = cake_theorem "contains_App_SOME_EXISTS"
  (fun () ->
    `!ls max_app. contains_App_SOME max_app ls <=> EXISTS (\x.
  contains_App_SOME max_app [x]) ls`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:275-278: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let every_Fn_SOME_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`every_Fn_SOME [] <=> T`;
   `every_Fn_SOME (x :: y :: xs) <=>
         every_Fn_SOME [x] /\
         every_Fn_SOME (y :: xs)`;
   `every_Fn_SOME [(Var _38 v:closLang_exp)] <=> T`;
   `every_Fn_SOME [(If _40 x1 x2 x3:closLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME [x2] /\
         every_Fn_SOME [x3]`;
   `every_Fn_SOME [(Let _42 xs x2:closLang_exp)] <=>
         every_Fn_SOME [x2] /\
         every_Fn_SOME xs`;
   `every_Fn_SOME [(Raise _44 x1:closLang_exp)] <=>
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(closLang_Tick _46 x1:closLang_exp)] <=>
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(closLang_Op _48 op xs:closLang_exp)] <=>
         every_Fn_SOME xs`;
   `every_Fn_SOME [(App _50 loc_opt x1 x2:closLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME x2`;
   `every_Fn_SOME [closLang_Fn _51 loc_opt vs num_args x1] <=>
         IS_SOME loc_opt /\
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(Letrec _53 loc_opt vs fns x1:closLang_exp)] <=>
         IS_SOME loc_opt /\
         every_Fn_SOME (MAP SND fns) /\
         every_Fn_SOME [x1]`;
   `every_Fn_SOME [(Handle _55 x1 x2:closLang_exp)] <=>
         every_Fn_SOME [x1] /\
         every_Fn_SOME [x2]`;
   `every_Fn_SOME [(closLang_Call _57 ticks dest xs:closLang_exp)] <=>
         every_Fn_SOME xs`];;

let every_Fn_SOME_EVERY = cake_theorem "every_Fn_SOME_EVERY"
  (fun () ->
    `!ls. every_Fn_SOME ls <=> EVERY (\x. every_Fn_SOME [x]) ls`)
  CHEAT_TAC;;

let every_Fn_SOME_APPEND = cake_theorem "every_Fn_SOME_APPEND[simp]"
  (fun () ->
    `every_Fn_SOME (l1 ++ l2) <=> every_Fn_SOME l1 /\ every_Fn_SOME l2`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:327-330: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let every_Fn_vs_NONE_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`every_Fn_vs_NONE [] <=> T`;
   `every_Fn_vs_NONE (x :: y :: xs) <=>
         every_Fn_vs_NONE [x] /\
         every_Fn_vs_NONE (y :: xs)`;
   `every_Fn_vs_NONE [(Var _59 v:closLang_exp)] <=> T`;
   `every_Fn_vs_NONE [(If _61 x1 x2 x3:closLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE [x2] /\
         every_Fn_vs_NONE [x3]`;
   `every_Fn_vs_NONE [(Let _63 xs x2:closLang_exp)] <=>
         every_Fn_vs_NONE [x2] /\
         every_Fn_vs_NONE xs`;
   `every_Fn_vs_NONE [(Raise _65 x1:closLang_exp)] <=>
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(closLang_Tick _67 x1:closLang_exp)] <=>
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(closLang_Op _69 op xs:closLang_exp)] <=>
         every_Fn_vs_NONE xs`;
   `every_Fn_vs_NONE [(App _71 loc_opt x1 x2:closLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE x2`;
   `every_Fn_vs_NONE [closLang_Fn _72 loc vs_opt num_args x1] <=>
         IS_NONE vs_opt /\
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(Letrec _74 loc vs_opt fns x1:closLang_exp)] <=>
         IS_NONE vs_opt /\
         every_Fn_vs_NONE (MAP SND fns) /\
         every_Fn_vs_NONE [x1]`;
   `every_Fn_vs_NONE [(Handle _76 x1 x2:closLang_exp)] <=>
         every_Fn_vs_NONE [x1] /\
         every_Fn_vs_NONE [x2]`;
   `every_Fn_vs_NONE [(closLang_Call _78 ticks dest xs:closLang_exp)]
  <=>
         every_Fn_vs_NONE xs`];;

let every_Fn_vs_NONE_EVERY = cake_theorem "every_Fn_vs_NONE_EVERY"
  (fun () ->
    `!ls. every_Fn_vs_NONE ls <=> EVERY (\x. every_Fn_vs_NONE [x]) ls`)
  CHEAT_TAC;;

let IMP_every_Fn_vs_NONE_TAKE = cake_theorem "IMP_every_Fn_vs_NONE_TAKE"
  (fun () ->
    `every_Fn_vs_NONE ls ==> every_Fn_vs_NONE (TAKE n ls)`)
  CHEAT_TAC;;

let every_Fn_vs_NONE_APPEND =
  cake_theorem "every_Fn_vs_NONE_APPEND[simp]"
  (fun () ->
    `every_Fn_vs_NONE (l1 ++ l2) <=> every_Fn_vs_NONE l1 /\
  every_Fn_vs_NONE l2`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:386-389: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let every_Fn_vs_SOME_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size)`)
  CHEAT_TAC
  [`every_Fn_vs_SOME [] <=> T`;
   `every_Fn_vs_SOME (x :: y :: xs) <=>
         every_Fn_vs_SOME [x] /\
         every_Fn_vs_SOME (y :: xs)`;
   `every_Fn_vs_SOME [(Var _80 v:closLang_exp)] <=> T`;
   `every_Fn_vs_SOME [(If _82 x1 x2 x3:closLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME [x2] /\
         every_Fn_vs_SOME [x3]`;
   `every_Fn_vs_SOME [(Let _84 xs x2:closLang_exp)] <=>
         every_Fn_vs_SOME [x2] /\
         every_Fn_vs_SOME xs`;
   `every_Fn_vs_SOME [(Raise _86 x1:closLang_exp)] <=>
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(closLang_Tick _88 x1:closLang_exp)] <=>
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(closLang_Op _90 op xs:closLang_exp)] <=>
         every_Fn_vs_SOME xs`;
   `every_Fn_vs_SOME [(App _92 loc_opt x1 x2:closLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME x2`;
   `every_Fn_vs_SOME [closLang_Fn _93 loc vs_opt num_args x1] <=>
         IS_SOME vs_opt /\
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(Letrec _95 loc vs_opt fns x1:closLang_exp)] <=>
         IS_SOME vs_opt /\
         every_Fn_vs_SOME (MAP SND fns) /\
         every_Fn_vs_SOME [x1]`;
   `every_Fn_vs_SOME [(Handle _97 x1 x2:closLang_exp)] <=>
         every_Fn_vs_SOME [x1] /\
         every_Fn_vs_SOME [x2]`;
   `every_Fn_vs_SOME [(closLang_Call _99 ticks dest xs:closLang_exp)]
  <=>
         every_Fn_vs_SOME xs`];;

let every_Fn_vs_SOME_EVERY = cake_theorem "every_Fn_vs_SOME_EVERY"
  (fun () ->
    `!ls. every_Fn_vs_SOME ls <=> EVERY (\x. every_Fn_vs_SOME [x]) ls`)
  CHEAT_TAC;;

let every_Fn_vs_SOME_APPEND =
  cake_theorem "every_Fn_vs_SOME_APPEND[simp]"
  (fun () ->
    `every_Fn_vs_SOME (l1 ++ l2) <=> every_Fn_vs_SOME l1 /\
  every_Fn_vs_SOME l2`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:404-408: a theorem whose statement the
   port cannot state yet: exp3_size *)

(* HOL4 closPropsScript.sml:410-415: a theorem whose statement the
   port cannot state yet: exp1_size_rw *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:446-450: the tactic that proves the
   termination *)
let no_mti_def = cake_define_list_try (fun () ->
  `MEASURE closLang_exp_size`)
  [`no_mti (Var t n:closLang_exp) = T`;
   `no_mti (If t e1 e2 e3:closLang_exp) <=>
        no_mti e1 /\
        no_mti e2 /\
        no_mti e3`;
   `no_mti (Let t es e:closLang_exp) <=>
        EVERY no_mti es /\
        no_mti e`;
   `no_mti (Raise t e:closLang_exp) <=>
        no_mti e`;
   `no_mti (Handle t e1 e2:closLang_exp) <=>
        no_mti e1 /\
        no_mti e2`;
   `no_mti (closLang_Tick t e:closLang_exp) <=>
        no_mti e`;
   `no_mti (closLang_Call t ticks n es:closLang_exp) = F`;
   `no_mti (App t opt e es:closLang_exp) <=>
        LENGTH es = 1 /\ opt = NONE /\
        EVERY no_mti es /\
        no_mti e`;
   `no_mti (closLang_Fn t opt1 opt2 num_args e) <=>
        num_args = 1 /\ opt1 = NONE /\ opt2 = NONE /\
        no_mti e`;
   `no_mti (Letrec t opt1 opt2 funs e:closLang_exp) <=>
        no_mti e /\ opt1 = NONE /\ opt2 = NONE /\
        EVERY (\x. FST x = 1 /\ no_mti (SND x)) funs`;
   `no_mti (closLang_Op t op es) <=>
        EVERY no_mti es`];;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:473-476: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let fv_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
  [`fv n [] <=> F`;
   `fv n ((x:closLang_exp) :: y :: xs) <=>
         fv n [x] \/ fv n (y :: xs)`;
   `fv n [(Var _101 v:closLang_exp)] <=> (n = v)`;
   `fv n [(If _103 x1 x2 x3:closLang_exp)] <=>
         fv n [x1] \/ fv n [x2] \/ fv n [x3]`;
   `fv n [(Let _105 xs x2:closLang_exp)] <=>
         fv n xs \/ fv (n + LENGTH xs) [x2]`;
   `fv n [(Raise _107 x1:closLang_exp)] <=> fv n [x1]`;
   `fv n [(closLang_Tick _109 x1:closLang_exp)] <=> fv n [x1]`;
   `fv n [(closLang_Op _111 op xs:closLang_exp)] <=> fv n xs`;
   `fv n [(App _113 loc_opt x1 x2:closLang_exp)] <=>
         fv n [x1] \/ fv n x2`;
   `fv n [closLang_Fn _114 loc vs num_args x1] <=>
         fv (n + num_args) [x1]`;
   `fv n [(Letrec _116 loc vs fns x1:closLang_exp)] <=>
         EXISTS (\(num_args,x). fv (n + num_args + LENGTH fns)
           [x]) fns \/ fv (n + LENGTH fns) [x1]`;
   `fv n [(Handle _118 x1 x2:closLang_exp)] <=>
         fv n [x1] \/ fv (n + 1) [x2]`;
   `fv n [(closLang_Call _120 ticks dest xs:closLang_exp)] <=> fv n
  xs`];;

let fv_append = cake_theorem "fv_append[simp]"
  (fun () ->
    `!v l1. fv v (l1 ++ l2) <=> fv v l1 \/ fv v l2`)
  CHEAT_TAC;;

let fv_nil = cake_theorem "fv_nil[simp]"
  (fun () ->
    `fv v [] <=> F`)
  CHEAT_TAC;;

let fv1_def = cake_define
  `fv1 v e = fv v [e]`;;

(* HOL4 closPropsScript.sml:499-500: a theorem that HOL4 states as
   the value of an ML expression: fv1_intro *)
(* HOL4 closPropsScript.sml:501-502: a theorem that HOL4 states as
   the value of an ML expression: fv1_thm *)

let fv_cons = cake_theorem "fv_cons[simp]"
  (fun () ->
    `fv v (x :: xs) <=> fv1 v x \/ fv v xs`)
  CHEAT_TAC;;

let fv_exists = cake_theorem "fv_exists"
  (fun () ->
    `!ls. fv v ls <=> EXISTS (fv1 v) ls`)
  CHEAT_TAC;;

let fv_MAPi = cake_theorem "fv_MAPi"
  (fun () ->
    `!l x f. fv x (MAPi f l) <=> (?n. n < LENGTH l /\ fv x [f n (EL n
  l)])`)
  CHEAT_TAC;;

let fv_GENLIST_Var = cake_theorem "fv_GENLIST_Var"
  (fun () ->
    `!n. fv v (GENLIST (Var tra) n) <=> v < n`)
  CHEAT_TAC;;

let fv_REPLICATE = cake_theorem "fv_REPLICATE[simp]"
  (fun () ->
    `fv n (REPLICATE m e) <=> 0 < m /\ fv1 n e`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:536-543: a theorem that HOL4 states as
   the value of an ML expression: v_ind *)

let closProps_do_app_err = cake_theorem "do_app_err"
  (fun () ->
    `!op ls s e.
       do_app op ls s = Rerr e ==>
       (~(op = closLang_BlockOp closLang_Equal) ==> (?a. e =
         Rabort a))`)
  CHEAT_TAC;;

let closProps_Boolv_11 = cake_theorem "Boolv_11[simp]"
  (fun () ->
    `closSem_Boolv b1 = Boolv b2 <=> b1 = b2`)
  CHEAT_TAC;;

let do_eq_sym = cake_theorem "do_eq_sym"
  (fun () ->
    `(!x y. do_eq x y = do_eq y x) /\
     (!x y. do_eq_list x y = do_eq_list y x)`)
  CHEAT_TAC;;

let do_eq_list_rel = cake_theorem "do_eq_list_rel"
  (fun () ->
    `!l1 l2 l3 l4.
       LENGTH l1 = LENGTH l2 /\ LENGTH l3 = LENGTH l4 /\
       LIST_REL (\p1 p2. UNCURRY do_eq p1 = UNCURRY do_eq p2) (ZIP
         l1 l2) (ZIP l3 l4) ==>
       closSem_do_eq_list l1 l2 = do_eq_list l3 l4`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:590-597: ML code, not ported *)

(* HOL4 closPropsScript.sml:599-604: a proof *)

(* HOL4 closPropsScript.sml:606-607: a theorem that HOL4 states as
   the value of an ML expression: evaluate_LENGTH *)

let closProps_evaluate_IMP_LENGTH = cake_theorem "evaluate_IMP_LENGTH"
  (fun () ->
    `(closSem_evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs =
  LENGTH res)`)
  CHEAT_TAC;;

let evaluate_app_IMP_LENGTH = cake_theorem "evaluate_app_IMP_LENGTH"
  (fun () ->
    `(evaluate_app x1 x2 x3 x4 = (Rval res,s1)) ==> (LENGTH res = 1)`)
  CHEAT_TAC;;

let closProps_evaluate_SING = cake_theorem "evaluate_SING"
  (fun () ->
    `(closSem_evaluate ([x],s,env) = (Rval r,s2)) ==> (?r1. r = [r1])`)
  CHEAT_TAC;;

let closProps_evaluate_CONS = cake_theorem "evaluate_CONS"
  (fun () ->
    `closSem_evaluate (x :: xs,env,s) =
        (match closSem_evaluate ([x],env,s) with (Rval v,s2) ->
           (match closSem_evaluate (xs,env,s2) with (Rval vs,s1)
             -> (Rval (HD v :: vs),s1) | t -> t) | t -> t)`)
  CHEAT_TAC;;

let closProps_evaluate_APPEND = cake_theorem "evaluate_APPEND"
  (fun () ->
    `!xs ys env s.
       closSem_evaluate (xs ++ ys,env,s) =
         (match closSem_evaluate (xs,env,s) with
           (Rval vs,s2) ->
             (match closSem_evaluate (ys,env,s2) with
                (Rval ws,s1) -> (Rval (vs ++ ws),s1) | (Rerr
                  v8,s1) -> (Rerr v8,s1)) | (Rerr v10,s2) -> (Rerr
                  v10,s2))`)
  CHEAT_TAC;;

let closProps_evaluate_SNOC = cake_theorem "evaluate_SNOC"
  (fun () ->
    `!xs env s x.
        closSem_evaluate (SNOC x xs,env,s) =
        (match closSem_evaluate (xs,env,s) with (Rval vs,s2) ->
           (match closSem_evaluate ([x],env,s2) with (Rval v,s1)
             -> (Rval (vs ++ v),s1) | t -> t) | t -> t)`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:679-686: ML code, not ported *)

let do_install_const = cake_theorem "do_install_const"
  (fun () ->
    `closSem_do_install vs s = (res,s') ==> closSem_state_max_app
     s' = closSem_state_max_app s /\ state_ffi
     s' = state_ffi s`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:698-708: a proof *)

let evaluate_const = cake_theorem "evaluate_const"
  (fun () ->
    `(closSem_evaluate (xs,env,s) = (res,s1)) ==>
        (closSem_state_max_app s1 = closSem_state_max_app s)`)
  CHEAT_TAC;;

let evaluate_app_const = cake_theorem "evaluate_app_const"
  (fun () ->
    `(evaluate_app x1 x2 x3 x4 = (res,s1)) ==>
        (closSem_state_max_app s1 = closSem_state_max_app x4)`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:728-745: ML code, not ported *)

(* HOL4 closPropsScript.sml:747-823: a proof *)

let closProps_evaluate_code = cake_theorem "evaluate_code"
  (fun () ->
    `(closSem_evaluate (xs,env,s) = (res,s1)) ==>
        (?n. closSem_state_compile_oracle s1 = misc_shift_seq n
          (closSem_state_compile_oracle s) /\
            (let ls = FLAT (MAP (SND o SND) (GENLIST
              (closSem_state_compile_oracle s) n)) in closSem_state_code
            s1 = closSem_state_code s |++ ls /\
            ALL_DISTINCT (MAP FST ls) /\
            DISJOINT (FDOM (closSem_state_code s)) (set_of_list
              (MAP FST ls))))`)
  CHEAT_TAC;;

let evaluate_app_code = cake_theorem "evaluate_app_code"
  (fun () ->
    `(evaluate_app lopt f args s = (res,s1)) ==>
        (?n. closSem_state_compile_oracle s1 = misc_shift_seq n
          (closSem_state_compile_oracle s) /\
            (let ls = FLAT (MAP (SND o SND) (GENLIST
              (closSem_state_compile_oracle s) n)) in closSem_state_code
            s1 = closSem_state_code s |++ ls /\
            ALL_DISTINCT (MAP FST ls) /\
            DISJOINT (FDOM (closSem_state_code s)) (set_of_list
              (MAP FST ls))))`)
  CHEAT_TAC;;

let closProps_evaluate_mono = cake_theorem "evaluate_mono"
  (fun () ->
    `!xs env s1 vs s2.
       (closSem_evaluate (xs,env,s1) = (vs,s2)) ==>
         closSem_state_code
       s1 SUBMAP closSem_state_code s2`)
  CHEAT_TAC;;

let evaluate_MAP_Op_Const = cake_theorem "evaluate_MAP_Op_Const"
  (fun () ->
    `!f env s ls.
        closSem_evaluate (MAP (\x. closLang_Op tra (closLang_IntOp
          (closLang_Const (f x))) []) ls,env,s) =
        (Rval (MAP (closSem_Number o f) ls),s)`)
  CHEAT_TAC;;

let lookup_vars_NONE = cake_theorem "lookup_vars_NONE"
  (fun () ->
    `!vs. (lookup_vars vs env = NONE) <=> (?v. MEM v vs /\ LENGTH env
  <= v)`)
  CHEAT_TAC;;

let lookup_vars_SOME = cake_theorem "lookup_vars_SOME"
  (fun () ->
    `!vs env xs.
        (lookup_vars vs env = SOME xs) ==>
        (LENGTH vs = LENGTH xs)`)
  CHEAT_TAC;;

let lookup_vars_MEM = cake_theorem "lookup_vars_MEM"
  (fun () ->
    `!ys n x (env2:closSem_v list).
           (lookup_vars ys env2 = SOME x) /\ n < LENGTH ys ==>
           (EL n ys) < LENGTH env2 /\
           (EL n x = EL (EL n ys) env2)`)
  CHEAT_TAC;;

let closProps_clock_lemmas = cake_theorem "clock_lemmas"
  (fun () ->
    `!s. (state_clock_fupd (K (state_clock s)) s) = s`)
  CHEAT_TAC;;

let evaluate_app_rw = cake_theorem "evaluate_app_rw"
  (fun () ->
    `(!args loc_opt f s. ~(args = []) ==>
      evaluate_app loc_opt f args s =
        (match dest_closure (closSem_state_max_app s) loc_opt f
          args with NONE -> (Rerr (Rabort Rtype_error),s) | SOME
          (Partial_app v) ->
               (if state_clock s < LENGTH args then
                 (Rerr (Rabort Rtimeout_error),state_clock_fupd (K
                   0) s) else (Rval [v],closSem_dec_clock (LENGTH args)
                   s)) | SOME (Full_app exp env rest_args) ->
               (if state_clock s < (LENGTH args - LENGTH rest_args)
                 then
                 (Rerr (Rabort Rtimeout_error),state_clock_fupd (K
                   0) s) else
                 match closSem_evaluate
                   ([exp],env,closSem_dec_clock (LENGTH args - LENGTH
                   rest_args) s) with (Rval [v],s1) ->
                        evaluate_app loc_opt v rest_args s1 | res
                          -> res)))`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:931-934: a proof *)

(* HOL4 closPropsScript.sml:936-970: a theorem that HOL4 states as
   the value of an ML expression: EVERY_pure_correct *)

(* HOL4 closPropsScript.sml:972-974: a theorem that HOL4 states as
   the value of an ML expression: pure_correct *)

let evaluate_pure = cake_theorem "evaluate_pure"
  (fun () ->
    `closSem_evaluate (xs,env,s) = (res,(t:('c,'ffi)closSem_state)) /\
  EVERY pure xs ==>
     (?vs. res = Rval vs /\ t = s \/ res = Rerr (Rabort
       Rtype_error))`)
  CHEAT_TAC;;

let closProps_pair_lam_lem = cake_theorem "pair_lam_lem[local]"
  (fun () ->
    `!f v z. (let (x,y) = z in f x y) = v <=> (?x1 x2. z = (x1,x2) /\
  (f x1 x2 = v))`)
  CHEAT_TAC;;

let closProps_do_app_split_list = cake_theorem "do_app_split_list"
  (fun () ->
    `do_app op vs s = res <=>
     vs = [] /\ do_app op [] s = res \/
     (?v vs1. vs = v :: vs1 /\ do_app op (v :: vs1) s = res)`)
  CHEAT_TAC;;

let dest_closure_none_loc = cake_theorem "dest_closure_none_loc"
  (fun () ->
    `!max_app l cl vs v e env rest.
       (dest_closure max_app l cl vs = SOME (Partial_app v) ==> l =
         NONE) /\
       (dest_closure max_app l cl vs = SOME (Full_app e env rest)
         /\ ~(rest = []) ==> l = NONE)`)
  CHEAT_TAC;;

let is_closure_def = cake_define
  `is_closure x1 =
        match x1 with
          (Closure _126 _127 _128 _129 _130:closSem_v) -> T
        | (Recclosure _131 _132 _133 _134 _135) -> T
        | _136 -> F`;;

let clo_to_loc_def = cake_define_list
  [`clo_to_loc (Closure l _141 _142 _143 _144:closSem_v) = l`;
   `clo_to_loc (Recclosure l _148 _149 _150 i:closSem_v) =
  OPTION_MAP ((+) (2 * i)) l`];;

let clo_to_env_def = cake_define_list
  [`clo_to_env (Closure _155 _156 env _157 _158:closSem_v) = env`;
   `clo_to_env (Recclosure loc _161 env fns _162:closSem_v) =
       GENLIST (Recclosure loc [] env fns) (LENGTH fns) ++ env`];;

let clo_to_partial_args_def = cake_define_list
  [`clo_to_partial_args (Closure _167 args _168 _169 _170:closSem_v)
  = args`;
   `clo_to_partial_args (Recclosure _175 args _176 _177
  _178:closSem_v) = args`];;

let clo_add_partial_args_def = cake_define_list
  [`clo_add_partial_args args (Closure x1 args' x2 x3 x4:closSem_v) =
       Closure x1 (args ++ args') x2 x3 x4`;
   `clo_add_partial_args args (Recclosure x1 args' x2 x3 x4:closSem_v) =
       Recclosure x1 (args ++ args') x2 x3 x4`];;

let clo_to_num_params_def = cake_define_list
  [`clo_to_num_params (Closure _183 _184 _185 n _186:closSem_v) = n`;
   `clo_to_num_params (Recclosure _190 _191 _192 fns i:closSem_v) =
  FST (EL i fns)`];;

let rec_clo_ok_def = cake_define_list
  [`rec_clo_ok (Recclosure _196 _197 _198 fns i:closSem_v) <=> i <
  LENGTH fns`;
   `rec_clo_ok (Closure _204 _205 _206 _207 _208:closSem_v) <=> T`];;

let dest_closure_full_length = cake_theorem "dest_closure_full_length"
  (fun () ->
    `!max_app l v vs e args rest.
       dest_closure max_app l v vs = SOME (Full_app e args rest)
         ==>
       LENGTH (clo_to_partial_args v) < clo_to_num_params v /\
       LENGTH vs + LENGTH (clo_to_partial_args v) =
         clo_to_num_params v + LENGTH rest /\
       LENGTH args = clo_to_num_params v + LENGTH (clo_to_env v)`)
  CHEAT_TAC;;

let evaluate_app_clock_less = cake_theorem "evaluate_app_clock_less"
  (fun () ->
    `!loc_opt f args s1 vs s2.
       ~(args = []) /\
       evaluate_app loc_opt f args s1 = (Rval vs,s2) ==>
         state_clock
       s2 < state_clock s1`)
  CHEAT_TAC;;

let clo_add_partial_args_nil =
  cake_theorem "clo_add_partial_args_nil[simp]"
  (fun () ->
    `!x. is_closure x ==> clo_add_partial_args [] x = x`)
  CHEAT_TAC;;

let clo_can_apply_def = cake_define
  `clo_can_apply loc cl num_args <=>
     LENGTH (clo_to_partial_args cl) < clo_to_num_params cl /\
     rec_clo_ok cl /\
     (~(loc = NONE) ==>
      loc = clo_to_loc cl /\
      num_args = clo_to_num_params cl /\
      clo_to_partial_args cl = [])`;;

let check_closures_def = cake_define
  `check_closures cl cl' <=>
     (!loc num_args.
       clo_can_apply loc cl num_args ==> clo_can_apply loc cl'
         num_args)`;;

let dest_closure_partial_is_closure =
  cake_theorem "dest_closure_partial_is_closure"
  (fun () ->
    `dest_closure max_app l v vs = SOME (Partial_app v') ==>
     is_closure v'`)
  CHEAT_TAC;;

let is_closure_add_partial_args_nil =
  cake_theorem "is_closure_add_partial_args_nil"
  (fun () ->
    `is_closure v ==> (clo_add_partial_args [] v = v)`)
  CHEAT_TAC;;

let evaluate_app_clock0 = cake_theorem "evaluate_app_clock0"
  (fun () ->
    `state_clock
        s0 = 0 /\ ~(args = []) ==> ~(evaluate_app lopt r args s0
          = (Rval vs,s))`)
  CHEAT_TAC;;

let evaluate_app_clock0_timeout =
  cake_theorem "evaluate_app_clock0_timeout"
  (fun () ->
    `state_clock
        s0 = 0 /\ ~(args = []) /\
        evaluate_app lopt r args s0 = (Rerr e,s) /\ ~(e = Rabort
          Rtype_error) ==>
          e = Rabort Rtimeout_error`)
  CHEAT_TAC;;

let evaluate_app_clock_drop = cake_theorem "evaluate_app_clock_drop"
  (fun () ->
    `!args f lopt s0 s vs.
       evaluate_app lopt f args s0 = (Rval vs,s) ==> state_clock
       s + LENGTH args <= state_clock s0`)
  CHEAT_TAC;;

let dest_closure_is_closure = cake_theorem "dest_closure_is_closure"
  (fun () ->
    `dest_closure max_app lopt f vs = SOME r ==> is_closure f`)
  CHEAT_TAC;;

let stage_partial_app = cake_theorem "stage_partial_app"
  (fun () ->
    `is_closure c /\
     dest_closure max_app NONE v (rest ++ used) =
       SOME (Partial_app (clo_add_partial_args rest c)) ==>
     dest_closure max_app NONE c rest =
       SOME (Partial_app (clo_add_partial_args rest c))`)
  CHEAT_TAC;;

let dest_closure_full_addargs = cake_theorem "dest_closure_full_addargs"
  (fun () ->
    `dest_closure max_app NONE c vs = SOME (Full_app b env r) /\
     LENGTH more + LENGTH vs <= max_app ==>
     dest_closure max_app NONE c (more ++ vs) = SOME (Full_app b
       env (more ++ r))`)
  CHEAT_TAC;;

let closProps_evaluate_append = cake_theorem "evaluate_append"
  (fun () ->
    `!es1 es2 env s.
      closSem_evaluate (es1 ++ es2,env,s) =
        (match closSem_evaluate (es1,env,s) with (Rval vs1,s') ->
            (match closSem_evaluate (es2,env,s') with (Rval
              vs2,s'') -> (Rval (vs1 ++ vs2),s'') | x -> x) | x -> x)`)
  CHEAT_TAC;;

let evaluate_GENLIST_Var = cake_theorem "evaluate_GENLIST_Var"
  (fun () ->
    `!n env s.
     closSem_evaluate (GENLIST (Var tra) n,env,s) =
     (if n <= LENGTH env then
       (Rval (TAKE n env),s) else
       (Rerr (Rabort Rtype_error),s))`)
  CHEAT_TAC;;

let evaluate_length_imp = cake_theorem "evaluate_length_imp"
  (fun () ->
    `closSem_evaluate (es,env,s1) = (Rval vs,s2) ==> LENGTH es =
  LENGTH vs`)
  CHEAT_TAC;;

let evaluate_app_length_imp = cake_theorem "evaluate_app_length_imp"
  (fun () ->
    `evaluate_app l f args s = (Rval vs,s2) ==> LENGTH vs = 1`)
  CHEAT_TAC;;

let dest_closure_none_append = cake_theorem "dest_closure_none_append"
  (fun () ->
    `!max_app l f args1 args2.
      dest_closure max_app NONE f args2 = NONE ==>
      dest_closure max_app NONE f (args1 ++ args2) = NONE`)
  CHEAT_TAC;;

let dest_closure_none_append2 = cake_theorem "dest_closure_none_append2"
  (fun () ->
    `!max_app l f args1 args2.
       LENGTH args1 + LENGTH args2 <= max_app /\
       dest_closure max_app NONE f (args1 ++ args2) = NONE ==>
       dest_closure max_app NONE f args2 = NONE`)
  CHEAT_TAC;;

let dest_closure_rest_length = cake_theorem "dest_closure_rest_length"
  (fun () ->
    `dest_closure max_app NONE f args = SOME (Full_app e l rest) ==>
  LENGTH rest < LENGTH args`)
  CHEAT_TAC;;

let dest_closure_partial_twice =
  cake_theorem "dest_closure_partial_twice"
  (fun () ->
    `!max_app f args1 args2 cl res.
      LENGTH args1 + LENGTH args2 <= max_app /\
      dest_closure max_app NONE f (args1 ++ args2) = res /\
      dest_closure max_app NONE f args2 = SOME (Partial_app cl) ==>
      dest_closure max_app NONE cl args1 = res`)
  CHEAT_TAC;;

let evaluate_app_append = cake_theorem "evaluate_app_append"
  (fun () ->
    `!args2 f args1 s.
      LENGTH (args1 ++ args2) <= closSem_state_max_app s ==>
      evaluate_app NONE f (args1 ++ args2) s =
        (match evaluate_app NONE f args2 s with (Rval vs1,s1) ->
          evaluate_app NONE (HD vs1) args1 s1 | err -> err)`)
  CHEAT_TAC;;

let revnil = cake_theorem "revnil[local]"
  (fun () ->
    `[] = REVERSE l <=> l = []`)
  CHEAT_TAC;;

let dest_closure_full_maxapp = cake_theorem "dest_closure_full_maxapp"
  (fun () ->
    `dest_closure max_app NONE c vs = SOME (Full_app b env r) /\ ~(r =
  []) ==>
     LENGTH vs <= max_app`)
  CHEAT_TAC;;

let dest_closure_full_split' = cake_theorem "dest_closure_full_split'"
  (fun () ->
    `dest_closure max_app loc v vs = SOME (Full_app e env rest) ==>
     (?used.
      vs = rest ++ used /\ dest_closure max_app loc v used = SOME
        (Full_app e env []))`)
  CHEAT_TAC;;

let dest_closure_partial_split =
  cake_theorem "dest_closure_partial_split"
  (fun () ->
    `!max_app v1 vs v2 n.
      dest_closure max_app NONE v1 vs = SOME (Partial_app v2) /\
      n <= LENGTH vs ==>
      (?v3.
        dest_closure max_app NONE v1 (DROP n vs) = SOME
          (Partial_app v3) /\
        v2 = clo_add_partial_args (TAKE n vs) v3)`)
  CHEAT_TAC;;

let dest_closure_partial_split' =
  cake_theorem "dest_closure_partial_split'"
  (fun () ->
    `!max_app n v vs cl.
        dest_closure max_app NONE v vs = SOME (Partial_app cl) /\ n
          <= LENGTH vs ==>
        (?cl0 used rest.
           vs = rest ++ used /\ LENGTH rest = n /\
           dest_closure max_app NONE v used = SOME (Partial_app
             cl0) /\
           cl = clo_add_partial_args rest cl0)`)
  CHEAT_TAC;;

let dest_closure_NONE_Full_to_Partial =
  cake_theorem "dest_closure_NONE_Full_to_Partial"
  (fun () ->
    `dest_closure max_app NONE v (l1 ++ l2) = SOME (Full_app b env [])
  /\ ~(l1 = []) ==>
     (?cl. dest_closure max_app NONE v l2 = SOME (Partial_app cl)
       /\
          dest_closure max_app NONE cl l1 = SOME (Full_app b env
            []))`)
  CHEAT_TAC;;

let dec_clock_with_clock = cake_theorem "dec_clock_with_clock[simp]"
  (fun () ->
    `(state_clock_fupd (K y) (closSem_dec_clock n s)) =
  (state_clock_fupd (K y) s)`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:1512-1516: ML code, not ported *)

let do_app_ffi_error_IMP = cake_theorem "do_app_ffi_error_IMP"
  (fun () ->
    `do_app op vs s = Rerr (Rabort (Rffi_error f)) ==> (?i. op = FFI
  i)`)
  CHEAT_TAC;;

let do_app_add_to_clock = cake_theorem "do_app_add_to_clock"
  (fun () ->
    `(do_app op vs (state_clock_fupd (K (state_clock s + extra)) s) =
      map_result (\(v,s). (v,state_clock_fupd (K (state_clock s +
        extra)) s)) I (do_app op vs s))`)
  CHEAT_TAC;;

let do_install_add_to_clock = cake_theorem "do_install_add_to_clock"
  (fun () ->
    `closSem_do_install vs s = (Rval e,s') ==>
     closSem_do_install vs (state_clock_fupd (K (state_clock s +
       extra)) s) =
       (Rval e,state_clock_fupd (K (state_clock s' + extra)) s')`)
  CHEAT_TAC;;

let do_install_type_error_add_to_clock =
  cake_theorem "do_install_type_error_add_to_clock"
  (fun () ->
    `closSem_do_install vs s = (Rerr (Rabort Rtype_error),t) ==>
     closSem_do_install vs (state_clock_fupd (K (state_clock s +
       extra)) s) =
       (Rerr (Rabort Rtype_error),state_clock_fupd (K
         (state_clock t + extra)) t)`)
  CHEAT_TAC;;

let do_install_not_Rraise = cake_theorem "do_install_not_Rraise[simp]"
  (fun () ->
    `closSem_do_install vs s = (res,t) ==> ~(res = Rerr (Rraise r))`)
  CHEAT_TAC;;

let do_install_not_Rffi_error =
  cake_theorem "do_install_not_Rffi_error[simp]"
  (fun () ->
    `closSem_do_install vs s = (res,t) ==> ~(res = Rerr (Rabort
  (Rffi_error f)))`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:1565: the ML values that the definitions
   below antiquote *)

let closProps_evaluate_add_to_clock =
  cake_theorem "evaluate_add_to_clock"
  (fun () ->
    `(!p es env (s:('c,'ffi)closSem_state) r s'.
         p = (es,env,s) /\
         closSem_evaluate (es,env,s) = (r,s') /\ ~(r = Rerr (Rabort
           Rtimeout_error)) ==>
         closSem_evaluate (es,env,closSem_state_clock_fupd (K
           (closSem_state_clock s + extra)) s) =
           (r,state_clock_fupd (K (state_clock s' + extra)) s')) /\
     (!loc_opt v rest_args (s:('c,'ffi)closSem_state) r s'.
         evaluate_app loc_opt v rest_args s = (r,s') /\ ~(r = Rerr
           (Rabort Rtimeout_error)) ==>
         evaluate_app loc_opt v rest_args (closSem_state_clock_fupd
           (K (closSem_state_clock s + extra)) s) =
           (r,state_clock_fupd (K (state_clock s' + extra)) s'))`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:1622-1626: a theorem that HOL4 states as
   the value of an ML expression: evaluate_add_clock *)

let closProps_evaluate_add_clock_initial_state =
  cake_theorem "evaluate_add_clock_initial_state"
  (fun () ->
    `closSem_evaluate (es,env,closSem_initial_state ffi ma code co cc k)
  = (r,s') /\ ~(r = Rerr (Rabort Rtimeout_error)) ==>
     (!extra.
       closSem_evaluate (es,env,closSem_initial_state ffi ma code
         co cc (k + extra)) =
       (r,state_clock_fupd (K (state_clock s' + extra)) s'))`)
  CHEAT_TAC;;

let closProps_do_app_io_events_mono =
  cake_theorem "do_app_io_events_mono[local]"
  (fun () ->
    `do_app op vs s = Rval (v,s') ==> ffi_state_io_events (state_ffi
      s) <<= ffi_state_io_events (state_ffi s')`)
  CHEAT_TAC;;

let closProps_evaluate_io_events_mono =
  cake_theorem "evaluate_io_events_mono"
  (fun () ->
    `(!p. ffi_state_io_events (closSem_state_ffi ((SND (SND
  p)):('c,'ffi)closSem_state)) <<= ffi_state_io_events (state_ffi (SND
  (closSem_evaluate p)))) /\
     (!loc_opt v rest (s:('c,'ffi)closSem_state).
       ffi_state_io_events (closSem_state_ffi
       s) <<= ffi_state_io_events (state_ffi (SND (evaluate_app
         loc_opt v rest s))))`)
  CHEAT_TAC;;

let closProps_evaluate_io_events_mono_imp =
  cake_theorem "evaluate_io_events_mono_imp[local]"
  (fun () ->
    `closSem_evaluate (es,env,s) = (r,s') ==> ffi_state_io_events
  (state_ffi
       s) <<= ffi_state_io_events (state_ffi s')`)
  CHEAT_TAC;;

let closProps_with_clock_ffi = cake_theorem "with_clock_ffi[local]"
  (fun () ->
    `state_ffi
        (state_clock_fupd (K k) s) = state_ffi s`)
  CHEAT_TAC;;
(* HOL4 closPropsScript.sml:1669-1671: the ML values that the
   definitions below antiquote *)

(* HOL4 closPropsScript.sml:1673-1685: a proof *)

let closProps_evaluate_add_to_clock_io_events_mono =
  cake_theorem "evaluate_add_to_clock_io_events_mono"
  (fun () ->
    `(!p es env (s:('c,'ffi)closSem_state).
       p = (es,env,s) ==> ffi_state_io_events (state_ffi
       (SND (closSem_evaluate p))) <<= ffi_state_io_events
         (state_ffi
       (SND (closSem_evaluate (es,env,closSem_state_clock_fupd (K
         (closSem_state_clock s + extra)) s))))) /\
     (!l v r (s:('c,'ffi)closSem_state). ffi_state_io_events
       (state_ffi
       (SND (evaluate_app l v r s))) <<= ffi_state_io_events
         (state_ffi
       (SND (evaluate_app l v r (closSem_state_clock_fupd (K
         (closSem_state_clock s + extra)) s)))))`)
  CHEAT_TAC;;

let do_app_never_timesout = cake_theorem "do_app_never_timesout[simp]"
  (fun () ->
    `~(do_app op args s = Rerr (Rabort Rtimeout_error))`)
  CHEAT_TAC;;

let evaluate_timeout_clocks0 = cake_theorem "evaluate_timeout_clocks0"
  (fun () ->
    `(!v (s:('c,'ffi)closSem_state).
        closSem_evaluate v = (Rerr (Rabort Rtimeout_error),s) ==>
          closSem_state_clock s = 0) /\
     (!locopt v env (s:('c,'ffi)closSem_state) s'.
         evaluate_app locopt v env s = (Rerr (Rabort
           Rtimeout_error),s') ==> state_clock
         s' = 0)`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:1737: ML code, not ported *)

(* HOL4 closPropsScript.sml:1739-1744: a theorem whose statement the
   port cannot state yet: exp_size_MEM *)

let evaluate_eq_nil = cake_theorem "evaluate_eq_nil[simp]"
  (fun () ->
    `closSem_evaluate (es,env,s0) = (Rval [],s) <=> s0 = s /\ es = []`)
  CHEAT_TAC;;

(* finding the SetGlobal operations *)
let op_gbag_def = cake_define
  `closProps_op_gbag x1 =
      match x1 with
        closLang_GlobOp (closLang_SetGlobal n) -> BAG_INSERT n
          EMPTY_BAG
      | _209 -> EMPTY_BAG`;;
hol4_overload "op_gbag" "closProps_op_gbag";;

(* HOL4 closPropsScript.sml:1761-1765: a theorem whose statement the
   port cannot state yet: exp2_size_rw *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:1783-1786: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let set_globals_def = cake_define_list_try_tac (fun () ->
  `MEASURE (sum_size closLang_exp_size (list_size closLang_exp_size))`)
  CHEAT_TAC
  [`closProps_set_globals (Var _212 _213:closLang_exp) = EMPTY_BAG`;
   `closProps_set_globals (If _215 e1 e2 e3:closLang_exp) =
  (BAG_UNION) ((BAG_UNION) (closProps_set_globals e1)
  (closProps_set_globals e2)) (closProps_set_globals e3)`;
   `closProps_set_globals (Let _217 binds e:closLang_exp) =
  (BAG_UNION) (closProps_set_globals e) (closProps_elist_globals
  binds)`;
   `closProps_set_globals (Raise _219 e:closLang_exp) =
  closProps_set_globals e`;
   `closProps_set_globals (Handle _221 e1 e2:closLang_exp) =
  (BAG_UNION) (closProps_set_globals e1) (closProps_set_globals e2)`;
   `closProps_set_globals (closLang_Tick _223 e:closLang_exp) =
  closProps_set_globals e`;
   `closProps_set_globals (closLang_Call _227 _228 _229
  args:closLang_exp) = closProps_elist_globals args`;
   `closProps_set_globals (App _232 _233 f args:closLang_exp) =
  (BAG_UNION) (closProps_set_globals f) (closProps_elist_globals
  args)`;
   `closProps_set_globals (closLang_Fn _234 _235 _236 _237 bod) =
  closProps_set_globals bod`;
   `closProps_set_globals (Letrec _241 _242 _243 fbinds
  bod:closLang_exp) = (BAG_UNION) (closProps_set_globals bod)
  (closProps_elist_globals (MAP SND fbinds))`;
   `closProps_set_globals (closLang_Op _245 opn args:closLang_exp) =
  (BAG_UNION) (closProps_op_gbag opn) (closProps_elist_globals args)`;
   `closProps_elist_globals [] = EMPTY_BAG`;
   `closProps_elist_globals (e :: es) = (BAG_UNION)
  (closProps_set_globals e) (closProps_elist_globals es)`];;
hol4_overload "elist_globals" "closProps_elist_globals";;
hol4_overload "set_globals" "closProps_set_globals";;

(* {foo}sgc_free: foo is free of SetGlobal closures, meaning closures that
   include calls to SetGlobal, for
     foo = {(e)xpr, (v)alue, (r)esult, and (s)tate}
*)
(* HOL4 closPropsScript.sml:1792-1797: a theorem whose statement the
   port cannot state yet: v_size_lemma *)

(* value is setglobal-closure free *)
let _ = size_thms "closSem_v";;
(* HOL4 closPropsScript.sml:1809-1812: the tactic that proves the
   termination *)
let vsgc_free_def = cake_define_wf
  `MEASURE closSem_v_size`
  `vsgc_free x1 =
        match x1 with
          (Closure _248 VL1 VL2 _249 body:closSem_v) ->
        closProps_set_globals body = EMPTY_BAG /\
        EVERY vsgc_free VL1 /\ EVERY vsgc_free VL2
        | (Recclosure _250 VL1 VL2 bods _251) ->
        closProps_elist_globals (MAP SND bods) = EMPTY_BAG /\
        EVERY vsgc_free VL1 /\ EVERY vsgc_free VL2
        | (closSem_Block _252 VL) -> EVERY vsgc_free VL
        | _253 -> T`;;

(* HOL4 closPropsScript.sml:1814-1815: a theorem that HOL4 states as
   the value of an ML expression: vsgc_free_def *)

let vsgc_free_Unit = cake_theorem "vsgc_free_Unit[simp]"
  (fun () ->
    `vsgc_free closSem_Unit`)
  CHEAT_TAC;;

let vsgc_free_Boolv = cake_theorem "vsgc_free_Boolv[simp]"
  (fun () ->
    `vsgc_free (Boolv b)`)
  CHEAT_TAC;;

(* result is setglobal-closure free *)
let rsgc_free_def = cake_define
  `rsgc_free x1 =
        match x1 with
          Rval vs -> EVERY vsgc_free vs
        | (Rerr (Rabort _254)) -> T
        | (Rerr (Rraise v)) -> vsgc_free v`;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:1849-1852: the tactic that proves the
   termination *)
let esgc_free_def = cake_define_list_try (fun () ->
  `MEASURE closLang_exp_size`)
  [`closProps_esgc_free (Var _257 _258:closLang_exp) <=> T`;
   `closProps_esgc_free (If _260 e1 e2 e3:closLang_exp) <=>
  closProps_esgc_free e1 /\ closProps_esgc_free e2 /\
  closProps_esgc_free e3`;
   `closProps_esgc_free (Let _262 binds e:closLang_exp) <=> EVERY
  closProps_esgc_free binds /\ closProps_esgc_free e`;
   `closProps_esgc_free (Raise _264 e:closLang_exp) <=>
  closProps_esgc_free e`;
   `closProps_esgc_free (Handle _266 e1 e2:closLang_exp) <=>
  closProps_esgc_free e1 /\ closProps_esgc_free e2`;
   `closProps_esgc_free (closLang_Tick _268 e:closLang_exp) <=>
  closProps_esgc_free e`;
   `closProps_esgc_free (closLang_Call _272 _273 _274
  args:closLang_exp) <=> EVERY closProps_esgc_free args`;
   `closProps_esgc_free (App _277 _278 e args:closLang_exp) <=>
  closProps_esgc_free e /\ EVERY closProps_esgc_free args`;
   `closProps_esgc_free (closLang_Fn _279 _280 _281 _282 b) <=>
  closProps_set_globals b = EMPTY_BAG`;
   `closProps_esgc_free (Letrec _286 _287 _288 binds bod:closLang_exp)
  <=>
        closProps_elist_globals (MAP SND binds) = EMPTY_BAG /\
          closProps_esgc_free bod`;
   `closProps_esgc_free (closLang_Op _291 _292 args:closLang_exp)
  <=> EVERY closProps_esgc_free args`];;
hol4_overload "esgc_free" "closProps_esgc_free";;

(* HOL4 closPropsScript.sml:1854-1855: a theorem that HOL4 states as
   the value of an ML expression: esgc_free_def *)

(* state is setglobal-closure free *)
let ssgc_free_def = cake_define
  `ssgc_free (s:('c,'ffi)closSem_state) <=>
     (!n m e. FLOOKUP (closSem_state_code s) n = SOME (m,e) ==>
       closProps_set_globals e = EMPTY_BAG) /\
     (!n vl. FLOOKUP (closSem_state_refs s) n = SOME
       (closSem_ValueArray vl) ==> EVERY vsgc_free vl) /\
     (!n m v. FLOOKUP (closSem_state_refs s) n = SOME (Thunk m v) ==>
       vsgc_free v) /\
     (!v. MEM (SOME v) (closSem_state_globals s) ==> vsgc_free v) /\
     (!n exp aux. SND (closSem_state_compile_oracle s n) = (exp,aux)
       ==> EVERY closProps_esgc_free exp /\
          closProps_elist_globals (MAP (SND o SND) aux) =
            EMPTY_BAG)`;;

let ssgc_free_clockupd = cake_theorem "ssgc_free_clockupd[simp]"
  (fun () ->
    `ssgc_free (state_clock_fupd f s) = ssgc_free s`)
  CHEAT_TAC;;

let ssgc_free_dec_clock = cake_theorem "ssgc_free_dec_clock[simp]"
  (fun () ->
    `ssgc_free (closSem_dec_clock n s) <=> ssgc_free s`)
  CHEAT_TAC;;

let elglobals_EQ_EMPTY = cake_theorem "elglobals_EQ_EMPTY"
  (fun () ->
    `closProps_elist_globals l = EMPTY_BAG <=> (!e. MEM e l ==>
  closProps_set_globals e = EMPTY_BAG)`)
  CHEAT_TAC;;

let set_globals_empty_esgc_free =
  cake_theorem "set_globals_empty_esgc_free"
  (fun () ->
    `closProps_set_globals e = EMPTY_BAG ==> closProps_esgc_free e`)
  CHEAT_TAC;;

let elist_globals_append = cake_theorem "elist_globals_append"
  (fun () ->
    `!a b. closProps_elist_globals (a ++ b) = (BAG_UNION)
  (closProps_elist_globals a) (closProps_elist_globals b)`)
  CHEAT_TAC;;
let elist_globals_FOLDR = cake_theorem "elist_globals_FOLDR"
  (fun () ->
    `closProps_elist_globals es = ITLIST (BAG_UNION) (MAP
  closProps_set_globals es) EMPTY_BAG`)
  CHEAT_TAC;;

let elist_globals_reverse = cake_theorem "elist_globals_reverse"
  (fun () ->
    `!ls. closProps_elist_globals (REVERSE ls) =
  closProps_elist_globals ls`)
  CHEAT_TAC;;

(* generic do_app compile proof *)

let isClos_def = cake_define
  `closProps_isClos x1 =
      match x1 with
        (Closure x1 x2 x3 x4 x5:closSem_v) -> T
      | (Recclosure y1 y2 y3 y4 y5) -> T
      | _293 -> F`;;
hol4_overload "isClos" "closProps_isClos";;

let isClos_cases = cake_theorem "isClos_cases"
  (fun () ->
    `closProps_isClos x <=>
      (?x1 x2 x3 x4 x5. x = Closure x1 x2 x3 x4 x5) \/
      (?y1 y2 y3 y4 y5. x = Recclosure y1 y2 y3 y4 y5)`)
  CHEAT_TAC;;

let simple_val_rel_def = cake_define
  `closProps_simple_val_rel vr <=>
    (!x n. vr x (closSem_Number n) <=> x = closSem_Number n) /\
    (!x p n.
       vr x (closSem_Block n p) <=>
       (?xs. x = closSem_Block n xs /\ LIST_REL vr xs p)) /\
    (!x p. vr x (Word64 p) <=> x = Word64 p) /\
    (!x p. vr x (closSem_ByteVector p) <=> x = closSem_ByteVector p)
      /\
    (!x p b. vr x (closSem_RefPtr b p) <=> x = closSem_RefPtr b p) /\
    (!x5 x4 x3 x2 x1 x.
       vr x (Closure x1 x2 x3 x4 x5) ==> closProps_isClos x) /\
    (!y5 y4 y3 y2 y1 x.
       vr x (Recclosure y1 y2 y3 y4 y5) ==> closProps_isClos x)`;;
hol4_overload "simple_val_rel" "closProps_simple_val_rel";;

let simple_val_rel_alt = cake_theorem "simple_val_rel_alt[local]"
  (fun () ->
    `closProps_simple_val_rel vr <=>
        (!x n. vr x (closSem_Number n) <=> x = closSem_Number n) /\
        (!x p n.
           vr x (closSem_Block n p) <=>
           (?xs. x = closSem_Block n xs /\ LIST_REL vr xs p)) /\
        (!x p. vr x (Word64 p) <=> x = Word64 p) /\
        (!x p. vr x (closSem_ByteVector p) <=> x =
          closSem_ByteVector p) /\
        (!x p b. vr x (closSem_RefPtr b p) <=> x = closSem_RefPtr b
          p) /\
        (!x5 x4 x3 x2 x1 x.
           vr x (Closure x1 x2 x3 x4 x5) ==> closProps_isClos x) /\
        (!y5 y4 y3 y2 y1 x.
           vr x (Recclosure y1 y2 y3 y4 y5) ==> closProps_isClos x)
             /\
        (!b1 b2. vr (Boolv b1) (Boolv b2) <=> (b1 = b2)) /\
        (vr (closSem_Unit) (closSem_Unit) <=> T)`)
  CHEAT_TAC;;

let simple_state_rel_def = cake_define
  `closProps_simple_state_rel vr sr <=>
     (!s t ptr. FLOOKUP (closSem_state_refs t) ptr = NONE /\ sr s t
       ==>
                FLOOKUP (closSem_state_refs s) ptr = NONE) /\
     (!w t s ptr.
       FLOOKUP (closSem_state_refs t) ptr = SOME (closSem_ByteArray
         w) /\ sr s t ==>
       FLOOKUP (closSem_state_refs s) ptr = SOME (closSem_ByteArray
         w)) /\
     (!w (t:('c,'ffi)closSem_state) (s:('d,'ffi)closSem_state) ptr.
       FLOOKUP (closSem_state_refs t) ptr = SOME (closSem_ValueArray
         w) /\ sr s t ==>
       (?w1.
         FLOOKUP (closSem_state_refs s) ptr = SOME
           (closSem_ValueArray w1) /\
         LIST_REL vr w1 w)) /\
     (!m v t s ptr.
       FLOOKUP (closSem_state_refs t) ptr = SOME (Thunk m v) /\ sr s
         t ==>
       (?w.
         FLOOKUP (closSem_state_refs s) ptr = SOME (Thunk m w) /\
         vr w v)) /\
     (!s t. sr s t ==> closSem_state_ffi s = closSem_state_ffi t /\
       FDOM (closSem_state_refs s) = FDOM (closSem_state_refs t) /\
                       LIST_REL (OPTREL vr) (closSem_state_globals s)
                         (closSem_state_globals t)) /\
     (!f s t.
       sr s t ==> sr (closSem_state_ffi_fupd (K f) s)
                     (closSem_state_ffi_fupd (K f) t)) /\
     (!bs s t p.
       sr s t ==> sr (closSem_state_refs_fupd (K (closSem_state_refs
         s |+ (p,closSem_ByteArray bs))) s)
                     (closSem_state_refs_fupd (K (closSem_state_refs
                       t |+ (p,closSem_ByteArray bs))) t)) /\
     (!s t p xs ys.
       sr s t /\ LIST_REL vr xs ys ==>
       sr (closSem_state_refs_fupd (K (closSem_state_refs s |+
         (p,closSem_ValueArray xs))) s)
          (closSem_state_refs_fupd (K (closSem_state_refs t |+
            (p,closSem_ValueArray ys))) t)) /\
     (!s t p m v w.
       sr s t /\ vr v w ==>
       sr (closSem_state_refs_fupd (K (closSem_state_refs s |+
         (p,Thunk m v))) s)
          (closSem_state_refs_fupd (K (closSem_state_refs t |+
            (p,Thunk m w))) t)) /\
     (!s t xs ys.
       sr s t /\ LIST_REL (OPTREL vr) xs ys ==>
       sr (closSem_state_globals_fupd (K xs) s)
         (closSem_state_globals_fupd (K ys) t))`;;
hol4_overload "simple_state_rel" "closProps_simple_state_rel";;

let simple_state_rel_ffi = cake_theorem "simple_state_rel_ffi"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t ==> state_ffi s =
  state_ffi t`)
  CHEAT_TAC;;

let simple_state_rel_fdom = cake_theorem "simple_state_rel_fdom"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t ==> FDOM (state_refs
  s) = FDOM (state_refs t)`)
  CHEAT_TAC;;

let simple_state_rel_update_ffi =
  cake_theorem "simple_state_rel_update_ffi[local]"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t ==>
     sr (state_ffi_fupd (K f) s) (state_ffi_fupd (K f) t)`)
  CHEAT_TAC;;

let simple_state_rel_update_bytes =
  cake_theorem "simple_state_rel_update_bytes[local]"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t ==>
     sr (state_refs_fupd (K (state_refs s |+ (p,closSem_ByteArray
       bs))) s)
        (state_refs_fupd (K (state_refs t |+ (p,closSem_ByteArray
          bs))) t)`)
  CHEAT_TAC;;

let simple_state_rel_update_values =
  cake_theorem "simple_state_rel_update_values[local]"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t /\ LIST_REL vr xs ys ==>
     sr (state_refs_fupd (K (state_refs s |+ (p,closSem_ValueArray
       xs))) s)
        (state_refs_fupd (K (state_refs t |+
          (p,closSem_ValueArray ys))) t)`)
  CHEAT_TAC;;

let simple_state_rel_update_thunks =
  cake_theorem "simple_state_rel_update_thunks[local]"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t /\ vr v w ==>
     sr (state_refs_fupd (K (state_refs s |+ (p,Thunk m v))) s)
        (state_refs_fupd (K (state_refs t |+ (p,Thunk m w))) t)`)
  CHEAT_TAC;;

let simple_state_rel_update_globals =
  cake_theorem "simple_state_rel_update_globals[local]"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t /\ LIST_REL (OPTREL vr)
  xs ys ==>
     sr (closSem_state_globals_fupd (K xs) s)
       (closSem_state_globals_fupd (K ys) t)`)
  CHEAT_TAC;;

let simple_state_rel_get_global =
  cake_theorem "simple_state_rel_get_global[local]"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t /\ get_global n
  (closSem_state_globals t) = x ==>
     (match x with NONE -> get_global n (closSem_state_globals s)
       = NONE | SOME NONE -> get_global n (closSem_state_globals s) =
       SOME NONE | SOME (SOME y) -> (?x. get_global n
       (closSem_state_globals s) = SOME (SOME x) /\ vr x y))`)
  CHEAT_TAC;;

let list_to_v_INJ = cake_theorem "list_to_v_INJ[simp]"
  (fun () ->
    `!xs ys.
      list_to_v xs = list_to_v ys <=>
      xs = ys`)
  CHEAT_TAC;;

let isClos_IMP_v_to_list_NONE =
  cake_theorem "isClos_IMP_v_to_list_NONE[local]"
  (fun () ->
    `closProps_isClos x ==> v_to_list x = NONE`)
  CHEAT_TAC;;

let v_rel_to_list_ByteVector =
  cake_theorem "v_rel_to_list_ByteVector[local]"
  (fun () ->
    `closProps_simple_val_rel vr ==>
     (!lv x.
       vr x lv ==>
       (!wss. (v_to_list x = SOME (MAP closSem_ByteVector wss) <=>
              v_to_list lv = SOME (MAP closSem_ByteVector wss))))`)
  CHEAT_TAC;;

let v_rel_to_list_byte1 = cake_theorem "v_rel_to_list_byte1[local]"
  (fun () ->
    `closProps_simple_val_rel vr ==>
     (!y x.
       vr x y ==>
       (!ns. (v_to_list x = SOME (MAP (closSem_Number o (&)) ns))
         <=>
            (v_to_list y = SOME (MAP (closSem_Number o (&))
              ns))))`)
  CHEAT_TAC;;

let v_rel_to_list_byte2 = cake_theorem "v_rel_to_list_byte2[local]"
  (fun () ->
    `closProps_simple_val_rel vr ==>
     (!y x.
       vr x y ==>
       (!ns. (v_to_list x = SOME (MAP (closSem_Number o (&)) ns) /\
             EVERY (\n. n < 256) ns) <=>
            (v_to_list y = SOME (MAP (closSem_Number o (&)) ns) /\
             EVERY (\n. n < 256) ns)))`)
  CHEAT_TAC;;

let v_to_list_SOME = cake_theorem "v_to_list_SOME[local]"
  (fun () ->
    `closProps_simple_val_rel vr ==>
     (!y ys x.
       vr x y /\ v_to_list y = SOME ys ==>
       (?xs. LIST_REL vr xs ys /\ v_to_list x = SOME xs))`)
  CHEAT_TAC;;

let v_to_list_NONE = cake_theorem "v_to_list_NONE[local]"
  (fun () ->
    `closProps_simple_val_rel vr ==>
     (!y x. vr x y /\ v_to_list y = NONE ==>
           v_to_list x = NONE)`)
  CHEAT_TAC;;

let v_rel_do_eq = cake_theorem "v_rel_do_eq[local]"
  (fun () ->
    `closProps_simple_val_rel vr ==>
     (!y1 y2 x1 x2.
       vr x1 y1 /\ vr x2 y2 ==>
       do_eq x1 x2 = do_eq y1 y2) /\
     (!y1 y2 x1 x2.
       LIST_REL vr x1 y1 /\ LIST_REL vr x2 y2 ==>
       do_eq_list x1 x2 = do_eq_list y1 y2)`)
  CHEAT_TAC;;

let simple_state_rel_FLOOKUP_refs_IMP =
  cake_theorem "simple_state_rel_FLOOKUP_refs_IMP"
  (fun () ->
    `closProps_simple_state_rel vr sr /\ sr s t /\
      FLOOKUP (state_refs t) p = x ==>
      (match x with NONE -> FLOOKUP (state_refs s) p = NONE | SOME
        (closSem_ByteArray bs) -> FLOOKUP (state_refs s) p = SOME
        (closSem_ByteArray bs) | SOME (closSem_ValueArray vs) ->
          (?xs. FLOOKUP (state_refs s) p = SOME (closSem_ValueArray
            xs) /\ LIST_REL vr xs vs) | SOME (Thunk m w) ->
          (?v. FLOOKUP (state_refs s) p = SOME (Thunk m v) /\ vr
            v w))`)
  CHEAT_TAC;;

let refs_ffi_lemma = cake_theorem "refs_ffi_lemma[local]"
  (fun () ->
    `(closSem_state_ffi_fupd (K ffi') (closSem_state_refs_fupd (K refs')
  (s:('c,'ffi)closSem_state))) =
     (state_ffi_fupd (K ffi') (closSem_state_refs_fupd (K refs')
       s))`)
  CHEAT_TAC;;

let simple_val_rel_list = cake_theorem "simple_val_rel_list"
  (fun () ->
    `!x x1 xs vr.
       closProps_simple_val_rel vr /\
       vr x x1 /\
       v_to_list x1 = SOME xs ==>
       (?xs1.
       vr (list_to_v xs1) (list_to_v xs) /\
       v_to_list x = SOME xs1)`)
  CHEAT_TAC;;

let simple_val_rel_APPEND = cake_theorem "simple_val_rel_APPEND"
  (fun () ->
    `!xs1 ys1 xs2 ys2 vr.
     closProps_simple_val_rel vr /\
     vr (list_to_v xs1) (list_to_v xs2) /\
     vr (list_to_v ys1) (list_to_v ys2) ==>
     vr (list_to_v (xs1 ++ ys1)) (list_to_v (xs2 ++ ys2))`)
  CHEAT_TAC;;

let vr_list_NONE = cake_theorem "vr_list_NONE"
  (fun () ->
    `!x x1 vr.
     closProps_simple_val_rel vr /\
     vr x x1 /\
     v_to_list x1 = NONE ==>
     v_to_list x = NONE`)
  CHEAT_TAC;;

let vr_list_to_v = cake_theorem "vr_list_to_v"
  (fun () ->
    `!xs vys.
     closProps_simple_val_rel vr ==>
     vr vys (list_to_v xs) = (?ys. vys = (list_to_v ys) /\
       LIST_REL vr ys xs)`)
  CHEAT_TAC;;

(*TODO move to semanticPrimitivesProps*)
let result_rel_Rval2 = cake_theorem "result_rel_Rval2[local,simp]"
  (fun () ->
    `semanticPrimitivesProps_result_rel R1 R2 r (Rval v) = (?v'. (r =
  Rval v') /\ R1 v' v)`)
  CHEAT_TAC;;

(*TODO upstream to HOL*)
let PAIR_REL_SIMP = cake_theorem "PAIR_REL_SIMP[local,simp]"
  (fun () ->
    `(((RPROD R1 R2) n (c,d)) <=> (?x y. n = (x,y) /\ R1 x c /\ R2 y d))
  /\
     (((RPROD R1 R2) (a,b) m) <=> (?x y. m = (x,y) /\ R1 a x /\
       R2 b y))`)
  CHEAT_TAC;;

(*TODO remove once its in Typebase and automatically
 simp*)
(* HOL4 closPropsScript.sml:2294-2296: ML code, not ported *)
(* HOL4 closPropsScript.sml:2297: a theorem that HOL4 states as the
   value of an ML expression: v_case_const *)
(* HOL4 closPropsScript.sml:2298: a theorem that HOL4 states as the
   value of an ML expression: option_case_const *)
(* HOL4 closPropsScript.sml:2299: a theorem that HOL4 states as the
   value of an ML expression: list_case_const *)

let LIST_REL_REFL_EVERY = cake_theorem "LIST_REL_REFL_EVERY"
  (fun () ->
    `!l.
     LIST_REL R l l <=> EVERY (\x. R x x) l`)
  CHEAT_TAC;;

let POS_INT_EQ_NUM = cake_theorem "POS_INT_EQ_NUM"
  (fun () ->
    `(&0) <= (i:int) <=> (?n. i = &n)`)
  CHEAT_TAC;;

let simple_val_rel_Boolv = cake_theorem "simple_val_rel_Boolv"
  (fun () ->
    `closProps_simple_val_rel vr ==>
     (vr (Boolv b) v1 ==> v1 = Boolv b) /\
     (vr v1 (Boolv b) ==> v1 = Boolv b)`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:2325: ML code, not ported *)
let simple_val_rel_do_app_rev = cake_theorem "simple_val_rel_do_app_rev"
  (fun () ->
    `closProps_simple_val_rel vr /\ closProps_simple_state_rel vr sr ==>
     sr s (t:('c,'ffi)closSem_state) /\ LIST_REL vr xs ys ==>
     (match do_app opp ys t with Rerr err2 -> (?err1. do_app opp xs
       s = Rerr err1 /\
                            exc_rel vr err1 err2) | Rval (y,t1) ->
                              (?x s1. vr x y /\ sr s1 t1 /\
                             do_app opp xs s = Rval (x,s1)))`)
  CHEAT_TAC;;

let simple_val_rel_do_app = cake_theorem "simple_val_rel_do_app"
  (fun () ->
    `closProps_simple_val_rel vr /\ closProps_simple_state_rel vr sr ==>
      sr s (t:('c,'ffi)closSem_state) /\ LIST_REL vr xs ys ==>
      (match do_app opp xs s with Rerr err1 -> (?err2. do_app opp
        ys t = Rerr err2 /\
                             exc_rel vr err1 err2) | Rval (x,s1) ->
                               (?y t1. vr x y /\ sr s1 t1 /\
                              do_app opp ys t = Rval (y,t1)))`)
  CHEAT_TAC;;

(* generic do_install compile proof *)
let simple_compile_state_rel_def = cake_define
  `simple_compile_state_rel vr sr comp' cr <=>
     closProps_simple_state_rel vr sr /\
     (!(s:('c,'ffi)closSem_state) (t:('c,'ffi)closSem_state).
         sr s t ==> closSem_state_clock
         t = closSem_state_clock s /\ closSem_state_compile s =
           pure_cc comp' (closSem_state_compile t) /\
           closSem_state_compile_oracle
         t = pure_co comp' o closSem_state_compile_oracle s /\
         (!n exps res p aux. SND (closSem_state_compile_oracle s n) =
           (p,aux) ==>
             comp' (p,aux) = (exps,res) ==>
             res = [] /\ LENGTH exps = LENGTH p /\ cr p exps) /\
         (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
         (!n. sr (closSem_state_code_fupd (K (closSem_state_code s))
           (closSem_state_compile_oracle_fupd (K
                         (misc_shift_seq 1
                           (closSem_state_compile_oracle s)))
                           (closSem_state_clock_fupd (K n) s)))
              (closSem_state_code_fupd (K (closSem_state_code t))
                (closSem_state_compile_oracle_fupd (K
                         (misc_shift_seq 1
                           (closSem_state_compile_oracle t)))
                           (closSem_state_clock_fupd (K n) t)))))`;;

let simple_val_rel_v_to_bytes = cake_theorem "simple_val_rel_v_to_bytes"
  (fun () ->
    `closProps_simple_val_rel vr /\ vr x y ==> closSem_v_to_bytes x =
  closSem_v_to_bytes y`)
  CHEAT_TAC;;

let simple_val_rel_Word64_left =
  cake_theorem "simple_val_rel_Word64_left"
  (fun () ->
    `closProps_simple_val_rel vr ==> (!x w. vr (Word64 w) x = (x =
  Word64 w))`)
  CHEAT_TAC;;

let val_rel_to_words_lemma = cake_theorem "val_rel_to_words_lemma"
  (fun () ->
    `closProps_simple_val_rel vr ==> (!xs ys. LIST_REL vr xs ys ==>
       (!ns. (xs = MAP Word64 ns) = (ys = MAP Word64 ns)))`)
  CHEAT_TAC;;

let simple_val_rel_v_to_words = cake_theorem "simple_val_rel_v_to_words"
  (fun () ->
    `!x y. closProps_simple_val_rel vr /\ vr x y ==>
  closSem_v_to_words x = closSem_v_to_words y`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:2726: ML code, not ported *)

(* HOL4 closPropsScript.sml:2728: ML code, not ported *)
  (* CASE_TAC restricted to a particular type. Works in the proof below,
     but needs more code from BasicProvers to be robust. *)
(* HOL4 closPropsScript.sml:2731-2736: a proof *)

let simple_val_rel_do_install = cake_theorem "simple_val_rel_do_install"
  (fun () ->
    `!comp'. closProps_simple_val_rel vr /\ simple_compile_state_rel vr
  sr comp' cr ==>
       sr s (t:('c,'ffi)closSem_state) /\ LIST_REL vr xs ys ==>
       (match closSem_do_install xs s with (Rerr err1,s1) -> (?err2
         t1. closSem_do_install ys t = (Rerr err2,t1) /\
                              exc_rel vr err1 err2 /\ sr s1 t1) |
                                (Rval exps1,s1) -> (?exps2 t1. sr s1 t1
                                /\ (~(exps1 = [])) /\
                              cr exps1 exps2 /\
                              closSem_do_install ys t = (Rval
                                exps2,t1)))`)
  CHEAT_TAC;;

(* after do_install evaluate uses the LAST element, and this helps *)
(* FIXME move *)
let LIST_REL_LAST = cake_theorem "LIST_REL_LAST"
  (fun () ->
    `!P. LIST_REL P xs ys /\ (~(xs = [])) ==> P (LAST xs) (LAST ys)`)
  CHEAT_TAC;;

(* a generic semantics preservation lemma *)

let closProps_FST_EQ_LEMMA = cake_theorem "FST_EQ_LEMMA[local]"
  (fun () ->
    `FST x = y <=> (?y1. x = (y,y1))`)
  CHEAT_TAC;;

let initial_state_max_app = cake_theorem "initial_state_max_app[simp]"
  (fun () ->
    `closSem_state_max_app
        (closSem_initial_state ffi max_app code co cc k) =
          max_app`)
  CHEAT_TAC;;

let eval_sim_def = cake_define
  `closProps_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2
  rel allow_fail =
     (!k res1 s2.
       closSem_evaluate (es1,[],closSem_initial_state ffi max_app
         code1 co1 cc1 k) = (res1,s2) /\
       (allow_fail \/ ~(res1 = Rerr (Rabort Rtype_error))) /\
       rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
       (?ck res2 t2.
         closSem_evaluate (es2,[],
           closSem_initial_state ffi max_app code2 co2 cc2 (k + ck))
             = (res2,t2) /\
         semanticPrimitivesProps_result_rel (\x y. T) (\x y. T)
           res1 res2 /\ state_ffi s2 = state_ffi t2))`;;
hol4_overload "eval_sim" "closProps_eval_sim";;

(* HOL4 closPropsScript.sml:2800-2804: ML code, not ported *)

let initial_state_with_clock =
  cake_theorem "initial_state_with_clock[local]"
  (fun () ->
    `(state_clock_fupd (K (state_clock
       (closSem_initial_state ffi ma code co cc k) + ck))
         (closSem_initial_state ffi ma code co cc k)) =
     closSem_initial_state ffi ma code co cc (k + ck)`)
  CHEAT_TAC;;

let IMP_semantics_eq = cake_theorem "IMP_semantics_eq"
  (fun () ->
    `closProps_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2
  rel F /\ ~(closSem_semantics (ffi:'ffi ffi_state) max_app code1 co1
  cc1 es1 = ffi_Fail) ==>
     rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
     closSem_semantics ffi max_app code2 co2 cc2 es2 =
     closSem_semantics ffi max_app code1 co1 cc1 es1`)
  CHEAT_TAC;;

let IMP_semantics_eq_no_fail = cake_theorem "IMP_semantics_eq_no_fail"
  (fun () ->
    `closProps_eval_sim ffi max_app code1 co1 cc1 es1 code2 co2 cc2 es2
  rel T ==>
     rel code1 co1 cc1 es1 code2 co2 cc2 es2 ==>
     closSem_semantics ffi max_app code2 co2 cc2 es2 =
     closSem_semantics ffi max_app code1 co1 cc1 es1`)
  CHEAT_TAC;;

let adj_orac_rel_def = cake_define
  `closProps_adj_orac_rel cc f s1 s2 <=>
      (!n x y. closSem_state_compile_oracle s1 n = (x,y) ==>
         OPTION_MAP (I ## (I ## f)) (closSem_state_compile s1 x y) =
           cc (f x) y) /\
      s2 = mk_closSem_state (closSem_state_globals s1) (state_refs
        s1) (state_ffi s1) (state_clock s1) cc ((f ## I) o
        closSem_state_compile_oracle s1) (closSem_state_code s1)
        (closSem_state_max_app s1)`;;
hol4_overload "adj_orac_rel" "closProps_adj_orac_rel";;

let closProps_do_install_adj_orac = cake_theorem "do_install_adj_orac"
  (fun () ->
    `closSem_do_install xs z1 = (r,s1) /\
     closProps_adj_orac_rel cc f z1 z2 /\ ~(r = Rerr (Rabort
       Rtype_error)) ==>
     (?s2.
       closSem_do_install xs z2 = (r,s2) /\
       closProps_adj_orac_rel cc f s1 s2)`)
  CHEAT_TAC;;

let do_app_lemma_simp = cake_theorem "do_app_lemma_simp[local]"
  (fun () ->
    `(exc_rel (=) err1 err2 <=> err1 = err2) /\
       LIST_REL (=) xs xs /\
       closProps_simple_state_rel (=) (closProps_adj_orac_rel cc f)
         /\
       closProps_simple_val_rel (=)`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:3178-3184: ML code, not ported *)

let do_app_adj_orac_Rerr = cake_theorem "do_app_adj_orac_Rerr"
  (fun () ->
    `!op xs s1 s2 r.
      do_app op xs s1 = Rerr r /\
      closProps_adj_orac_rel cc f s1 s2 ==>
      do_app op xs s2 = Rerr r`)
  CHEAT_TAC;;

let do_app_adj_orac_Rval = cake_theorem "do_app_adj_orac_Rval"
  (fun () ->
    `!op xs s1 s2 r z1.
      do_app op xs s1 = Rval (r,z1) /\
      closProps_adj_orac_rel cc f s1 s2 ==>
      (?z2.
      do_app op xs s2 = Rval (r,z2) /\
      closProps_adj_orac_rel cc f z1 z2)`)
  CHEAT_TAC;;

let closProps_evaluate_adj_orac = cake_theorem "evaluate_adj_orac"
  (fun () ->
    `(!p (z1) r s1 s2 (z2).
      closSem_evaluate p = (r,s1) /\
      SND (SND p) = z1 /\ ~(r = Rerr (Rabort Rtype_error)) /\
      closProps_adj_orac_rel cc f z1 z2 ==>
      (?s2.
      closSem_evaluate (FST p,FST (SND p),z2) = (r,s2) /\
      closProps_adj_orac_rel cc f s1 s2)) /\
     (!w x y (z1) r s1 s2 (z2).
      evaluate_app w x y z1 = (r,s1) /\ ~(r = Rerr (Rabort
        Rtype_error)) /\
      closProps_adj_orac_rel cc f z1 z2 ==>
      (?s2.
      evaluate_app w x y z2 = (r,s2) /\
      closProps_adj_orac_rel cc f s1 s2))`)
  CHEAT_TAC;;

let semantics_adj_orac = cake_theorem "semantics_adj_orac"
  (fun () ->
    `~(closSem_semantics ffi max_app code co cc_x es = ffi_Fail) /\
        (co_x = (f ## I) o co) /\
        (!n x y. co n = (x,y) ==> cc (f x) y = OPTION_MAP (I ## (I
          ## f)) (cc_x x y)) ==>
        closSem_semantics ffi max_app code co_x cc es =
        closSem_semantics ffi max_app code co cc_x es`)
  CHEAT_TAC;;

let semantics_CURRY_I_gen = cake_theorem "semantics_CURRY_I_gen"
  (fun () ->
    `(!n x y. co n = (x,y) ==> cc_x x y = state_cc (CURRY I) cc x y) ==>
  ~(closSem_semantics ffi max_app code co cc_x es = ffi_Fail) ==>
     closSem_semantics ffi max_app code (state_co (CURRY I) co) cc
       es =
     closSem_semantics ffi max_app code co cc_x es`)
  CHEAT_TAC;;

let closProps_semantics_CURRY_I = cake_theorem "semantics_CURRY_I"
  (fun () ->
    `~(closSem_semantics ffi max_app code co (state_cc (CURRY I) cc) es
  = ffi_Fail) ==>
        closSem_semantics ffi max_app code (state_co (CURRY I) co)
          cc es =
        closSem_semantics ffi max_app code co (state_cc (CURRY I)
          cc) es`)
  CHEAT_TAC;;

let semantics_nil = cake_theorem "semantics_nil[simp]"
  (fun () ->
    `closSem_semantics ffi maxapp code co cc [] = ffi_Terminate
  ffi_Success (ffi_state_io_events ffi)`)
  CHEAT_TAC;;

let find_code_SUBMAP = cake_theorem "find_code_SUBMAP"
  (fun () ->
    `closSem_find_code dest vs code1 = SOME p /\ code1 SUBMAP code2 ==>
     closSem_find_code dest vs code2 = SOME p`)
  CHEAT_TAC;;

let SUBMAP_rel_def = cake_define
  `SUBMAP_rel z1 z2 <=>
     z2 = closSem_state_code_fupd (K (closSem_state_code z2)) z1 /\
       closSem_state_code z1 SUBMAP closSem_state_code z2 /\
     oracle_monotonic (set_of_list o MAP FST o SND o SND) (<)
         (FDOM (closSem_state_code z2))
           (closSem_state_compile_oracle z1)`;;

let find_code_SUBMAP_rel = cake_theorem "find_code_SUBMAP_rel"
  (fun () ->
    `closSem_find_code dest vs (closSem_state_code s1) = SOME p /\
  SUBMAP_rel s1 s2 ==>
     closSem_find_code dest vs (closSem_state_code s2) = SOME p`)
  CHEAT_TAC;;

let SUBMAP_rel_EX = cake_theorem "SUBMAP_rel_EX"
  (fun () ->
    `SUBMAP_rel z1 z2 ==> (?code. z2 = closSem_state_code_fupd (K
  code) z1 /\ closSem_state_code z1 SUBMAP code)`)
  CHEAT_TAC;;

let do_install_SUBMAP = cake_theorem "do_install_SUBMAP"
  (fun () ->
    `closSem_do_install xs z1 = (r,s1) /\ ~(r = Rerr (Rabort
  Rtype_error)) /\
     SUBMAP_rel z1 z2 ==>
     (?s2. closSem_do_install xs z2 = (r,s2) /\ SUBMAP_rel s1 s2)`)
  CHEAT_TAC;;

let closProps_do_app_lemma_simp =
  cake_theorem "do_app_lemma_simp[local]"
  (fun () ->
    `(exc_rel (=) err1 err2 <=> err1 = err2) /\
     LIST_REL (=) xs xs /\
     closProps_simple_state_rel (=) SUBMAP_rel /\
     closProps_simple_val_rel (=)`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:3396-3402: ML code, not ported *)

let do_app_SUBMAP_Rerr = cake_theorem "do_app_SUBMAP_Rerr"
  (fun () ->
    `!op xs s1 s2 r.
      do_app op xs s1 = Rerr r /\
      SUBMAP_rel s1 s2 ==>
      do_app op xs s2 = Rerr r`)
  CHEAT_TAC;;

let do_app_SUBMAP_Rval = cake_theorem "do_app_SUBMAP_Rval"
  (fun () ->
    `!op xs s1 s2 r z1.
      do_app op xs s1 = Rval (r,z1) /\
      SUBMAP_rel s1 s2 ==>
      (?z2.
      do_app op xs s2 = Rval (r,z2) /\
      SUBMAP_rel z1 z2)`)
  CHEAT_TAC;;

let SUBMAP_refs_clocks_eqs =
  cake_theorem "SUBMAP_refs_clocks_eqs[local]"
  (fun () ->
    `SUBMAP_rel s1 s2 ==> state_refs s1 = state_refs s2 /\ state_clock
  s1 = state_clock s2`)
  CHEAT_TAC;;

let SUBMAP_dec_clock = cake_theorem "SUBMAP_dec_clock[local]"
  (fun () ->
    `SUBMAP_rel s1 s2 ==> SUBMAP_rel (closSem_dec_clock 1 s1)
  (closSem_dec_clock 1 s2)`)
  CHEAT_TAC;;

let evaluate_code_SUBMAP = cake_theorem "evaluate_code_SUBMAP"
  (fun () ->
    `(!p x y (z1:('c,'ffi)closSem_state) r s1 s2
  (z2:('c,'ffi)closSem_state).
      p = (x,y,z1) /\
      closSem_evaluate (x,y,z1) = (r,s1) /\ ~(r = Rerr (Rabort
        Rtype_error)) /\
      SUBMAP_rel z1 z2 ==>
      (?s2.
      closSem_evaluate (x,y,z2) = (r,s2) /\
      SUBMAP_rel s1 s2)) /\
     (!w x y (z1:('c,'ffi)closSem_state) r s1 s2
       (z2:('c,'ffi)closSem_state).
      evaluate_app w x y z1 = (r,s1) /\ ~(r = Rerr (Rabort
        Rtype_error)) /\
      SUBMAP_rel z1 z2 ==>
      (?s2.
      evaluate_app w x y z2 = (r,s2) /\
      SUBMAP_rel s1 s2))`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3554-3560: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let obeys_max_app_def = cake_define_list_try_tac (fun () ->
  `MEASURE (closLang_exp_size o SND)`)
  CHEAT_TAC
  [`obeys_max_app m (Var _296 _297:closLang_exp) <=> T`;
   `obeys_max_app m (If _299 e1 e2 e3:closLang_exp) <=> obeys_max_app
  m e1 /\ obeys_max_app m e2 /\ obeys_max_app m e3`;
   `obeys_max_app m (Let _301 es e:closLang_exp) <=> EVERY
  (obeys_max_app m) es /\ obeys_max_app m e`;
   `obeys_max_app m (Raise _303 e:closLang_exp) <=> obeys_max_app m e`;
   `obeys_max_app m (Handle _305 e1 e2:closLang_exp) <=>
  obeys_max_app m e1 /\ obeys_max_app m e2`;
   `obeys_max_app m (closLang_Tick _307 e:closLang_exp) <=>
  obeys_max_app m e`;
   `obeys_max_app m (closLang_Call _311 _312 _313 es:closLang_exp)
  <=> EVERY (obeys_max_app m) es`;
   `obeys_max_app m (App _316 _317 e es:closLang_exp) <=> LENGTH es
  <= m /\ obeys_max_app m e /\ EVERY (obeys_max_app m) es`;
   `obeys_max_app m (closLang_Fn _318 _319 _320 _321 e) <=>
  obeys_max_app m e`;
   `obeys_max_app m (Letrec _325 _326 _327 es e:closLang_exp) <=>
  EVERY (obeys_max_app m) (MAP SND es) /\ obeys_max_app m e`;
   `obeys_max_app m (closLang_Op _330 _331 es:closLang_exp) <=>
  EVERY (obeys_max_app m) es`];;

(* HOL4 closPropsScript.sml:3562-3564: a theorem that HOL4 states as
   the value of an ML expression: obeys_max_app_def *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3578-3584: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let no_Labels_def = cake_define_list_try_tac (fun () ->
  `MEASURE closLang_exp_size`)
  CHEAT_TAC
  [`no_Labels (Var _334 _335:closLang_exp) <=> T`;
   `no_Labels (If _337 e1 e2 e3:closLang_exp) <=> no_Labels e1 /\
  no_Labels e2 /\ no_Labels e3`;
   `no_Labels (Let _339 es e:closLang_exp) <=> EVERY no_Labels es /\
  no_Labels e`;
   `no_Labels (Raise _341 e:closLang_exp) <=> no_Labels e`;
   `no_Labels (Handle _343 e1 e2:closLang_exp) <=> no_Labels e1 /\
  no_Labels e2`;
   `no_Labels (closLang_Tick _345 e:closLang_exp) <=> no_Labels e`;
   `no_Labels (closLang_Call _349 _350 _351 es:closLang_exp) <=>
  EVERY no_Labels es`;
   `no_Labels (App _354 _355 e es:closLang_exp) <=> no_Labels e /\
  EVERY no_Labels es`;
   `no_Labels (closLang_Fn _356 _357 _358 _359 e) <=> no_Labels e`;
   `no_Labels (Letrec _363 _364 _365 es e:closLang_exp) <=> EVERY
  no_Labels (MAP SND es) /\ no_Labels e`;
   `no_Labels (closLang_Op _367 op es:closLang_exp) <=> (!n. ~(op =
  closLang_Label n)) /\ EVERY no_Labels es`];;

(* HOL4 closPropsScript.sml:3586-3588: a theorem that HOL4 states as
   the value of an ML expression: no_Labels_def *)

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3631-3634: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let app_call_dests_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size closLang_exp_size o SND)`)
  CHEAT_TAC
  [`app_call_dests opt [] = {}`;
   `app_call_dests opt (x :: y :: xs) =
         (let c1 = app_call_dests opt [x] in
         let c2 = app_call_dests opt (y :: xs) in
           c1 UNION c2)`;
   `app_call_dests opt [(Var _369 v:closLang_exp)] = {}`;
   `app_call_dests opt [(If _371 x1 x2 x3:closLang_exp)] =
         (let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt [x2] in
         let c3 = app_call_dests opt [x3] in
           c1 UNION c2 UNION c3)`;
   `app_call_dests opt [(Let _373 xs x2:closLang_exp)] =
         (let c1 = app_call_dests opt xs in
         let c2 = app_call_dests opt [x2] in
           c1 UNION c2)`;
   `app_call_dests opt [(Raise _375 x1:closLang_exp)] =
         app_call_dests opt [x1]`;
   `app_call_dests opt [(closLang_Tick _377 x1:closLang_exp)] =
         app_call_dests opt [x1]`;
   `app_call_dests opt [(closLang_Op _379 op xs:closLang_exp)] =
         app_call_dests opt xs`;
   `app_call_dests opt [(App _383 loc_opt x1 xs:closLang_exp)] =
         (let ll = (if opt = SOME T then {} else
                    match loc_opt with SOME n -> {n} | _384 -> {})
                      in
         let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt xs in
             ll UNION c1 UNION c2)`;
   `app_call_dests opt [closLang_Fn _385 loc_opt vs num_args x1] =
         (let c1 = app_call_dests opt [x1] in c1)`;
   `app_call_dests opt [(Letrec _387 loc_opt vs fns x1:closLang_exp)] =
         (let c1 = app_call_dests opt (MAP SND fns) in
         let c2 = app_call_dests opt [x1] in
         c1 UNION c2)`;
   `app_call_dests opt [(Handle _389 x1 x2:closLang_exp)] =
         (let c1 = app_call_dests opt [x1] in
         let c2 = app_call_dests opt [x2] in
           c1 UNION c2)`;
   `app_call_dests opt [(closLang_Call _391 ticks dest xs:closLang_exp)]
  =
         (if opt = SOME F then app_call_dests opt xs else
           dest INSERT app_call_dests opt xs)`];;

(* HOL4 closPropsScript.sml:3636-3637: a theorem that HOL4 states as
   the value of an ML expression: app_call_dests_def *)

(* HOL4 closPropsScript.sml:3639: the overload call_dests, which the
   port expands *)
(* HOL4 closPropsScript.sml:3640: the overload app_dests, which the
   port expands *)
(* HOL4 closPropsScript.sml:3641: the overload any_dests, which the
   port expands *)

(* HOL4 closPropsScript.sml:3643: ML code, not ported *)

let app_call_dests_cons = cake_theorem "app_call_dests_cons"
  (fun () ->
    `!y x. app_call_dests opt (x :: y) =
           app_call_dests opt [x] UNION app_call_dests opt y`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:3652-3653: a theorem that HOL4 states as
   the value of an ML expression: any_dest_cons *)
(* HOL4 closPropsScript.sml:3654-3655: a theorem that HOL4 states as
   the value of an ML expression: call_dest_cons *)
(* HOL4 closPropsScript.sml:3656-3657: a theorem that HOL4 states as
   the value of an ML expression: app_dest_cons *)

let app_call_dests_append = cake_theorem "app_call_dests_append"
  (fun () ->
    `!l1 l2. app_call_dests opt (l1 ++ l2) =
             app_call_dests opt l1 UNION app_call_dests opt l2`)
  CHEAT_TAC;;

(* HOL4 closPropsScript.sml:3668-3669: a theorem that HOL4 states as
   the value of an ML expression: any_dest_append *)
(* HOL4 closPropsScript.sml:3670-3671: a theorem that HOL4 states as
   the value of an ML expression: call_dest_append *)
(* HOL4 closPropsScript.sml:3672-3673: a theorem that HOL4 states as
   the value of an ML expression: app_dest_append *)

let app_call_dests_map = cake_theorem "app_call_dests_map"
  (fun () ->
    `!ls. app_call_dests opt (MAP f ls) =
          BIGUNION (set_of_list (MAP (\x. app_call_dests opt [f
            x]) ls))`)
  CHEAT_TAC;;

let any_dests_call_dests_app_dests =
  cake_theorem "any_dests_call_dests_app_dests"
  (fun () ->
    `!xs. (app_call_dests NONE) xs = (app_call_dests (SOME T)) xs
  UNION (app_call_dests (SOME F)) xs`)
  CHEAT_TAC;;

let _ = size_thms "closLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closPropsScript.sml:3725-3731: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let get_code_labels_def = cake_define_list_try_tac (fun () ->
  `MEASURE closLang_exp_size`)
  CHEAT_TAC
  [`closProps_get_code_labels (Var _394 _395:closLang_exp) = {}`;
   `closProps_get_code_labels (If _397 e1 e2 e3:closLang_exp) =
        closProps_get_code_labels e1 UNION
        closProps_get_code_labels e2 UNION
        closProps_get_code_labels e3`;
   `closProps_get_code_labels (Let _399 es e:closLang_exp) =
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))
          UNION
        closProps_get_code_labels e`;
   `closProps_get_code_labels (Raise _401 e:closLang_exp) =
  closProps_get_code_labels e`;
   `closProps_get_code_labels (Handle _403 e1 e2:closLang_exp) =
        closProps_get_code_labels e1 UNION
        closProps_get_code_labels e2`;
   `closProps_get_code_labels (closLang_Tick _405 e:closLang_exp) =
  closProps_get_code_labels e`;
   `closProps_get_code_labels (closLang_Call _408 _409 l
  es:closLang_exp) =
        {l} UNION BIGUNION (set_of_list (MAP
          closProps_get_code_labels es))`;
   `closProps_get_code_labels (App _411 l e es:closLang_exp) =
        (match l with NONE -> {} | SOME n -> {n}) UNION
        closProps_get_code_labels e UNION
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))`;
   `closProps_get_code_labels (closLang_Fn _412 l _413 _414 e) =
       (match l with NONE -> {} | SOME n -> {n}) UNION
       closProps_get_code_labels e`;
   `closProps_get_code_labels (Letrec _417 l _418 es e:closLang_exp) =
       (match l with NONE -> {} | SOME n ->
         IMAGE (\k. n + 2 * k) (count (LENGTH es))) UNION
        closProps_get_code_labels e UNION
        BIGUNION (set_of_list (MAP closProps_get_code_labels (MAP
          SND es)))`;
   `closProps_get_code_labels (closLang_Op _420 op es:closLang_exp) =
        BIGUNION (set_of_list (MAP closProps_get_code_labels es))
          UNION
        assign_get_code_label op`];;
hol4_overload "get_code_labels" "closProps_get_code_labels";;

(* HOL4 closPropsScript.sml:3733-3735: a theorem that HOL4 states as
   the value of an ML expression: get_code_labels_def *)

(* HOL4 closPropsScript.sml:3737: ML code, not ported *)

let get_code_labels_code_locs = cake_theorem "get_code_labels_code_locs"
  (fun () ->
    `!xs. EVERY no_Labels xs /\ every_Fn_SOME xs ==>
          BIGUNION (set_of_list (MAP closProps_get_code_labels xs))
            =
          set_of_list (code_locs xs) UNION (app_call_dests NONE)
            xs`)
  CHEAT_TAC;;

let initial_state_clock = cake_theorem "initial_state_clock"
  (fun () ->
    `state_clock
       (closSem_initial_state ffi max_app f co cc k) = k /\
       ((state_clock_fupd (K k) (closSem_initial_state ffi max_app
         f co cc k')) =
        closSem_initial_state ffi max_app f co cc k)`)
  CHEAT_TAC;;

cake_hide [];;

cake_hide_consts [];;
