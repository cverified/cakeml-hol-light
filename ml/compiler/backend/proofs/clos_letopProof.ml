(* ======================================================== *)
(*  clos_letopProof: ported from HOL4's
    compiler/backend/proofs/clos_letopProofScript.sml
    A proof theory about clos_letop.ml, with 6 definitions and 40
    theorems.  Needed by clos_knownProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_letop
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_letop.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "misc/misc.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_letopProof"
  ["backendProps"; "closLang"; "closProps"; "closSem"; "clos_letop"];;


(* HOL4 clos_letopProofScript.sml:11: ML code, not ported *)

(* HOL4 clos_letopProofScript.sml:15: the overload let_op, which the
   port expands *)
(* HOL4 clos_letopProofScript.sml:16: the overload var_list, which
   the port expands *)

let let_op_SING = prove
 (`!x. ?y. clos_letop_let_op [x] = [y]`,
  CHEAT_TAC);;

let HD_let_op_SING = prove
 (`!x. [HD (clos_letop_let_op [x])] = clos_letop_let_op [x] /\
       LENGTH (clos_letop_let_op [x]) = 1`,
  CHEAT_TAC);;
add_simp HD_let_op_SING;;

let clos_letopProof_code_rel_def = new_definition
  `clos_letopProof_code_rel e1 e2 <=>
     e2 = clos_letop_let_op e1`;;

(* code_rel_IMP_LENGTH *)
let clos_letopProof_code_rel_IMP_LENGTH = prove
 (`!xs ys. clos_letopProof_code_rel xs ys ==> LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;

(* code_rel_CONS_CONS *)
let clos_letopProof_code_rel_CONS_CONS = prove
 (`clos_letopProof_code_rel (CONS x1 (CONS x2 xs)) (CONS y1 (CONS y2
  ys)) ==>
      clos_letopProof_code_rel [x1] [y1] /\
        clos_letopProof_code_rel (CONS x2 xs) (CONS y2 ys)`,
  CHEAT_TAC);;

(* value relation *)

let clos_letopProof_f_rel_def = new_definition
  `clos_letopProof_f_rel (a1,e1) (a2,e2) <=>
      a1 = a2 /\ clos_letopProof_code_rel [e1] [e2]`;;

let clos_letopProof_v_rel = cake_inductive
  `(!i. clos_letopProof_v_rel (closSem_Number i) (closSem_Number i)) /\
   (!w. clos_letopProof_v_rel (closSem_Word64 w) (closSem_Word64 w))
     /\
   (!w. clos_letopProof_v_rel (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_letopProof_v_rel (closSem_RefPtr b n) (closSem_RefPtr
     b n)) /\
   (!tag xs ys.
      ALL2 clos_letopProof_v_rel xs ys ==>
        clos_letopProof_v_rel (closSem_Block tag xs) (closSem_Block
          tag ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      ALL2 clos_letopProof_v_rel env1 env2 /\
      ALL2 clos_letopProof_v_rel args1 args2 /\
      clos_letopProof_code_rel [e1] [e2] ==>
        clos_letopProof_v_rel (closSem_Closure loc args1 env1
          num_args e1) (closSem_Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 k.
      ALL2 clos_letopProof_v_rel env1 env2 /\
      ALL2 clos_letopProof_v_rel args1 args2 /\
      ALL2 clos_letopProof_f_rel funs1 funs2 ==>
        clos_letopProof_v_rel (closSem_Recclosure loc args1 env1
          funs1 k) (closSem_Recclosure loc args2 env2 funs2 k))`;;

(* HOL4 clos_letopProofScript.sml:76-88: a theorem that HOL4 states
   as the value of an ML expression: v_rel_simps *)

(* state relation *)

let clos_letopProof_ref_rel = cake_inductive
  `(!bs. clos_letopProof_ref_rel (closSem_ByteArray bs)
  (closSem_ByteArray bs)) /\
   (!xs ys.
     ALL2 clos_letopProof_v_rel xs ys ==>
     clos_letopProof_ref_rel (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_letopProof_v_rel v w ==>
     clos_letopProof_ref_rel (closSem_Thunk m v) (closSem_Thunk m
       w))`;;

let FMAP_REL_def = new_definition
  `clos_letopProof_FMAP_REL r f1 f2 <=>
     FDOM f1 = FDOM f2 /\
     (!k v. FLOOKUP f1 k = SOME v ==>
           (?v2. FLOOKUP f2 k = SOME v2 /\ r v v2))`;;

let clos_letopProof_state_rel_def = new_definition
  `clos_letopProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       closSem_state_clock
     t = closSem_state_clock s /\ closSem_state_ffi
     t = closSem_state_ffi s /\
     ALL2 (OPTREL clos_letopProof_v_rel) (closSem_state_globals s)
       (closSem_state_globals t) /\
     clos_letopProof_FMAP_REL clos_letopProof_ref_rel
       (closSem_state_refs s) (closSem_state_refs t) /\
       closSem_state_compile
     s = pure_cc clos_letop_compile_inc (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co clos_letop_compile_inc o
       closSem_state_compile_oracle s`;;

(* *)

(* v_rel_IMP_v_to_bytes_lemma[local] *)
let clos_letopProof_v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y.
     clos_letopProof_v_rel x y ==>
     (!ns. (closSem_v_to_list x = SOME (MAP (closSem_Number o (&) o
       (w2n:word8->num)) ns)) <=>
          (closSem_v_to_list y = SOME (MAP (closSem_Number o (&) o
            (w2n:word8->num)) ns)))`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_bytes[local] *)
let clos_letopProof_v_rel_IMP_v_to_bytes = prove
 (`clos_letopProof_v_rel x y ==> closSem_v_to_bytes y =
  closSem_v_to_bytes x`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_words_lemma[local] *)
let clos_letopProof_v_rel_IMP_v_to_words_lemma = prove
 (`!x y.
     clos_letopProof_v_rel x y ==>
     (!ns. (closSem_v_to_list x = SOME (MAP closSem_Word64 ns)) <=>
          (closSem_v_to_list y = SOME (MAP closSem_Word64 ns)))`,
  CHEAT_TAC);;

(* v_rel_IMP_v_to_words[local] *)
let clos_letopProof_v_rel_IMP_v_to_words = prove
 (`clos_letopProof_v_rel x y ==> closSem_v_to_words y =
  closSem_v_to_words x`,
  CHEAT_TAC);;


(* *)

let dest_op_SOME_IMP = prove
 (`!x args opp. clos_letop_dest_op x args = SOME opp ==>
      (?t xs. x = closLang_Op t opp xs /\
             clos_letop_var_list 0 xs args)`,
  CHEAT_TAC);;


let var_list_IMP_LENGTH = prove
 (`!n xs ys. clos_letop_var_list n xs ys ==> LENGTH xs = LENGTH ys`,
  CHEAT_TAC);;

(* var_list_IMP_evaluate[local] *)
let clos_letopProof_var_list_IMP_evaluate = prove
 (`!a2 a1 xs (ys:closLang_exp list) (s:('c,'ffi)closSem_state) env.
     clos_letop_var_list (LENGTH a1) xs ys /\ LENGTH ys = LENGTH a2
       ==>
     closSem_evaluate (xs,APPEND (APPEND a1 a2) env,s) = (Rval
       a2,s)`,
  CHEAT_TAC);;

(* var_list_IMP_evaluate[local] *)
let clos_letopProof_var_list_IMP_evaluate = prove
 (`!vs xs (ys:closLang_exp list) (s:('c,'ffi)closSem_state) env.
     clos_letop_var_list 0 xs ys /\ LENGTH ys = LENGTH vs ==>
       closSem_evaluate (xs,APPEND vs env,s) = (Rval vs,s)`,
  CHEAT_TAC);;

(* lookup_vars_lemma *)
let clos_letopProof_lookup_vars_lemma = prove
 (`!vs env1 env2. ALL2 clos_letopProof_v_rel env1 env2 ==>
    (match lookup_vars vs env1 with NONE -> lookup_vars vs env2 =
      NONE | SOME l1 -> (?l2. ALL2 clos_letopProof_v_rel l1 l2 /\
      lookup_vars vs env2 = SOME l2))`,
  CHEAT_TAC);;

(* find_code_lemma *)
let clos_letopProof_find_code_lemma = prove
 (`!s t p args. clos_letopProof_state_rel s t ==>
      closSem_find_code p args (closSem_state_code s) = NONE /\
      closSem_find_code p args (closSem_state_code t) = NONE`,
  CHEAT_TAC);;

(* dest_closure_SOME_IMP *)
let clos_letopProof_dest_closure_SOME_IMP = prove
 (`dest_closure max_app loc_opt f2 xs = SOME x ==>
    (?loc arg_env clo_env num_args e. f2 = closSem_Closure loc
      arg_env clo_env num_args e) \/
    (?loc arg_env clo_env fns i. f2 = closSem_Recclosure loc
      arg_env clo_env fns i)`,
  CHEAT_TAC);;

(* dest_closure_SOME_Full_app *)
let clos_letopProof_dest_closure_SOME_Full_app = prove
 (`clos_letopProof_v_rel f1 f2 /\ clos_letopProof_v_rel a1 a2 /\ ALL2
  clos_letopProof_v_rel args1 args2 /\
    dest_closure max_app loc_opt f1 (CONS a1 args1) = SOME (Full_app
      exp1 env1 rest_args1) ==>
      (?exp2 env2 rest_args2.
      clos_letopProof_code_rel [exp1] [exp2] /\
      ALL2 clos_letopProof_v_rel env1 env2 /\
      ALL2 clos_letopProof_v_rel rest_args1 rest_args2 /\
      dest_closure max_app loc_opt f2 (CONS a2 args2) = SOME
        (Full_app exp2 env2 rest_args2))`,
  CHEAT_TAC);;

(* simple_state_rel[local] *)
let clos_letopProof_simple_state_rel = prove
 (`closProps_simple_state_rel clos_letopProof_v_rel
  clos_letopProof_state_rel`,
  CHEAT_TAC);;

(* do_app_lemma[local] *)
let clos_letopProof_do_app_lemma = prove
 (`clos_letopProof_state_rel s t /\ ALL2 clos_letopProof_v_rel xs ys ==>
   (match closSem_do_app opp xs s with Rerr err1 -> (?err2.
     closSem_do_app opp ys t = Rerr err2 /\
                           exc_rel clos_letopProof_v_rel err1 err2) |
                             Rval (x,s1) -> (?y t1.
                             clos_letopProof_v_rel x y /\
                             clos_letopProof_state_rel s1 t1 /\
                              closSem_do_app opp ys t = Rval
                                (y,t1)))`,
  CHEAT_TAC);;

(* do_install_lemma[local] *)
let clos_letopProof_do_install_lemma = prove
 (`clos_letopProof_state_rel s t /\ ALL2 clos_letopProof_v_rel xs ys ==>
   (match closSem_do_install xs s with (Rerr err1,s1) -> (?err2 t1.
     closSem_do_install ys t = (Rerr err2,t1) /\
                           exc_rel clos_letopProof_v_rel err1 err2 /\
                             clos_letopProof_state_rel s1 t1) | (Rval
                             exps1,s1) -> (?exps2 t1.
                             clos_letopProof_state_rel s1 t1 /\ (~(exps1
                             = [])) /\
                              clos_letopProof_code_rel exps1 exps2 /\
                              closSem_do_install ys t = (Rval
                                exps2,t1)))`,
  CHEAT_TAC);;

(* state_rel_opt_rel_refs[local] *)
let clos_letopProof_state_rel_opt_rel_refs = prove
 (`(clos_letopProof_state_rel s1 s2 /\ FLOOKUP (state_refs s1) n = r1
  ==>
      (?r2. FLOOKUP (state_refs s2) n = r2 /\ OPTREL
        clos_letopProof_ref_rel r1 r2)) /\
   (clos_letopProof_state_rel s1 s2 /\ FLOOKUP (state_refs s2) n = r2
     ==>
      (?r1. FLOOKUP (state_refs s1) n = r1 /\ OPTREL
        clos_letopProof_ref_rel r1 r2))`,
  CHEAT_TAC);;

(* state_rel_clocks_eqs[local] *)
let clos_letopProof_state_rel_clocks_eqs = prove
 (`clos_letopProof_state_rel s1 s2 ==> state_clock s1 = state_clock s2`,
  CHEAT_TAC);;

(* state_rel_dec_clock[local] *)
let clos_letopProof_state_rel_dec_clock = prove
 (`clos_letopProof_state_rel s1 s2 ==> clos_letopProof_state_rel
  (closSem_dec_clock 1 s1) (closSem_dec_clock 1 s2)`,
  CHEAT_TAC);;

(* rel_update_thunk[local] *)
let clos_letopProof_rel_update_thunk = prove
 (`clos_letopProof_state_rel s1 s2 /\
   ALL2 clos_letopProof_v_rel vs ys ==>
     (closSem_update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs
       = NONE ==>
        closSem_update_thunk [closSem_RefPtr v ptr] (state_refs s2)
          ys = NONE) /\
     (closSem_update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs
       = SOME refs1 ==>
        (?refs2. closSem_update_thunk [closSem_RefPtr v ptr]
          (state_refs s2) ys = SOME refs2 /\
                clos_letopProof_state_rel (state_refs_fupd (K
                  refs1) s1) (state_refs_fupd (K refs2) s2)))`,
  CHEAT_TAC);;

(* evaluate_let_op *)

(* evaluate_let_op *)
let clos_letopProof_evaluate_let_op = prove
 (`(!xs env1 (s1:('c,'ffi)closSem_state) res1 s2 ys env2 t1.
       closSem_evaluate (xs,env1,s1) = (res1,s2) /\
       ALL2 clos_letopProof_v_rel env1 env2 /\
         clos_letopProof_state_rel s1 t1 /\
       clos_letopProof_code_rel xs ys ==>
       (?res2 t2.
         closSem_evaluate (ys,env2,t1) = (res2,t2) /\
         semanticPrimitivesProps_result_rel (ALL2
           clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
         clos_letopProof_state_rel s2 t2)) /\
    (!loc_opt f1 args1 (s1:('c,'ffi)closSem_state) res1 s2 f2 args2
      t1.
       evaluate_app loc_opt f1 args1 s1 = (res1,s2) /\
       clos_letopProof_v_rel f1 f2 /\ ALL2 clos_letopProof_v_rel
         args1 args2 /\
       clos_letopProof_state_rel s1 t1 ==>
       (?res2 t2.
         evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
         semanticPrimitivesProps_result_rel (ALL2
           clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
         clos_letopProof_state_rel s2 t2))`,
  CHEAT_TAC);;

let let_op_correct = prove
 (`!xs env1 (s1:('c,'ffi)closSem_state) res1 s2 env2 t1.
       closSem_evaluate (xs,env1,s1) = (res1,s2) /\
       ALL2 clos_letopProof_v_rel env1 env2 /\
         clos_letopProof_state_rel s1 t1 ==>
       (?res2 t2.
         closSem_evaluate (clos_letop_let_op xs,env2,t1) = (res2,t2)
           /\
         semanticPrimitivesProps_result_rel (ALL2
           clos_letopProof_v_rel) clos_letopProof_v_rel res1 res2 /\
         clos_letopProof_state_rel s2 t2)`,
  CHEAT_TAC);;

(* preservation of observational semantics *)

(* semantics_let_op *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let clos_letopProof_semantics_let_op = prove
 (cake_as_vars (fun () ->
    `~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc clos_letop_compile_inc cc) xs = ffi_Fail) ==>
        (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          (pure_co clos_letop_compile_inc o co) cc
            (clos_letop_let_op xs) =
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc clos_letop_compile_inc cc) xs`),
  CHEAT_TAC);;

(* syntactic properties *)

(* [local] *)
let var_list_IMP_code_locs = prove
 (`!k l x. clos_letop_var_list k l x ==> code_locs l = []`,
  CHEAT_TAC);;

(* [local] *)
let var_list_let_op_IMP_code_locs = prove
 (`!k l x. clos_letop_var_list k (clos_letop_let_op l) x ==> code_locs
  l = []`,
  CHEAT_TAC);;

let code_locs_let_op = prove
 (`!xs. code_locs (clos_letop_let_op xs) = code_locs xs`,
  CHEAT_TAC);;

let let_op_every_Fn_SOME = prove
 (`!es. every_Fn_SOME (clos_letop_let_op es) <=> every_Fn_SOME es`,
  CHEAT_TAC);;
add_simp let_op_every_Fn_SOME;;

let let_op_every_Fn_vs_NONE = prove
 (`!es. every_Fn_vs_NONE (clos_letop_let_op es) <=> every_Fn_vs_NONE
  es`,
  CHEAT_TAC);;
add_simp let_op_every_Fn_vs_NONE;;

let EVERY_let_op_sing = prove
 (`ALL f (clos_letop_let_op [x]) = f (HD (clos_letop_let_op [x]))`,
  CHEAT_TAC);;

let var_list_no_Labels = prove
 (`!n l m. clos_letop_var_list n l m ==> ALL no_Labels l /\ ALL
  (obeys_max_app k) l`,
  CHEAT_TAC);;

let let_op_obeys_max_app = prove
 (`!es. ALL (obeys_max_app k) (clos_letop_let_op es) <=> ALL
  (obeys_max_app k) es`,
  CHEAT_TAC);;

let let_op_no_Labels = prove
 (`!es. ALL no_Labels (clos_letop_let_op es) <=> ALL no_Labels es`,
  CHEAT_TAC);;

let var_list_app_call_dests = prove
 (`!x y z. clos_letop_var_list x y z ==> app_call_dests a y = {}`,
  CHEAT_TAC);;

let let_op_app_call_dests = prove
 (`!es. app_call_dests x (clos_letop_let_op es) = app_call_dests x es`,
  CHEAT_TAC);;
add_simp let_op_app_call_dests;;

(* var_list_code_labels_imp *)
let clos_letopProof_var_list_code_labels_imp = prove
 (`!n x y. clos_letop_var_list n x y ==> UNIONS (set_of_list (MAP
  closProps_get_code_labels x)) = {}`,
  CHEAT_TAC);;

let let_op_get_code_labels = prove
 (`!es. MAP closProps_get_code_labels (clos_letop_let_op es) = MAP
  closProps_get_code_labels es`,
  CHEAT_TAC);;
add_simp let_op_get_code_labels;;

(* and the interface *)
let _ = unhide_overloads ();;
