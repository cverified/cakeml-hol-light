(* ======================================================== *)
(*  clos_ticksProof: ported from HOL4's
    compiler/backend/proofs/clos_ticksProofScript.sml
    A proof theory about clos_ticks.ml, with 7 definitions and 46
    theorems.  Needed by clos_knownProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_ticks
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_ticks.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 clos_ticksProofScript.sml:10-11: ML code, not ported *)

(* HOL4 clos_ticksProofScript.sml:15: the overload remove_ticks,
   which the port expands *)

let remove_ticks_IMP_LENGTH = cake_theorem "remove_ticks_IMP_LENGTH"
  (fun () ->
    `!(es:closLang_exp list) xs. xs = clos_ticks_remove_ticks es ==>
  LENGTH es = LENGTH xs`)
  CHEAT_TAC;;

let clos_ticksProof_remove_ticks_SING = cake_theorem "remove_ticks_SING"
  (fun () ->
    `!e. ?e'. clos_ticks_remove_ticks [e] = [e']`)
  CHEAT_TAC;;

let HD_remove_ticks_SING = cake_theorem "HD_remove_ticks_SING[simp]"
  (fun () ->
    `!x. [HD (clos_ticks_remove_ticks [x])] = clos_ticks_remove_ticks
  [x] /\
         LENGTH (clos_ticks_remove_ticks [x]) = 1`)
  CHEAT_TAC;;

(* code relation *)

let code_rel_def = cake_define
  `clos_ticksProof_code_rel e1 e2 <=>
     e2 = clos_ticks_remove_ticks e1`;;
hol4_overload "code_rel" "clos_ticksProof_code_rel";;

let clos_ticksProof_code_rel_IMP_LENGTH =
  cake_theorem "code_rel_IMP_LENGTH"
  (fun () ->
    `!xs ys. clos_ticksProof_code_rel xs ys ==> LENGTH xs = LENGTH ys`)
  CHEAT_TAC;;

let remove_ticks_CONS = cake_theorem "remove_ticks_CONS"
  (fun () ->
    `!es e. clos_ticks_remove_ticks (e :: es) = HD
  (clos_ticks_remove_ticks [e]) :: clos_ticks_remove_ticks es`)
  CHEAT_TAC;;

let clos_ticksProof_code_rel_CONS_CONS =
  cake_theorem "code_rel_CONS_CONS"
  (fun () ->
    `!x1 x2 xs y1 y2 ys. clos_ticksProof_code_rel (x1 :: x2 :: xs) (y1
  :: y2 :: ys) <=>
                          clos_ticksProof_code_rel [x1] [y1] /\
                            clos_ticksProof_code_rel (x2 :: xs) (y2 ::
                            ys)`)
  CHEAT_TAC;;

(* value relation *)

let f_rel_def = cake_define
  `clos_ticksProof_f_rel (a1,e1) (a2,e2) <=>
      a1 = a2 /\ clos_ticksProof_code_rel [e1] [e2]`;;
hol4_overload "f_rel" "clos_ticksProof_f_rel";;

let v_rel = cake_inductive
  `(!i. clos_ticksProof_v_rel (closSem_Number i) (closSem_Number i)) /\
   (!w. clos_ticksProof_v_rel (Word64 w) (Word64 w)) /\
   (!w. clos_ticksProof_v_rel (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_ticksProof_v_rel (closSem_RefPtr b n) (closSem_RefPtr
     b n)) /\
   (!tag xs ys.
      LIST_REL clos_ticksProof_v_rel xs ys ==>
        clos_ticksProof_v_rel (closSem_Block tag xs) (closSem_Block
          tag ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      LIST_REL clos_ticksProof_v_rel env1 env2 /\
      LIST_REL clos_ticksProof_v_rel args1 args2 /\
      clos_ticksProof_code_rel [e1] [e2] ==>
        clos_ticksProof_v_rel (Closure loc args1 env1 num_args e1)
          (Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 k.
      LIST_REL clos_ticksProof_v_rel env1 env2 /\
      LIST_REL clos_ticksProof_v_rel args1 args2 /\
      LIST_REL clos_ticksProof_f_rel funs1 funs2 ==>
        clos_ticksProof_v_rel (Recclosure loc args1 env1 funs1 k)
          (Recclosure loc args2 env2 funs2 k))`;;
hol4_overload "v_rel" "clos_ticksProof_v_rel";;

(* HOL4 clos_ticksProofScript.sml:93-105: a theorem that HOL4 states
   as the value of an ML expression *)

(* state relation *)

let ref_rel = cake_inductive
  `(!bs. clos_ticksProof_ref_rel (closSem_ByteArray bs)
  (closSem_ByteArray bs)) /\
   (!xs ys.
     LIST_REL clos_ticksProof_v_rel xs ys ==>
     clos_ticksProof_ref_rel (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_ticksProof_v_rel v w ==>
     clos_ticksProof_ref_rel (Thunk m v) (Thunk m w))`;;
hol4_overload "ref_rel" "clos_ticksProof_ref_rel";;

let FMAP_REL_def = cake_define
  `clos_ticksProof_FMAP_REL r f1 f2 <=>
     FDOM f1 = FDOM f2 /\
     (!k v. FLOOKUP f1 k = SOME v ==>
           (?v2. FLOOKUP f2 k = SOME v2 /\ r v v2))`;;
hol4_overload "FMAP_REL" "clos_ticksProof_FMAP_REL";;

let state_rel_def = cake_define
  `clos_ticksProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\
     LIST_REL (OPTREL clos_ticksProof_v_rel) (closSem_state_globals
       s) (closSem_state_globals t) /\
     clos_ticksProof_FMAP_REL ref_rel (state_refs s) (state_refs t)
       /\ closSem_state_compile
     s = pure_cc clos_ticks_compile_inc (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co clos_ticks_compile_inc o
       closSem_state_compile_oracle s`;;
hol4_overload "state_rel" "clos_ticksProof_state_rel";;

(* eval remove ticks *)

let mk_Ticks_def = cake_define_list
  [`clos_ticksProof_mk_Ticks [] (e:closLang_exp) = e`;
   `clos_ticksProof_mk_Ticks (t :: tr) (e:closLang_exp) =
  closLang_Tick t (clos_ticksProof_mk_Ticks tr e)`];;
hol4_overload "mk_Ticks" "clos_ticksProof_mk_Ticks";;

let remove_ticks_Tick = cake_theorem "remove_ticks_Tick"
  (fun () ->
    `!x t e. ~([closLang_Tick t e] = clos_ticks_remove_ticks [x])`)
  CHEAT_TAC;;

let remove_ticks_Var_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Var_IMP_mk_Ticks"
  (fun () ->
    `(!x tr n. [Var tr n] = clos_ticks_remove_ticks [x] ==> (?ts. x =
  clos_ticksProof_mk_Ticks ts (Var tr n)))`)
  CHEAT_TAC;;

let remove_ticks_If_IMP_mk_Ticks =
  cake_theorem "remove_ticks_If_IMP_mk_Ticks"
  (fun () ->
    `!x tr e1' e2' e3'.
        [If tr e1' e2' e3'] = clos_ticks_remove_ticks [x] ==>
          (?ts e1 e2 e3. x = clos_ticksProof_mk_Ticks ts (If tr e1
            e2 e3) /\
                        e1' = HD (clos_ticks_remove_ticks [e1]) /\
                        e2' = HD (clos_ticks_remove_ticks [e2]) /\
                        e3' = HD (clos_ticks_remove_ticks [e3]))`)
  CHEAT_TAC;;

let remove_ticks_Let_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Let_IMP_mk_Ticks"
  (fun () ->
    `!x t l e. [Let t l e] = clos_ticks_remove_ticks [x] ==>
                (?ts l' e'. x = clos_ticksProof_mk_Ticks ts (Let t
                  l' e') /\
                 l = clos_ticks_remove_ticks l' /\
                 [e] = clos_ticks_remove_ticks [e'])`)
  CHEAT_TAC;;

let remove_ticks_Raise_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Raise_IMP_mk_Ticks"
  (fun () ->
    `!x t e. [Raise t e] = clos_ticks_remove_ticks [x] ==>
              (?ts e'. x = clos_ticksProof_mk_Ticks ts (Raise t
                e') /\ [e] = clos_ticks_remove_ticks [e'])`)
  CHEAT_TAC;;

let remove_ticks_Handle_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Handle_IMP_mk_Ticks"
  (fun () ->
    `!x t e1' e2'. [Handle t e1' e2'] = clos_ticks_remove_ticks [x] ==>
                    (?ts e1 e2. x = clos_ticksProof_mk_Ticks ts
                      (Handle t e1 e2) /\
                     [e1'] = clos_ticks_remove_ticks [e1] /\
                       [e2'] = clos_ticks_remove_ticks [e2])`)
  CHEAT_TAC;;

let remove_ticks_Op_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Op_IMP_mk_Ticks"
  (fun () ->
    `!x tr op es'. [closLang_Op tr op es'] = clos_ticks_remove_ticks [x]
  ==>
        (?ts es. x = clos_ticksProof_mk_Ticks ts (closLang_Op tr
          op es) /\ es' = clos_ticks_remove_ticks es)`)
  CHEAT_TAC;;

let remove_ticks_Fn_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Fn_IMP_mk_Ticks"
  (fun () ->
    `!x tr loc vsopt num_args e'.
        [closLang_Fn tr loc vsopt num_args e'] =
          clos_ticks_remove_ticks [x] ==>
          (?ts e. x = clos_ticksProof_mk_Ticks ts (closLang_Fn tr
            loc vsopt num_args e) /\ [e'] = clos_ticks_remove_ticks
            [e])`)
  CHEAT_TAC;;

let remove_ticks_Letrec_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Letrec_IMP_mk_Ticks"
  (fun () ->
    `!x tr loc vsopt fns' e'.
        [Letrec tr loc vsopt fns' e'] = clos_ticks_remove_ticks [x]
          ==>
          (?ts fns e. x = clos_ticksProof_mk_Ticks ts (Letrec tr
            loc vsopt fns e) /\
                     e' = HD (clos_ticks_remove_ticks [e]) /\
                     fns' = MAP (\(num_args,x). (num_args,HD
                       (clos_ticks_remove_ticks [x]))) fns)`)
  CHEAT_TAC;;

let remove_ticks_App_IMP_mk_Ticks =
  cake_theorem "remove_ticks_App_IMP_mk_Ticks"
  (fun () ->
    `!x tr loc_opt e1' es'.
        [App tr loc_opt e1' es'] = clos_ticks_remove_ticks [x] ==>
          (?ts e1 es. x = clos_ticksProof_mk_Ticks ts (App tr
            loc_opt e1 es) /\
                     e1' = HD (clos_ticks_remove_ticks [e1]) /\
                     es' = clos_ticks_remove_ticks es)`)
  CHEAT_TAC;;

let remove_ticks_Call_IMP_mk_Ticks =
  cake_theorem "remove_ticks_Call_IMP_mk_Ticks"
  (fun () ->
    `!x tr ticks' dest es'. [closLang_Call tr ticks' dest es'] =
  clos_ticks_remove_ticks [x] ==>
        ticks' = 0 /\
        (?ts ticks es. x = clos_ticksProof_mk_Ticks ts
          (closLang_Call tr ticks dest es) /\
                      es' = clos_ticks_remove_ticks es)`)
  CHEAT_TAC;;

let remove_ticks_mk_Ticks = cake_theorem "remove_ticks_mk_Ticks"
  (fun () ->
    `!tr e. clos_ticks_remove_ticks [clos_ticksProof_mk_Ticks tr e] =
  clos_ticks_remove_ticks [e]`)
  CHEAT_TAC;;

let evaluate_mk_Ticks = cake_theorem "evaluate_mk_Ticks"
  (fun () ->
    `!tr e env s1.
        closSem_evaluate ([clos_ticksProof_mk_Ticks tr e],env,s1) =
          (if state_clock s1 < LENGTH tr then (Rerr (Rabort
            Rtimeout_error),state_clock_fupd (K 0) s1) else
            closSem_evaluate ([e],env,closSem_dec_clock (LENGTH tr)
            s1))`)
  CHEAT_TAC;;

let simple_val_rel = cake_theorem "simple_val_rel"
  (fun () ->
    `closProps_simple_val_rel clos_ticksProof_v_rel`)
  CHEAT_TAC;;

let clos_ticksProof_simple_state_rel = cake_theorem "simple_state_rel"
  (fun () ->
    `closProps_simple_state_rel clos_ticksProof_v_rel
  clos_ticksProof_state_rel`)
  CHEAT_TAC;;

let clos_ticksProof_do_app_lemma = cake_theorem "do_app_lemma[local]"
  (fun () ->
    `clos_ticksProof_state_rel s t /\ LIST_REL clos_ticksProof_v_rel xs
  ys ==>
     (match do_app opp ys t with Rerr err2 -> (?err1. do_app opp xs
       s = Rerr err1 /\
                             exc_rel clos_ticksProof_v_rel err1
                               err2) | Rval (y,t1) -> (?x s1.
                               clos_ticksProof_v_rel x y /\
                               clos_ticksProof_state_rel s1 t1 /\
                              do_app opp xs s = Rval (x,s1)))`)
  CHEAT_TAC;;

let clos_ticksProof_do_install_lemma =
  cake_theorem "do_install_lemma[local]"
  (fun () ->
    `clos_ticksProof_state_rel s t /\ LIST_REL clos_ticksProof_v_rel xs
  ys ==>
     (match closSem_do_install xs s with (Rerr err1,s1) -> (?err2
       t1. closSem_do_install ys t = (Rerr err2,t1) /\
                             exc_rel clos_ticksProof_v_rel err1
                               err2 /\ clos_ticksProof_state_rel s1 t1)
                               | (Rval exps1,s1) -> (?exps2 t1.
                               clos_ticksProof_state_rel s1 t1 /\
                               (~(exps1 = [])) /\
                              clos_ticksProof_code_rel exps1 exps2
                                /\
                              closSem_do_install ys t = (Rval
                                exps2,t1)))`)
  CHEAT_TAC;;

let clos_ticksProof_lookup_vars_lemma = cake_theorem "lookup_vars_lemma"
  (fun () ->
    `!vs env1 env2. LIST_REL clos_ticksProof_v_rel env1 env2 ==>
      (match lookup_vars vs env2 with NONE -> lookup_vars vs env1
        = NONE | SOME l2 -> (?l1. LIST_REL clos_ticksProof_v_rel l1 l2
        /\ lookup_vars vs env1 = SOME l1))`)
  CHEAT_TAC;;

let state_rel_IMP_max_app_EQ = cake_theorem "state_rel_IMP_max_app_EQ"
  (fun () ->
    `!s t. clos_ticksProof_state_rel s t ==> closSem_state_max_app s =
  closSem_state_max_app t`)
  CHEAT_TAC;;

let state_rel_IMP_code_FEMPTY =
  cake_theorem "state_rel_IMP_code_FEMPTY[local]"
  (fun () ->
    `!s t. clos_ticksProof_state_rel s t ==> closSem_state_code s =
  FEMPTY /\ closSem_state_code t = FEMPTY`)
  CHEAT_TAC;;

let clos_ticksProof_state_rel_clock = cake_theorem "state_rel_clock"
  (fun () ->
    `!s t k. clos_ticksProof_state_rel (state_clock_fupd (K k) s)
  (state_clock_fupd (K k) t) <=> clos_ticksProof_state_rel s
  (state_clock_fupd (K (state_clock s)) t)`)
  CHEAT_TAC;;


let clos_ticksProof_dest_closure_SOME_IMP =
  cake_theorem "dest_closure_SOME_IMP"
  (fun () ->
    `dest_closure max_app loc_opt f2 xs = SOME x ==>
      (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env
        clo_env num_args e) \/
      (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env
        clo_env fns i)`)
  CHEAT_TAC;;

let clos_ticksProof_v_rel_IMP_v_to_bytes =
  cake_theorem "v_rel_IMP_v_to_bytes[local]"
  (fun () ->
    `clos_ticksProof_v_rel x y ==> closSem_v_to_bytes y =
  closSem_v_to_bytes x`)
  CHEAT_TAC;;

let clos_ticksProof_v_rel_IMP_v_to_words =
  cake_theorem "v_rel_IMP_v_to_words[local]"
  (fun () ->
    `clos_ticksProof_v_rel x y ==> closSem_v_to_words y =
  closSem_v_to_words x`)
  CHEAT_TAC;;

let clos_ticksProof_state_rel_opt_rel_refs =
  cake_theorem "state_rel_opt_rel_refs[local]"
  (fun () ->
    `(clos_ticksProof_state_rel s1 s2 /\ FLOOKUP (state_refs s1) n = r1
  ==>
        (?r2. FLOOKUP (state_refs s2) n = r2 /\ OPTREL ref_rel r1
          r2)) /\
     (clos_ticksProof_state_rel s1 s2 /\ FLOOKUP (state_refs s2) n
       = r2 ==>
        (?r1. FLOOKUP (state_refs s1) n = r1 /\ OPTREL ref_rel r1
          r2))`)
  CHEAT_TAC;;

let state_rel_clock_eqs = cake_theorem "state_rel_clock_eqs[local]"
  (fun () ->
    `clos_ticksProof_state_rel s t ==> state_clock s = state_clock t`)
  CHEAT_TAC;;

let clos_ticksProof_state_rel_dec_clock =
  cake_theorem "state_rel_dec_clock[local]"
  (fun () ->
    `clos_ticksProof_state_rel s1 s2 ==> clos_ticksProof_state_rel
  (closSem_dec_clock 1 s1) (closSem_dec_clock 1 s2)`)
  CHEAT_TAC;;

let clos_ticksProof_rel_update_thunk =
  cake_theorem "rel_update_thunk[local]"
  (fun () ->
    `clos_ticksProof_state_rel s1 s2 /\
     LIST_REL clos_ticksProof_v_rel vs ys ==>
       (update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys =
         NONE ==>
          update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs =
            NONE) /\
       (update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys =
         SOME refs2 ==>
          (?refs1. update_thunk [closSem_RefPtr v ptr] (state_refs
            s1) vs = SOME refs1 /\
                  clos_ticksProof_state_rel (state_refs_fupd (K
                    refs1) s1) (state_refs_fupd (K refs2) s2)))`)
  CHEAT_TAC;;

let clos_ticksProof_evaluate_remove_ticks =
  cake_theorem "evaluate_remove_ticks"
  (fun () ->
    `(!ys env2 (t1:('c,'ffi)closSem_state) res2 t2 env1 s1 xs.
       (closSem_evaluate (ys,env2,t1) = (res2,t2)) /\
       LIST_REL clos_ticksProof_v_rel env1 env2 /\
       clos_ticksProof_state_rel s1 t1 /\ clos_ticksProof_code_rel
         xs ys ==>
       (?ck res1 s2.
          (closSem_evaluate (xs,env1,state_clock_fupd (K
            (state_clock s1 + ck)) s1) = (res1,s2)) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
          clos_ticksProof_state_rel s2 t2)) /\
     (!loc_opt f2 args2 (t1:('c,'ffi)closSem_state) res2 t2 f1
       args1 s1.
       (evaluate_app loc_opt f2 args2 t1 = (res2,t2)) /\
       clos_ticksProof_v_rel f1 f2 /\ LIST_REL
         clos_ticksProof_v_rel args1 args2 /\
       clos_ticksProof_state_rel s1 t1 ==>
       (?ck res1 s2.
         (evaluate_app loc_opt f1 args1 (state_clock_fupd (K
           (state_clock s1 + ck)) s1) = (res1,s2)) /\
         semanticPrimitivesProps_result_rel (LIST_REL
           clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
         clos_ticksProof_state_rel s2 t2))`)
  CHEAT_TAC;;

let remove_ticks_correct = cake_theorem "remove_ticks_correct"
  (fun () ->
    `(!xs env2 (t1:('c,'ffi)closSem_state) res2 t2 env1 s1.
       (closSem_evaluate (clos_ticks_remove_ticks xs,env2,t1) =
         (res2,t2)) /\
       LIST_REL clos_ticksProof_v_rel env1 env2 /\
         clos_ticksProof_state_rel s1 t1 ==>
       (?ck res1 s2.
          (closSem_evaluate (xs,env1,state_clock_fupd (K
            (state_clock s1 + ck)) s1) = (res1,s2)) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            clos_ticksProof_v_rel) clos_ticksProof_v_rel res1 res2 /\
          clos_ticksProof_state_rel s2 t2))`)
  CHEAT_TAC;;

(* preservation of observable semantics *)

let clos_ticksProof_semantics_remove_ticks =
  cake_theorem "semantics_remove_ticks"
  (fun () ->
    `~(
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc clos_ticks_compile_inc cc) xs = ffi_Fail) ==>
        (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc clos_ticks_compile_inc cc) xs =
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          (pure_co clos_ticks_compile_inc o co) cc
          (clos_ticks_remove_ticks xs)`)
  CHEAT_TAC;;

(* syntactic properties *)

let code_locs_remove_ticks = cake_theorem "code_locs_remove_ticks"
  (fun () ->
    `!xs. code_locs (clos_ticks_remove_ticks xs) = code_locs xs`)
  CHEAT_TAC;;

let remove_ticks_every_Fn_SOME =
  cake_theorem "remove_ticks_every_Fn_SOME[simp]"
  (fun () ->
    `!ls. every_Fn_SOME (clos_ticks_remove_ticks ls) <=> every_Fn_SOME
  ls`)
  CHEAT_TAC;;

let remove_ticks_every_Fn_vs_NONE =
  cake_theorem "remove_ticks_every_Fn_vs_NONE[simp]"
  (fun () ->
    `!ls. every_Fn_vs_NONE (clos_ticks_remove_ticks ls) <=>
  every_Fn_vs_NONE ls`)
  CHEAT_TAC;;

let EVERY_remove_ticks_sing = cake_theorem "EVERY_remove_ticks_sing"
  (fun () ->
    `EVERY f (clos_ticks_remove_ticks [x]) = f (HD
  (clos_ticks_remove_ticks [x]))`)
  CHEAT_TAC;;

let remove_ticks_obeys_max_app =
  cake_theorem "remove_ticks_obeys_max_app"
  (fun () ->
    `!xs. EVERY (obeys_max_app m) xs ==> EVERY (obeys_max_app m)
  (clos_ticks_remove_ticks xs)`)
  CHEAT_TAC;;

let remove_ticks_no_Labels = cake_theorem "remove_ticks_no_Labels"
  (fun () ->
    `!xs. EVERY no_Labels xs ==> EVERY no_Labels
  (clos_ticks_remove_ticks xs)`)
  CHEAT_TAC;;

let remove_ticks_app_call_dests =
  cake_theorem "remove_ticks_app_call_dests[simp]"
  (fun () ->
    `!es. app_call_dests x (clos_ticks_remove_ticks es) =
  app_call_dests x es`)
  CHEAT_TAC;;

let clos_ticksProof_remove_ticks_code_labels =
  cake_theorem "remove_ticks_code_labels[simp]"
  (fun () ->
    `!es. MAP get_code_labels' (clos_ticks_remove_ticks es) = MAP
  get_code_labels' es`)
  CHEAT_TAC;;
