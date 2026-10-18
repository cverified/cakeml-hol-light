(* ======================================================== *)
(*  clos_fvsProof: ported from HOL4's
    compiler/backend/proofs/clos_fvsProofScript.sml
    A proof theory about clos_fvs.ml, with 5 definitions and 37
    theorems.  Needed by clos_knownProof.ml and clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_fvs
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_fvs.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let clos_fvsProof_LENGTH_remove_fvs = cake_theorem "LENGTH_remove_fvs"
  (fun () ->
    `!fvs xs. LENGTH (remove_fvs fvs xs) = LENGTH xs`)
  CHEAT_TAC;;

let remove_fvs_SING = cake_theorem "remove_fvs_SING"
  (fun () ->
    `!x. ?y. remove_fvs fvs [x] = [y]`)
  CHEAT_TAC;;

let HD_remove_fvs_SING = cake_theorem "HD_remove_fvs_SING[simp]"
  (fun () ->
    `!x. [HD (remove_fvs fvs [x])] = remove_fvs fvs [x]`)
  CHEAT_TAC;;

let EVERY_remove_fvs_SING = cake_theorem "EVERY_remove_fvs_SING"
  (fun () ->
    `EVERY P (remove_fvs fvs [x]) <=> P (HD (remove_fvs fvs [x]))`)
  CHEAT_TAC;;

let code_rel_def = cake_define
  `clos_fvsProof_code_rel fvs e1 e2 <=>
     e2 = remove_fvs fvs e1`;;
hol4_overload "code_rel" "clos_fvsProof_code_rel";;

let code_rel_IMP_LENGTH = cake_theorem "code_rel_IMP_LENGTH"
  (fun () ->
    `!xs ys. clos_fvsProof_code_rel fvs xs ys ==> LENGTH xs = LENGTH
  ys`)
  CHEAT_TAC;;

let code_rel_CONS_CONS = cake_theorem "code_rel_CONS_CONS"
  (fun () ->
    `clos_fvsProof_code_rel fvs (x1 :: x2 :: xs) (y1 :: y2 :: ys) ==>
        clos_fvsProof_code_rel fvs [x1] [y1] /\
          clos_fvsProof_code_rel fvs (x2 :: xs) (y2 :: ys)`)
  CHEAT_TAC;;

(* value relation *)

let f_rel_def = cake_define
  `clos_fvsProof_f_rel fvs (a1,e1) (a2,e2) <=>
      a1 = a2 /\ clos_fvsProof_code_rel (a1 + fvs) [e1] [e2]`;;
hol4_overload "f_rel" "clos_fvsProof_f_rel";;

let v_rel = cake_inductive
  `(!i. clos_fvsProof_v_rel (closSem_Number i) (closSem_Number i)) /\
   (!w. clos_fvsProof_v_rel (Word64 w) (Word64 w)) /\
   (!w. clos_fvsProof_v_rel (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_fvsProof_v_rel (closSem_RefPtr b n) (closSem_RefPtr b
     n)) /\
   (!tag xs ys.
      LIST_REL clos_fvsProof_v_rel xs ys ==>
        clos_fvsProof_v_rel (closSem_Block tag xs) (closSem_Block tag
          ys)) /\
   (!loc args1 args2 env1 env2 num_args e1 e2.
      LIST_REL clos_fvsProof_v_rel env1 env2 /\
      LIST_REL clos_fvsProof_v_rel args1 args2 /\
      clos_fvsProof_code_rel (LENGTH env1 + num_args) [e1] [e2] ==>
        clos_fvsProof_v_rel (Closure loc args1 env1 num_args e1)
          (Closure loc args2 env2 num_args e2)) /\
   (!loc args1 args2 env1 env2 k.
      LIST_REL clos_fvsProof_v_rel env1 env2 /\
      LIST_REL clos_fvsProof_v_rel args1 args2 /\
      LIST_REL (clos_fvsProof_f_rel (LENGTH env1 + LENGTH funs1))
        funs1 funs2 ==>
        clos_fvsProof_v_rel (Recclosure loc args1 env1 funs1 k)
          (Recclosure loc args2 env2 funs2 k))`;;
hol4_overload "v_rel" "clos_fvsProof_v_rel";;

(* HOL4 clos_fvsProofScript.sml:81-93: a theorem that HOL4 states as
   the value of an ML expression: v_rel_simps *)

(* state relation *)

let ref_rel = cake_inductive
  `(!bs. clos_fvsProof_ref_rel (closSem_ByteArray bs) (closSem_ByteArray
  bs)) /\
   (!xs ys.
     LIST_REL clos_fvsProof_v_rel xs ys ==>
     clos_fvsProof_ref_rel (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_fvsProof_v_rel v w ==>
     clos_fvsProof_ref_rel (Thunk m v) (Thunk m w))`;;
hol4_overload "ref_rel" "clos_fvsProof_ref_rel";;

let state_rel_def = cake_define
  `clos_fvsProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\
     LIST_REL (OPTREL clos_fvsProof_v_rel) (closSem_state_globals s)
       (closSem_state_globals t) /\
     fmap_rel ref_rel (state_refs s) (state_refs t) /\
       closSem_state_compile
     s = pure_cc clos_fvs_compile_inc (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = pure_co clos_fvs_compile_inc o
       closSem_state_compile_oracle s`;;
hol4_overload "state_rel" "clos_fvsProof_state_rel";;

(* *)

let clos_fvsProof_v_rel_IMP_v_to_bytes_lemma =
  cake_theorem "v_rel_IMP_v_to_bytes_lemma[local]"
  (fun () ->
    `!x y.
       clos_fvsProof_v_rel x y ==>
       (!ns. (v_to_list x = SOME (MAP (closSem_Number o (&) o
         (w2n:word8->num)) ns)) <=>
            (v_to_list y = SOME (MAP (closSem_Number o (&) o
              (w2n:word8->num)) ns)))`)
  CHEAT_TAC;;

let v_rel_IMP_v_to_bytes = cake_theorem "v_rel_IMP_v_to_bytes[local]"
  (fun () ->
    `clos_fvsProof_v_rel x y ==> closSem_v_to_bytes y =
  closSem_v_to_bytes x`)
  CHEAT_TAC;;

let clos_fvsProof_v_rel_IMP_v_to_words_lemma =
  cake_theorem "v_rel_IMP_v_to_words_lemma[local]"
  (fun () ->
    `!x y.
       clos_fvsProof_v_rel x y ==>
       (!ns. (v_to_list x = SOME (MAP Word64 ns)) <=>
            (v_to_list y = SOME (MAP Word64 ns)))`)
  CHEAT_TAC;;

let v_rel_IMP_v_to_words = cake_theorem "v_rel_IMP_v_to_words[local]"
  (fun () ->
    `clos_fvsProof_v_rel x y ==> closSem_v_to_words y =
  closSem_v_to_words x`)
  CHEAT_TAC;;


(* *)

let lookup_vars_lemma = cake_theorem "lookup_vars_lemma"
  (fun () ->
    `!vs env1 env2. LIST_REL clos_fvsProof_v_rel env1 env2 ==>
      (match lookup_vars vs env1 with NONE -> lookup_vars vs env2
        = NONE | SOME l1 -> (?l2. LIST_REL clos_fvsProof_v_rel l1 l2
        /\ lookup_vars vs env2 = SOME l2))`)
  CHEAT_TAC;;

let clos_fvsProof_find_code_lemma = cake_theorem "find_code_lemma"
  (fun () ->
    `!s t p args. clos_fvsProof_state_rel s t ==>
        closSem_find_code p args (closSem_state_code s) = NONE /\
        closSem_find_code p args (closSem_state_code t) = NONE`)
  CHEAT_TAC;;

let dest_closure_SOME_IMP = cake_theorem "dest_closure_SOME_IMP"
  (fun () ->
    `dest_closure max_app loc_opt f2 xs = SOME x ==>
      (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env
        clo_env num_args e) \/
      (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env
        clo_env fns i)`)
  CHEAT_TAC;;

let dest_closure_SOME_Full_app =
  cake_theorem "dest_closure_SOME_Full_app"
  (fun () ->
    `clos_fvsProof_v_rel f1 f2 /\ clos_fvsProof_v_rel a1 a2 /\ LIST_REL
  clos_fvsProof_v_rel args1 args2 /\
      dest_closure max_app loc_opt f1 (a1 :: args1) = SOME
        (Full_app exp1 env1 rest_args1) ==>
        (?exp2 env2 rest_args2.
        clos_fvsProof_code_rel (LENGTH env1) [exp1] [exp2] /\
        LIST_REL clos_fvsProof_v_rel env1 env2 /\
        LIST_REL clos_fvsProof_v_rel rest_args1 rest_args2 /\
        dest_closure max_app loc_opt f2 (a2 :: args2) = SOME
          (Full_app exp2 env2 rest_args2))`)
  CHEAT_TAC;;

let simple_state_rel = cake_theorem "simple_state_rel[local]"
  (fun () ->
    `closProps_simple_state_rel clos_fvsProof_v_rel
  clos_fvsProof_state_rel`)
  CHEAT_TAC;;

let clos_fvsProof_do_app_lemma = cake_theorem "do_app_lemma[local]"
  (fun () ->
    `clos_fvsProof_state_rel s t /\ LIST_REL clos_fvsProof_v_rel xs ys
  ==>
     (match do_app opp xs s with Rerr err1 -> (?err2. do_app opp ys
       t = Rerr err2 /\
                             exc_rel clos_fvsProof_v_rel err1 err2)
                               | Rval (x,s1) -> (?y t1.
                               clos_fvsProof_v_rel x y /\
                               clos_fvsProof_state_rel s1 t1 /\
                              do_app opp ys t = Rval (y,t1)))`)
  CHEAT_TAC;;

let do_install_lemma = cake_theorem "do_install_lemma[local]"
  (fun () ->
    `clos_fvsProof_state_rel s t /\ LIST_REL clos_fvsProof_v_rel xs ys
  ==>
     (match closSem_do_install xs s with (Rerr err1,s1) -> (?err2
       t1. closSem_do_install ys t = (Rerr err2,t1) /\
                             exc_rel clos_fvsProof_v_rel err1 err2
                               /\ clos_fvsProof_state_rel s1 t1) | (Rval
                               exps1,s1) -> (?exps2 t1.
                               clos_fvsProof_state_rel s1 t1 /\ (~(exps1
                               = [])) /\
                              clos_fvsProof_code_rel 0 exps1 exps2
                                /\
                              closSem_do_install ys t = (Rval
                                exps2,t1)))`)
  CHEAT_TAC;;

let clos_fvsProof_state_rel_opt_rel_refs =
  cake_theorem "state_rel_opt_rel_refs[local]"
  (fun () ->
    `(clos_fvsProof_state_rel s1 s2 /\ FLOOKUP (state_refs s1) n = r1
  ==>
        (?r2. FLOOKUP (state_refs s2) n = r2 /\ OPTREL ref_rel r1
          r2)) /\
     (clos_fvsProof_state_rel s1 s2 /\ FLOOKUP (state_refs s2) n =
       r2 ==>
        (?r1. FLOOKUP (state_refs s1) n = r1 /\ OPTREL ref_rel r1
          r2))`)
  CHEAT_TAC;;

let clos_fvsProof_state_rel_clocks_eqs =
  cake_theorem "state_rel_clocks_eqs[local]"
  (fun () ->
    `clos_fvsProof_state_rel s1 s2 ==> state_clock s1 = state_clock s2`)
  CHEAT_TAC;;

let clos_fvsProof_state_rel_dec_clock =
  cake_theorem "state_rel_dec_clock[local]"
  (fun () ->
    `clos_fvsProof_state_rel s1 s2 ==> clos_fvsProof_state_rel
  (closSem_dec_clock 1 s1) (closSem_dec_clock 1 s2)`)
  CHEAT_TAC;;

let clos_fvsProof_rel_update_thunk =
  cake_theorem "rel_update_thunk[local]"
  (fun () ->
    `clos_fvsProof_state_rel s1 s2 /\
     LIST_REL clos_fvsProof_v_rel vs ys ==>
       (update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs =
         NONE ==>
          update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys =
            NONE) /\
       (update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs =
         SOME refs1 ==>
          (?refs2. update_thunk [closSem_RefPtr v ptr] (state_refs
            s2) ys = SOME refs2 /\
                  clos_fvsProof_state_rel (state_refs_fupd (K
                    refs1) s1) (state_refs_fupd (K refs2) s2)))`)
  CHEAT_TAC;;

(* evaluate level correctness *)

let evaluate_remove_fvs = cake_theorem "evaluate_remove_fvs"
  (fun () ->
    `(!xs env1 (s1:('c,'ffi)closSem_state) res1 s2 ys env2 t1.
        closSem_evaluate (xs,env1,s1) = (res1,s2) /\
        LIST_REL clos_fvsProof_v_rel env1 env2 /\
          clos_fvsProof_state_rel s1 t1 /\
        clos_fvsProof_code_rel (LENGTH env1) xs ys ==>
        (?res2 t2.
          closSem_evaluate (ys,env2,t1) = (res2,t2) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
          clos_fvsProof_state_rel s2 t2)) /\
     (!loc_opt f1 args1 (s1:('c,'ffi)closSem_state) res1 s2 f2
       args2 t1.
        evaluate_app loc_opt f1 args1 s1 = (res1,s2) /\
        clos_fvsProof_v_rel f1 f2 /\ LIST_REL clos_fvsProof_v_rel
          args1 args2 /\
        clos_fvsProof_state_rel s1 t1 ==>
        (?res2 t2.
          evaluate_app loc_opt f2 args2 t1 = (res2,t2) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
          clos_fvsProof_state_rel s2 t2))`)
  CHEAT_TAC;;

let remove_fvs_correct = cake_theorem "remove_fvs_correct"
  (fun () ->
    `!xs env1 (s1:('c,'ffi)closSem_state) res1 s2 env2 t1.
         closSem_evaluate (xs,env1,s1) = (res1,s2) /\
         LIST_REL clos_fvsProof_v_rel env1 env2 /\
           clos_fvsProof_state_rel s1 t1 ==>
         (?res2 t2.
           closSem_evaluate (remove_fvs (LENGTH env1) xs,env2,t1) =
             (res2,t2) /\
           semanticPrimitivesProps_result_rel (LIST_REL
             clos_fvsProof_v_rel) clos_fvsProof_v_rel res1 res2 /\
           clos_fvsProof_state_rel s2 t2)`)
  CHEAT_TAC;;

(* preservation of observational semantics *)

let clos_fvsProof_semantics_compile = cake_theorem "semantics_compile"
  (fun () ->
    `~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc clos_fvs_compile_inc cc) xs = ffi_Fail) ==>
        (!n. SND (SND (co n)) = []) /\ 1 <= max_app ==>
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          (pure_co clos_fvs_compile_inc o co) cc (clos_fvs_compile
            xs) =
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (pure_cc clos_fvs_compile_inc cc) xs`)
  CHEAT_TAC;;

(* syntactic properties *)

let code_locs_remove_fvs = cake_theorem "code_locs_remove_fvs[simp]"
  (fun () ->
    `!fvs xs. code_locs (remove_fvs fvs xs) = code_locs xs`)
  CHEAT_TAC;;

let fv_max_remove_fvs = cake_theorem "fv_max_remove_fvs"
  (fun () ->
    `!fvs xs.
      every_Fn_vs_NONE xs ==>
      (!v. fv v (remove_fvs fvs xs) ==> v < fvs)`)
  CHEAT_TAC;;

let remove_fvs_every_Fn_SOME =
  cake_theorem "remove_fvs_every_Fn_SOME[simp]"
  (fun () ->
    `!fvs es. every_Fn_SOME (remove_fvs fvs es) <=> every_Fn_SOME es`)
  CHEAT_TAC;;

let remove_fvs_every_Fn_vs_NONE =
  cake_theorem "remove_fvs_every_Fn_vs_NONE[simp]"
  (fun () ->
    `!fvs es. every_Fn_vs_NONE (remove_fvs fvs es) <=>
  every_Fn_vs_NONE es`)
  CHEAT_TAC;;

let remove_fvs_set_globals = cake_theorem "remove_fvs_set_globals[simp]"
  (fun () ->
    `!fvs x. MAP closProps_set_globals (remove_fvs fvs x) = MAP
  closProps_set_globals x`)
  CHEAT_TAC;;

let set_globals_HD_remove_fvs_SING =
  cake_theorem "set_globals_HD_remove_fvs_SING[simp]"
  (fun () ->
    `closProps_set_globals (HD (remove_fvs fvs [x])) =
  closProps_set_globals x`)
  CHEAT_TAC;;

let remove_fvs_esgc_free = cake_theorem "remove_fvs_esgc_free[simp]"
  (fun () ->
    `!fvs x. EVERY closProps_esgc_free (remove_fvs fvs x) <=> EVERY
  closProps_esgc_free x`)
  CHEAT_TAC;;

let remove_fvs_elist_globals =
  cake_theorem "remove_fvs_elist_globals[simp]"
  (fun () ->
    `closProps_elist_globals (remove_fvs fvs xs) =
  closProps_elist_globals xs`)
  CHEAT_TAC;;

let EVERY_remove_fvs_sing = cake_theorem "EVERY_remove_fvs_sing"
  (fun () ->
    `EVERY f (remove_fvs n [y]) <=> f (HD (remove_fvs n [y]))`)
  CHEAT_TAC;;

let remove_fvs_no_Labels = cake_theorem "remove_fvs_no_Labels"
  (fun () ->
    `!n xs. EVERY no_Labels (remove_fvs n xs) = EVERY no_Labels xs`)
  CHEAT_TAC;;

let remove_fvs_obeys_max_app = cake_theorem "remove_fvs_obeys_max_app"
  (fun () ->
    `!n xs. EVERY (obeys_max_app k) (remove_fvs n xs) = EVERY
  (obeys_max_app k) xs`)
  CHEAT_TAC;;

let get_code_labels_remove_fvs =
  cake_theorem "get_code_labels_remove_fvs[simp]"
  (fun () ->
    `!n es. MAP closProps_get_code_labels (remove_fvs n es) = MAP
  closProps_get_code_labels es`)
  CHEAT_TAC;;
