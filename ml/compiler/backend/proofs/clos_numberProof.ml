(* ======================================================== *)
(*  clos_numberProof: ported from HOL4's
    compiler/backend/proofs/clos_numberProofScript.sml
    A proof theory about clos_number.ml, with 2 definitions and 47
    theorems.  Needed by clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_number
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sorting.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_numberProof"
  ["backendProps"; "closLang"; "closProps"; "closSem"; "clos_number"];;

hol4_overload "lookup" "sptree_lookup";;
hol4_overload "insert" "sptree_insert";;
hol4_overload "delete" "sptree_delete";;
hol4_overload "map" "sptree_map";;
hol4_overload "wf" "sptree_wf";;

(* properties of renumber_code_locs *)

(* HOL4 clos_numberProofScript.sml:20-36: a proof *)

let renumber_code_locs_list_IMP_LENGTH = prove
 (`renumber_code_locs_list loc es = (l1,es2) ==> LENGTH es2 = LENGTH
  es`,
  CHEAT_TAC);;

let renumber_code_locs_inc = prove
 (`(!n es. n <= FST (renumber_code_locs_list n es)) /\
    (!n e. n <= FST (renumber_code_locs n e))`,
  CHEAT_TAC);;

let renumber_code_locs_imp_inc = prove
 (`(renumber_code_locs_list n es = (m,vs) ==> n <= m) /\
    (renumber_code_locs n e = (z,v) ==> n <= z)`,
  CHEAT_TAC);;

let renumber_code_locs_list_length = prove
 (`!ls n x y. renumber_code_locs_list n ls = (x,y) ==> LENGTH y =
  LENGTH ls`,
  CHEAT_TAC);;

(* [local] *)
let renumber_code_locs_distinct_lemma = prove
 (`(!n es. SORTED (<) (code_locs (SND (renumber_code_locs_list n es)))
  /\
            EVERY ((<=) n) (code_locs (SND (renumber_code_locs_list n
              es))) /\
            EVERY ((>) (FST (renumber_code_locs_list n es)))
              (code_locs (SND (renumber_code_locs_list n es)))) /\
    (!n e. SORTED (<) (code_locs [SND (renumber_code_locs n e)]) /\
            EVERY ((<=) n) (code_locs [SND (renumber_code_locs n e)])
              /\
            EVERY ((>) (FST (renumber_code_locs n e))) (code_locs
              [SND (renumber_code_locs n e)]))`,
  CHEAT_TAC);;

let renumber_code_locs_distinct = prove
 (`!n e. ALL_DISTINCT (code_locs [SND (renumber_code_locs n e)]) /\
          EVERY ((<=) n) (code_locs [SND (renumber_code_locs n e)])
            /\
          EVERY ((>) (FST (renumber_code_locs n e))) (code_locs
            [SND (renumber_code_locs n e)])`,
  CHEAT_TAC);;

let renumber_code_locs_list_distinct = prove
 (`!n es.
     ALL_DISTINCT (code_locs (SND (renumber_code_locs_list n es))) /\
     EVERY ((<=) n) (code_locs (SND (renumber_code_locs_list n es)))
       /\
     EVERY ((>) (FST (renumber_code_locs_list n es)))
           (code_locs (SND (renumber_code_locs_list n es)))`,
  CHEAT_TAC);;

(* [local] *)
let renumber_code_locs_list_els = prove
 (`!ls ls' n n'. renumber_code_locs_list n ls = (n',ls') ==>
       (!x. x < LENGTH ls ==>
         (?m. EL x ls' = SND (renumber_code_locs m (EL x ls))))`,
  CHEAT_TAC);;

(* value relation *)

let clos_numberProof_v_rel = cake_inductive
  `(clos_numberProof_v_rel max_app (closSem_Number j) (closSem_Number
  j)) /\
   (clos_numberProof_v_rel max_app (Word64 w) (Word64 w)) /\
   (EVERY2 (clos_numberProof_v_rel max_app) (xs:closSem_v list)
     (ys:closSem_v list) ==>
    clos_numberProof_v_rel max_app (closSem_Block t xs)
      (closSem_Block t ys)) /\
   (clos_numberProof_v_rel max_app (closSem_ByteVector ws)
     (closSem_ByteVector ws)) /\
   (clos_numberProof_v_rel max_app (closSem_RefPtr b r1)
     (closSem_RefPtr b r1)) /\
   (LIST_REL (clos_numberProof_v_rel max_app) env env' /\
    LIST_REL (clos_numberProof_v_rel max_app) argenv argenv' /\
    ~(contains_App_SOME max_app [c]) /\
    c' = SND (renumber_code_locs n c) ==>
    clos_numberProof_v_rel max_app (Closure p argenv env num_args c)
      (Closure p' argenv' env' num_args c')) /\
   (
    LIST_REL (clos_numberProof_v_rel max_app) env env' /\
    LIST_REL (clos_numberProof_v_rel max_app) argenv argenv' /\
    ~(contains_App_SOME max_app (MAP SND es)) /\
    es' = ZIP (MAP FST es) (SND (renumber_code_locs_list n (MAP SND
      es))) ==>
    clos_numberProof_v_rel max_app (Recclosure p argenv env es k)
      (Recclosure p' argenv' env' es' k))`;;
hol4_overload "v_rel" "clos_numberProof_v_rel";;

let clos_numberProof_state_rel_def = new_definition
  `clos_numberProof_state_rel (s:(num#'c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (closSem_state_clock s = closSem_state_clock t) /\
       (closSem_state_ffi s = closSem_state_ffi t) /\
       (closSem_state_max_app t = closSem_state_max_app s) /\
       closSem_state_compile
     s = state_cc (ignore_table clos_number_compile_inc)
       (closSem_state_compile t) /\ closSem_state_compile_oracle
     t = state_co (ignore_table clos_number_compile_inc)
       (closSem_state_compile_oracle s) /\
     fmap_rel (closProps_ref_rel (clos_numberProof_v_rel
       (closSem_state_max_app s))) (closSem_state_refs s)
       (closSem_state_refs t) /\
     EVERY2 (OPTREL (clos_numberProof_v_rel (closSem_state_max_app
       s))) (closSem_state_globals s) (closSem_state_globals t) /\
     (!n. SND (SND (closSem_state_compile_oracle s n)) = [] /\
          ~(contains_App_SOME (closSem_state_max_app s) (FST (SND
            (closSem_state_compile_oracle s n))))) /\ closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY`;;
hol4_overload "state_rel" "clos_numberProof_state_rel";;

(* state_rel_max_app[local] *)
let clos_numberProof_state_rel_max_app = prove
 (`!s t. clos_numberProof_state_rel s t ==> closSem_state_max_app s =
  closSem_state_max_app t`,
  CHEAT_TAC);;

(* state_rel_with_clock[local] *)
let clos_numberProof_state_rel_with_clock = prove
 (`!s t. clos_numberProof_state_rel s t ==> clos_numberProof_state_rel
  (state_clock_fupd (K x) s) (state_clock_fupd (K x) t)`,
  CHEAT_TAC);;

(* state_rel_clock[local] *)
let clos_numberProof_state_rel_clock = prove
 (`clos_numberProof_state_rel s t ==> state_clock s = state_clock t`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_globals = prove
 (`clos_numberProof_state_rel s t ==>
     LIST_REL (OPTREL (clos_numberProof_v_rel
       (closSem_state_max_app s))) (closSem_state_globals s)
       (closSem_state_globals t)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_refs = prove
 (`clos_numberProof_state_rel s t ==>
     fmap_rel (closProps_ref_rel (clos_numberProof_v_rel
       (closSem_state_max_app t))) (state_refs s) (state_refs t)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_code = prove
 (`clos_numberProof_state_rel s t ==> closSem_state_code s = FEMPTY /\
  closSem_state_code t = FEMPTY`,
  CHEAT_TAC);;

(* HOL4 clos_numberProofScript.sml:246-262: a theorem that HOL4
   states as the value of an ML expression: v_rel_simp *)

(* v_rel_Boolv[simp] *)
let clos_numberProof_v_rel_Boolv = prove
 (`(clos_numberProof_v_rel max_app x (Boolv b) <=> (x = Boolv b)) /\
    (clos_numberProof_v_rel max_app (Boolv b) x <=> (x = Boolv b))`,
  CHEAT_TAC);;

(* v_rel_Unit[simp] *)
let clos_numberProof_v_rel_Unit = prove
 (`(clos_numberProof_v_rel max_app x closSem_Unit <=> (x =
  closSem_Unit)) /\
    (clos_numberProof_v_rel max_app closSem_Unit x <=> (x =
      closSem_Unit))`,
  CHEAT_TAC);;

(* semantic functions respect relation *)

(* [local] *)
let dest_closure_v_rel_none = prove
 (`!f args f' args'.
     clos_numberProof_v_rel max_app f f' /\
     LIST_REL (clos_numberProof_v_rel max_app) args args' /\
     dest_closure max_app NONE f args = NONE ==>
     dest_closure max_app NONE f' args' = NONE`,
  CHEAT_TAC);;

(* [local] *)
let dest_closure_v_rel_partial = prove
 (`!c f args f' args'.
     clos_numberProof_v_rel max_app f f' /\
     LIST_REL (clos_numberProof_v_rel max_app) args args' /\
     dest_closure max_app NONE f args = SOME (Partial_app c) ==>
     (?c'.
       dest_closure max_app NONE f' args' = SOME (Partial_app c') /\
       clos_numberProof_v_rel max_app c c')`,
  CHEAT_TAC);;

(* [local] *)
let dest_closure_v_rel_full = prove
 (`!c f args f' args' args1 args2.
     clos_numberProof_v_rel max_app f f' /\
     LIST_REL (clos_numberProof_v_rel max_app) args args' /\
     dest_closure max_app NONE f args = SOME (Full_app exp args1
       args2) ==>
     (?args1' args2' n.
       dest_closure max_app NONE f' args' = SOME (Full_app (SND
         (renumber_code_locs n exp)) args1' args2') /\
       LIST_REL (clos_numberProof_v_rel max_app) args1 args1' /\
       LIST_REL (clos_numberProof_v_rel max_app) args2 args2' /\
       ~(contains_App_SOME max_app [exp]))`,
  CHEAT_TAC);;

(* [local] *)
let helper = prove
 (`SND ((\(n',x'). (n',[x'])) x) = [SND x]`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_Boolv_mono = prove
 (`(x <=> y) ==> (clos_numberProof_v_rel max_app (Boolv x) (Boolv y))`,
  CHEAT_TAC);;

(* v_to_list[local] *)
let clos_numberProof_v_to_list = prove
 (`!x y. clos_numberProof_v_rel max_app x y ==>
           OPTREL (LIST_REL (clos_numberProof_v_rel max_app))
             (v_to_list x) (v_to_list y)`,
  CHEAT_TAC);;

(* simple_val_rel *)
let clos_numberProof_simple_val_rel = prove
 (`closProps_simple_val_rel (clos_numberProof_v_rel max_app_n)`,
  CHEAT_TAC);;

(* simple_state_rel *)
let clos_numberProof_simple_state_rel = prove
 (`closProps_simple_state_rel (clos_numberProof_v_rel max_app_n)
     (\s t. closSem_state_max_app s = max_app_n /\
       clos_numberProof_state_rel s t)`,
  CHEAT_TAC);;

(* HOL4 clos_numberProofScript.sml:467-472: ML code, not ported *)

(* do_app_lemma *)
let clos_numberProof_do_app_lemma = prove
 (`clos_numberProof_state_rel s t /\ LIST_REL (clos_numberProof_v_rel
  (closSem_state_max_app s)) xs ys ==>
    (match do_app opp xs s with
      Rval (x,s1) ->
        (?y t1.
          clos_numberProof_v_rel (closSem_state_max_app s) x y /\
          (closSem_state_max_app s1 = closSem_state_max_app s /\
            clos_numberProof_state_rel s1 t1) /\
          do_app opp ys t = Rval (y,t1)) | Rerr err1 ->
        (?err2.
          do_app opp ys t = Rerr err2 /\
          exc_rel (clos_numberProof_v_rel (closSem_state_max_app
            s)) err1 err2))`,
  CHEAT_TAC);;

(* list_to_v_v_rel *)
let clos_numberProof_list_to_v_v_rel = prove
 (`!xs ys.
     LIST_REL (clos_numberProof_v_rel ap) xs ys ==>
       clos_numberProof_v_rel ap (list_to_v xs) (list_to_v ys)`,
  CHEAT_TAC);;

(* [local] *)
let do_app = prove
 (`clos_numberProof_state_rel s1 s2 /\
     LIST_REL (clos_numberProof_v_rel (closSem_state_max_app s1)) x1
       x2 ==>
     (!err.
       do_app op x1 s1 = (Rerr err) ==>
       do_app op x2 s2 = (Rerr err)) /\
     (!v1 w1. do_app op x1 s1 = Rval (v1,w1) ==>
              (?v2 w2. do_app op x2 s2 = Rval (v2,w2) /\
                      clos_numberProof_v_rel (closSem_state_max_app
                        s1) v1 v2 /\ clos_numberProof_state_rel w1
                        w2))`,
  CHEAT_TAC);;

(* v_to_bytes[local] *)
let clos_numberProof_v_to_bytes = prove
 (`clos_numberProof_v_rel m v w ==> closSem_v_to_bytes v =
  closSem_v_to_bytes w`,
  CHEAT_TAC);;

(* v_to_words[local] *)
let clos_numberProof_v_to_words = prove
 (`clos_numberProof_v_rel m v w ==> closSem_v_to_words v =
  closSem_v_to_words w`,
  CHEAT_TAC);;

(* HOL4 clos_numberProofScript.sml:531-538: ML code, not ported *)

let ignore_table_imp = prove
 (`ignore_table f st p = (st',p') ==> SND p' = SND p`,
  CHEAT_TAC);;

(* [local] *)
let do_install = prove
 (`clos_numberProof_state_rel s1 s2 /\
    LIST_REL (clos_numberProof_v_rel (closSem_state_max_app s1)) x1
      x2 ==>
    (!err t. closSem_do_install x1 s1 = (Rerr (Rabort
      Rtimeout_error),t) ==>
             (?t'. closSem_do_install x2 s2 = (Rerr (Rabort
               Rtimeout_error),t') /\
                  clos_numberProof_state_rel t t')) /\
    (!e1 t1. closSem_do_install x1 s1 = (Rval e1,t1) ==>
      (?e2 t2. closSem_do_install x2 s2 = (Rval e2,t2) /\
              ~(contains_App_SOME (closSem_state_max_app t1) (e1)) /\
                closSem_state_max_app t1 = closSem_state_max_app s1 /\
              e2 = SND (clos_number_compile_inc (FST (FST
                (closSem_state_compile_oracle s1 0))) e1) /\
              clos_numberProof_state_rel t1 t2))`,
  CHEAT_TAC);;

(* compiler correctness *)

let lookup_vars_NONE_related_env = prove
 (`LIST_REL (clos_numberProof_v_rel max_app) e1 e2 ==>
   (lookup_vars vs e1 = NONE <=> lookup_vars vs e2 = NONE)`,
  CHEAT_TAC);;

let lookup_vars_SOME_related_env = prove
 (`LIST_REL (clos_numberProof_v_rel max_app) e1 e2 /\ lookup_vars vs e1
  = SOME e1' /\
   lookup_vars vs e2 = SOME e2' ==> LIST_REL
     (clos_numberProof_v_rel max_app) e1' e2'`,
  CHEAT_TAC);;

(* rel_update_thunk[local] *)
let clos_numberProof_rel_update_thunk = prove
 (`clos_numberProof_state_rel s1 s2 /\
   LIST_REL (clos_numberProof_v_rel (closSem_state_max_app s1)) vs ys
     /\
   update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs = SOME
     refs1 ==>
     (?refs2. update_thunk [closSem_RefPtr v ptr] (state_refs s2) ys
       = SOME refs2 /\
             clos_numberProof_state_rel (state_refs_fupd (K refs1)
               s1) (state_refs_fupd (K refs2) s2))`,
  CHEAT_TAC);;

(* HOL4 clos_numberProofScript.sml:637-645: code that the source has
   in a comment *)

let renumber_code_locs_correct = prove
 (`(!tmp xs env (s1:(num#'c,'ffi)closSem_state) env' t1 res s2 n.
     tmp = (xs,env,s1) /\
     (closSem_evaluate (xs,env,s1) = (res,s2)) /\ ~(res = Rerr
       (Rabort Rtype_error)) ==>
     ~(contains_App_SOME (closSem_state_max_app s1) xs) /\
     LIST_REL (clos_numberProof_v_rel (closSem_state_max_app s1)) env
       env' /\
     clos_numberProof_state_rel s1 t1 ==>
     (?res' t2.
        (closSem_evaluate (SND (renumber_code_locs_list n
          xs),env',t1) = (res',t2)) /\
        semanticPrimitivesProps_result_rel (LIST_REL
          (clos_numberProof_v_rel (closSem_state_max_app s1)))
          (clos_numberProof_v_rel (closSem_state_max_app s1)) res res'
          /\
        clos_numberProof_state_rel s2 t2)) /\
   (!loc f args (s:(num#'c,'ffi)closSem_state) res s2 f' args' t1.
       evaluate_app loc f args s = (res,s2) /\ ~(res = Rerr (Rabort
         Rtype_error)) ==>
       clos_numberProof_v_rel (closSem_state_max_app s) f f' /\
       loc = NONE /\
       LIST_REL (clos_numberProof_v_rel (closSem_state_max_app s))
         args args' /\
       clos_numberProof_state_rel s t1 ==>
       (?res' t2.
          (evaluate_app loc f' args' t1 = (res',t2)) /\
          semanticPrimitivesProps_result_rel (LIST_REL
            (clos_numberProof_v_rel (closSem_state_max_app s)))
            (clos_numberProof_v_rel (closSem_state_max_app s)) res res'
            /\
          clos_numberProof_state_rel s2 t2))`,
  CHEAT_TAC);;

let renumber_code_locs_every_Fn_SOME = prove
 (`(!n es. every_Fn_SOME (SND (renumber_code_locs_list n es))) /\
   (!n e. every_Fn_SOME [SND (renumber_code_locs n e)])`,
  CHEAT_TAC);;

let renumber_code_locs_every_Fn_vs_NONE = prove
 (`(!n es. every_Fn_vs_NONE (SND (renumber_code_locs_list n es)) <=>
           every_Fn_vs_NONE es) /\
   (!n e. every_Fn_vs_NONE [SND (renumber_code_locs n e)] <=>
          every_Fn_vs_NONE [e])`,
  CHEAT_TAC);;

let renumber_code_locs_EVEN = prove
 (`(!n es. EVEN n ==> EVEN (FST (renumber_code_locs_list n es)) /\ EVERY
  EVEN (code_locs (SND (renumber_code_locs_list n es)))) /\
   (!n e. EVEN n ==> EVEN (FST (renumber_code_locs n e)) /\ EVERY
     EVEN (code_locs [SND (renumber_code_locs n e)]))`,
  CHEAT_TAC);;

let renumber_code_locs_elist_globals = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') ==>
      closProps_elist_globals es' = closProps_elist_globals es) /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') ==>
      closProps_set_globals e' = closProps_set_globals e)`,
  CHEAT_TAC);;

let renumber_code_locs_esgc_free = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') /\ EVERY
        closProps_esgc_free es ==>
      EVERY closProps_esgc_free es') /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') /\ closProps_esgc_free e
        ==> closProps_esgc_free e')`,
  CHEAT_TAC);;

let renumber_code_locs_obeys_max_app = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') /\ EVERY
        (obeys_max_app m) es ==>
      EVERY (obeys_max_app m) es') /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') /\ obeys_max_app m e ==>
        obeys_max_app m e')`,
  CHEAT_TAC);;

let renumber_code_locs_no_Labels = prove
 (`(!loc es n es'.
      renumber_code_locs_list loc es = (n,es') /\ EVERY no_Labels es
        ==>
      EVERY no_Labels es') /\
   (!loc e n e'.
      renumber_code_locs loc e = (n,e') /\ no_Labels e ==>
        no_Labels e')`,
  CHEAT_TAC);;

let renumber_code_locs_imp_EVEN = prove
 (`(renumber_code_locs_list n es = (n',es') /\ EVEN n ==> EVEN n') /\
   (renumber_code_locs n e = (n',e') /\ EVEN n ==> EVEN n')`,
  CHEAT_TAC);;

let renumber_code_locs_get_code_labels = prove
 (`(!n es n' es'. renumber_code_locs_list n es = (n',es') /\ EVERY ((=)
  {}) (MAP closProps_get_code_labels es) /\ EVEN n ==>
      BIGUNION (set_of_list (MAP closProps_get_code_labels es')) = {n
        + 2 * k | k | n + 2 * k < n'}) /\
   (!n e n' e'. renumber_code_locs n e = (n',e') /\
     closProps_get_code_labels e = {} /\ EVEN n ==>
     closProps_get_code_labels e' = {n + 2 * k | k | n + 2 * k <
       n'})`,
  CHEAT_TAC);;

let renumber_code_locs_any_dests = prove
 (`(!k xs n ys. renumber_code_locs_list k xs = (n,ys) ==>
  (app_call_dests NONE) ys = {}) /\
    (!k x n y. renumber_code_locs k x = (n,y) ==> (app_call_dests
      NONE) [y] = {})`,
  CHEAT_TAC);;

(* preservation of observable semantics *)

let semantics_number = prove
 (`~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY co
        (state_cc (ignore_table clos_number_compile_inc) cc) xs =
          ffi_Fail) ==>
      ~(contains_App_SOME max_app xs) /\
      (!n.
         SND (SND (co n)) = [] /\
         ~(contains_App_SOME max_app (FST (SND (co n))))) ==>
      closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        (state_co (ignore_table clos_number_compile_inc) co) cc
           (SND (renumber_code_locs_list n xs)) =
      closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
        co (state_cc (ignore_table clos_number_compile_inc) cc) xs`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
