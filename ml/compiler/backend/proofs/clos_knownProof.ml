(* ======================================================== *)
(*  clos_knownProof: ported from HOL4's
    compiler/backend/proofs/clos_knownProofScript.sml
    A proof theory about clos_known.ml, with 40 definitions and 188
    theorems.  Needed by backendProof.ml and clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_known
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_fvs.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/proofs/clos_fvsProof.ml";;
needs "compiler/backend/proofs/clos_knownProps.ml";;
needs "compiler/backend/proofs/clos_letopProof.ml";;
needs "compiler/backend/proofs/clos_opProof.ml";;
needs "compiler/backend/proofs/clos_ticksProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/mergesort.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 clos_knownProofScript.sml:19: an overload that the source
   brings to the front: domain *)

(* HOL4 clos_knownProofScript.sml:21-22: ML code, not ported *)

(* fixeqs flips any equations in the assumption that have evaluate on the rhs *)
(* HOL4 clos_knownProofScript.sml:25: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_knownProofScript.sml:27: ML code, not ported *)

(* HOL4 clos_knownProofScript.sml:29: ML code, not ported *)

(* HOL4 clos_knownProofScript.sml:31: ML code, not ported *)

(* simple properties of constants from clos_known: i.e., merge and known *)

let known_op_changed_globals = cake_theorem "known_op_changed_globals"
  (fun () ->
    `!opn aenv g0 a g.
       known_op opn aenv g0 = (a,g) ==>
       (!i. i IN domain g /\ (i IN domain g0 ==> ~(sptree_lookup i
         g = sptree_lookup i g0)) ==>
           i IN SET_OF_BAG (closProps_op_gbag opn))`)
  CHEAT_TAC;;

let known_changed_globals = cake_theorem "known_changed_globals"
  (fun () ->
    `!c xs aenv g0 alist g.
       known c xs aenv g0 = (alist,g) ==>
       (!i. i IN domain g /\ (i IN domain g0 ==> ~(sptree_lookup i
         g = sptree_lookup i g0)) ==>
           i IN SET_OF_BAG (closProps_elist_globals xs))`)
  CHEAT_TAC;;

let known_unchanged_globals = cake_theorem "known_unchanged_globals"
  (fun () ->
    `!c xs aenv g0 eas1 g1.
       known c xs aenv g0 = (eas1,g1) /\
       closProps_elist_globals xs = EMPTY_BAG ==> g0 = g1`)
  CHEAT_TAC;;


let known_op_changed_globals_alt =
  cake_theorem "known_op_changed_globals_alt"
  (fun () ->
    `!opn aenv g0 a g.
       known_op opn aenv g0 = (a,g) ==>
         BAG_OF_SET (domain g) <= (BAG_UNION) (BAG_OF_SET (domain
           g0)) (closProps_op_gbag opn)`)
  CHEAT_TAC;;

let known_op_changed_globals_alt_set =
  cake_theorem "known_op_changed_globals_alt_set"
  (fun () ->
    `!opn aenv g0 a g.
       known_op opn aenv g0 = (a,g) ==>
         domain g SUBSET domain g0 UNION SET_OF_BAG
           (closProps_op_gbag opn)`)
  CHEAT_TAC;;

let known_changed_globals_alt = cake_theorem "known_changed_globals_alt"
  (fun () ->
    `!c xs aenv g0 alist g.
       known c xs aenv g0 = (alist,g) ==>
         BAG_OF_SET (domain g) <= (BAG_UNION) (BAG_OF_SET (domain
           g0)) (closProps_elist_globals xs)`)
  CHEAT_TAC;;

let known_changed_globals_alt_set =
  cake_theorem "known_changed_globals_alt_set"
  (fun () ->
    `!c xs aenv g0 alist g.
       known c xs aenv g0 = (alist,g) ==>
         domain g SUBSET domain g0 UNION SET_OF_BAG
           (closProps_elist_globals xs)`)
  CHEAT_TAC;;

(* Take the first n expression lists returned by the compile oracle. *)
let first_n_exps_def = cake_define
  `first_n_exps co n = GENLIST (FST o SND o co) n`;;

let first_n_exps_shift_seq = cake_theorem "first_n_exps_shift_seq"
  (fun () ->
    `!co n k. first_n_exps co (n + k) = first_n_exps co k ++
  first_n_exps (misc_shift_seq k co) n`)
  CHEAT_TAC;;

let MEM_first_n_exps = cake_theorem "MEM_first_n_exps"
  (fun () ->
    `!k n. k < n ==> (!co. MEM (FST (SND (co k))) (first_n_exps co n))`)
  CHEAT_TAC;;

(* All globals set in the program and in code returned by
   the compile oracle are unique. *)
let unique_set_globals_def = cake_define
  `unique_set_globals es co <=>
     (!n. BAG_ALL_DISTINCT (closProps_elist_globals (es ++ FLAT
       (first_n_exps co n))))`;;

let unique_set_globals_shift_seq =
  cake_theorem "unique_set_globals_shift_seq"
  (fun () ->
    `!es co. unique_set_globals es co ==> (!k. unique_set_globals es
  (misc_shift_seq k co))`)
  CHEAT_TAC;;

let unique_set_globals_evaluate =
  cake_theorem "unique_set_globals_evaluate"
  (fun () ->
    `!es xs env s1 s2 res. unique_set_globals xs
  (closSem_state_compile_oracle s1) /\
     closSem_evaluate (es,env,s1) = (res,s2) ==>
       unique_set_globals xs (closSem_state_compile_oracle s2)`)
  CHEAT_TAC;;

let unique_set_globals_subexps =
  cake_theorem "unique_set_globals_subexps"
  (fun () ->
    `(unique_set_globals (x1 :: x2 :: xs) co ==>
        unique_set_globals [x1] co /\ unique_set_globals (x2 :: xs)
          co) /\
     (unique_set_globals [If t x1 x2 x3] co ==>
        unique_set_globals [x1] co /\ unique_set_globals [x2] co /\
          unique_set_globals [x3] co) /\
     (unique_set_globals [Let t xs x2] co ==>
        unique_set_globals xs co /\ unique_set_globals [x2] co) /\
     (unique_set_globals [Raise t x1] co ==>
        unique_set_globals [x1] co) /\
     (unique_set_globals [Handle t x1 x2] co ==>
        unique_set_globals [x1] co /\ unique_set_globals [x2] co)
          /\
     (unique_set_globals [closLang_Op t opn xs] co ==>
        unique_set_globals xs co) /\
     (
      // /\ !n. BAG_ALL_DISTINCT (op_gbag opn ⊎ (elist_globals (first_n_exps co n)))
      unique_set_globals [closLang_Fn src_name loc_opt vsopt
        num_args x1] co ==>
        unique_set_globals [x1] co) /\
     (unique_set_globals [Letrec src_names loc_opt vsopt fns x1] co
       ==>
        unique_set_globals [x1] co /\ unique_set_globals (MAP SND
          fns) co) /\
     (unique_set_globals [App t loc_opt x1 xs] co ==>
        unique_set_globals [x1] co /\ unique_set_globals xs co) /\
     (unique_set_globals [closLang_Tick t x1] co ==>
        unique_set_globals [x1] co) /\
     (unique_set_globals [closLang_Call t ticks dest xs] co ==>
        unique_set_globals xs co)`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:224: ML code, not ported *)

let unique_set_globals_IMP_es_distinct_elist_globals =
  cake_theorem "unique_set_globals_IMP_es_distinct_elist_globals"
  (fun () ->
    `!es co. unique_set_globals es co ==> BAG_ALL_DISTINCT
  (closProps_elist_globals es)`)
  CHEAT_TAC;;

let set_globals_empty_unique_set_globals =
  cake_theorem "set_globals_empty_unique_set_globals"
  (fun () ->
    `closProps_set_globals e = EMPTY_BAG ==> (unique_set_globals [e]
  co <=> unique_set_globals [] co)`)
  CHEAT_TAC;;

let nil_unique_set_globals = cake_theorem "nil_unique_set_globals"
  (fun () ->
    `unique_set_globals es co ==> unique_set_globals [] co`)
  CHEAT_TAC;;


(* Value approximation is sgc free *)

let _ = size_thms "val_approx";;
let val_approx_sgc_free_def = cake_define_wf
  `MEASURE val_approx_size`
  `val_approx_sgc_free x1 =
        match x1 with
          clos_known_ClosNoInline m n -> T
        | (clos_known_Clos m n e s) -> closProps_set_globals e =
          EMPTY_BAG
        | (clos_known_Tuple tag vas) -> EVERY val_approx_sgc_free vas
        | _1 -> T`;;

(* HOL4 clos_knownProofScript.sml:257-258: a theorem that HOL4 states
   as the value of an ML expression: val_approx_sgc_free_def *)

let val_approx_sgc_free_merge = cake_theorem "val_approx_sgc_free_merge"
  (fun () ->
    `!a1 a2. val_approx_sgc_free a1 /\ val_approx_sgc_free a2 ==>
     val_approx_sgc_free (merge a1 a2)`)
  CHEAT_TAC;;

let globals_approx_sgc_free_def = cake_define
  `globals_approx_sgc_free g <=>
   (!n a. sptree_lookup n g = SOME a ==> val_approx_sgc_free a)`;;

(* alternative val_approx to value relation *)

let val_approx_val = cake_inductive
  `(!v. val_approx_val clos_known_Other v) /\
   (!i. val_approx_val (Int i) (closSem_Number i)) /\
   (!tg vas vs.
      LIST_REL val_approx_val vas vs ==>
      val_approx_val (clos_known_Tuple tg vas) (closSem_Block tg vs))
        /\
   (!m n env b. val_approx_val (clos_known_ClosNoInline m n) (Closure
     (SOME m) [] env n b)) /\
   (!m n env base fs j.
      m = base + 2 * j /\ j < LENGTH fs /\ n = FST (EL j fs) ==>
      val_approx_val (clos_known_ClosNoInline m n) (Recclosure (SOME
        base) [] env fs j)) /\
   (!m n b s env. val_approx_val (clos_known_Clos m n b s)
     (Closure (SOME m) [] env n b))`;;

(* HOL4 clos_knownProofScript.sml:294-302: a theorem that HOL4 states
   as the value of an ML expression: val_approx_val_simps *)

let val_approx_val_merge_I_lemma =
  cake_theorem "val_approx_val_merge_I_lemma"
  (fun () ->
    `!a1 v. val_approx_val a1 v ==> (!a2. val_approx_val (merge a1 a2)
  v)`)
  CHEAT_TAC;;

let val_approx_val_merge_I = cake_theorem "val_approx_val_merge_I"
  (fun () ->
    `!a1 v a2.
       val_approx_val a1 v \/ val_approx_val a2 v ==>
       val_approx_val (merge a1 a2) v`)
  CHEAT_TAC;;

let evaluate_IMP_shift_seq = cake_theorem "evaluate_IMP_shift_seq"
  (fun () ->
    `!es env s0 res s.
       closSem_evaluate (es,env,s0) = (res,s) ==>
         (?k. closSem_state_compile_oracle s = misc_shift_seq k
           (closSem_state_compile_oracle s0))`)
  CHEAT_TAC;;

let shift_seq_zero = cake_theorem "shift_seq_zero[simp]"
  (fun () ->
    `!co. misc_shift_seq 0 co = co`)
  CHEAT_TAC;;

let shift_seq_add = cake_theorem "shift_seq_add[simp]"
  (fun () ->
    `!co k1 k2. misc_shift_seq k2 (misc_shift_seq k1 co) =
  misc_shift_seq (k1 + k2) co`)
  CHEAT_TAC;;

let do_install_IMP_shift_seq = cake_theorem "do_install_IMP_shift_seq"
  (fun () ->
    `closSem_do_install xs s0 = (res,s) ==>
       (?k. closSem_state_compile_oracle s = misc_shift_seq k
         (closSem_state_compile_oracle s0))`)
  CHEAT_TAC;;

let evaluate_app_IMP_shift_seq =
  cake_theorem "evaluate_app_IMP_shift_seq"
  (fun () ->
    `evaluate_app lopt f args s0 = (res,s) ==>
       (?k. closSem_state_compile_oracle s = misc_shift_seq k
         (closSem_state_compile_oracle s0))`)
  CHEAT_TAC;;

let state_globals_approx_def = cake_define
  `state_globals_approx s g <=>
     (!k v a.
       get_global k (closSem_state_globals s) = SOME (SOME v) /\
         sptree_lookup k g = SOME a ==> val_approx_val a v)`;;

let state_globals_approx_clock_fupd =
  cake_theorem "state_globals_approx_clock_fupd[simp]"
  (fun () ->
    `state_globals_approx (state_clock_fupd f s) g <=>
     state_globals_approx s g`)
  CHEAT_TAC;;

let state_globals_approx_dec_clock =
  cake_theorem "state_globals_approx_dec_clock[simp]"
  (fun () ->
    `state_globals_approx (closSem_dec_clock n s) g <=>
  state_globals_approx s g`)
  CHEAT_TAC;;

let state_globals_approx_refsfupd =
  cake_theorem "state_globals_approx_refsfupd[simp]"
  (fun () ->
    `state_globals_approx (state_refs_fupd f s) g <=>
     state_globals_approx s g`)
  CHEAT_TAC;;

let state_globals_approx_ffifupd =
  cake_theorem "state_globals_approx_ffifupd[simp]"
  (fun () ->
    `state_globals_approx (state_ffi_fupd f s) g <=>
     state_globals_approx s g`)
  CHEAT_TAC;;

let state_globals_approx_codeupd =
  cake_theorem "state_globals_approx_codeupd[simp]"
  (fun () ->
    `state_globals_approx (closSem_state_code_fupd f s) g <=>
     state_globals_approx s g`)
  CHEAT_TAC;;

let state_globals_approx_coupd =
  cake_theorem "state_globals_approx_coupd[simp]"
  (fun () ->
    `state_globals_approx (closSem_state_compile_oracle_fupd f s) g <=>
     state_globals_approx s g`)
  CHEAT_TAC;;

(* Mapped globals *)

let mapped_globals_def = cake_define
  `mapped_globals g =
     {i | ?v. get_global i g = SOME (SOME v)}`;;

(* Extending mapped globals *)

let mglobals_extend_def = cake_define
  `mglobals_extend g1 mgs g2 <=>
      mapped_globals g2 SUBSET mapped_globals g1 UNION mgs /\
      (!k v. get_global k g2 = SOME (SOME v) /\ ~(k IN mgs) ==>
            get_global k g1 = SOME (SOME v))`;;

let mglobals_extend_refl = cake_theorem "mglobals_extend_refl[simp]"
  (fun () ->
    `mglobals_extend s gs s`)
  CHEAT_TAC;;

let mglobals_extend_trans = cake_theorem "mglobals_extend_trans"
  (fun () ->
    `!s0 s1 s2 g1 g2. mglobals_extend s0 g1 s1 /\ mglobals_extend s1 g2
  s2 ==>
     mglobals_extend s0 (g1 UNION g2) s2`)
  CHEAT_TAC;;

let mglobals_extend_SUBSET = cake_theorem "mglobals_extend_SUBSET"
  (fun () ->
    `!s0 s g1 g2. mglobals_extend s0 g1 s /\ g1 SUBSET g2 ==>
  mglobals_extend s0 g2 s`)
  CHEAT_TAC;;

let subspt_better_definedg = cake_theorem "subspt_better_definedg"
  (fun () ->
    `!sp1 sp2 sp3. subspt sp1 sp3 /\ better_definedg sp1 sp2 /\
  better_definedg sp2 sp3 ==>
     subspt sp1 sp2`)
  CHEAT_TAC;;

let subspt_known_elist_globals =
  cake_theorem "subspt_known_elist_globals"
  (fun () ->
    `!c es1 as1 g0 al1 g1 es2 as2 al2 g2.
       known c es1 as1 g0 = (al1,g1) /\ known c es2 as2 g1 =
         (al2,g2) /\
       subspt g0 g2 /\ BAG_DISJOINT (closProps_elist_globals es1)
         (closProps_elist_globals es2) ==>
       subspt g0 g1 /\ subspt g1 g2`)
  CHEAT_TAC;;

let subspt_known_op_elist_globals =
  cake_theorem "subspt_known_op_elist_globals"
  (fun () ->
    `!c es as1 g0 al1 g1 opn as2 g2 a.
        known c es as1 g0 = (al1,g1) /\ known_op opn as2 g1 =
          (a,g2) /\ subspt g0 g2 /\
        BAG_DISJOINT (closProps_op_gbag opn)
          (closProps_elist_globals es) ==>
        subspt g0 g1 /\ subspt g1 g2`)
  CHEAT_TAC;;

(* fv_max *)

let fv_max_def = cake_define
  `fv_max n xs = (!v. fv v xs ==> v < n)`;;

let fv_max_SmartOp = cake_theorem "fv_max_SmartOp"
  (fun () ->
    `fv_max n [closLang_Op t op xs] ==> fv_max n [clos_op_SmartOp t op
  xs]`)
  CHEAT_TAC;;

let fv_alt = cake_theorem "fv_alt"
  (fun () ->
    `!n xs. fv n xs <=> has_var n (SND (clos_known_free xs))`)
  CHEAT_TAC;;

let fv1_alt = cake_theorem "fv1_alt"
  (fun () ->
    `fv1 n x = has_var n (SND (clos_known_free [x]))`)
  CHEAT_TAC;;

let fv_max_rw = cake_theorem "fv_max_rw"
  (fun () ->
    `(fv_max n [] <=> T) /\
     (fv_max n (x :: y :: xs) <=> fv_max n [x] /\ fv_max n (y ::
       xs)) /\
     (fv_max n [Var tr v] <=> v < n) /\
     (fv_max n [If tr x1 x2 x3] <=> fv_max n [x1] /\ fv_max n [x2]
       /\ fv_max n [x3]) /\
     (fv_max n [Let tr xs x1] <=> fv_max n xs /\ fv_max (n + LENGTH
       xs) [x1]) /\
     (fv_max n [Raise tr x1] <=> fv_max n [x1]) /\
     (fv_max n [closLang_Tick tr x1] <=> fv_max n [x1]) /\
     (fv_max n [closLang_Op tr opn xs] <=> fv_max n xs) /\
     (fv_max n [App tr lopt x1 xs] <=> fv_max n [x1] /\ fv_max n
       xs) /\
     (fv_max n [closLang_Fn src_name loc vs num_args x1] <=> fv_max
       (n + num_args) [x1]) /\
     (fv_max n [Letrec src_names loc vs fns x1] <=>
        EVERY (\(num_args,x). fv_max (n + num_args + LENGTH fns)
          [x]) fns /\
        fv_max (n + LENGTH fns) [x1]) /\
     (fv_max n [Handle tr x1 x2] <=> fv_max n [x1] /\ fv_max (n +
       1) [x2]) /\
     (fv_max n [closLang_Call tr ticks dest xs] <=> fv_max n xs)`)
  CHEAT_TAC;;

let fv_max_mk_Ticks = cake_theorem "fv_max_mk_Ticks[simp]"
  (fun () ->
    `!t trc i e. fv_max n [mk_Ticks t trc i e] <=> fv_max n [e]`)
  CHEAT_TAC;;

let fv_max_cons = cake_theorem "fv_max_cons"
  (fun () ->
    `fv_max n (h :: t) <=> fv_max n [h] /\ fv_max n t`)
  CHEAT_TAC;;

let fv_max_append = cake_theorem "fv_max_append[simp]"
  (fun () ->
    `!xs ys n. fv_max n (xs ++ ys) <=> fv_max n xs /\ fv_max n ys`)
  CHEAT_TAC;;

let fv_max_less = cake_theorem "fv_max_less"
  (fun () ->
    `!m n xs. fv_max m xs /\ m <= n ==> fv_max n xs`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:612-615: a proof *)

let known_op_correct_approx = cake_theorem "known_op_correct_approx"
  (fun () ->
    `!opn args g0 a g vs s0 v s.
       known_op opn args g0 = (a,g) /\ do_app opn vs s0 = Rval
         (v,s) /\
       LIST_REL val_approx_val args vs /\ state_globals_approx s0
         g0 ==>
         state_globals_approx s g /\ val_approx_val a v`)
  CHEAT_TAC;;

let ssgc_free_co_shift_seq = cake_theorem "ssgc_free_co_shift_seq"
  (fun () ->
    `ssgc_free s ==> (!k. ssgc_free (closSem_state_compile_oracle_fupd
  (K (misc_shift_seq k (closSem_state_compile_oracle s))) s))`)
  CHEAT_TAC;;

let ssgc_free_do_install = cake_theorem "ssgc_free_do_install"
  (fun () ->
    `!s. ssgc_free s ==>
     ssgc_free (closSem_state_code_fupd (K (closSem_state_code s
       |++ SND (SND (closSem_state_compile_oracle s 0))))
       (closSem_state_compile_oracle_fupd (K (misc_shift_seq 1
       (closSem_state_compile_oracle s))) s))`)
  CHEAT_TAC;;

let do_install_ssgc = cake_theorem "do_install_ssgc"
  (fun () ->
    `!vs s0 es s1. closSem_do_install vs s0 = (Rval es,s1) /\ ssgc_free
  s0 ==>
     ssgc_free s1 /\ EVERY closProps_esgc_free es /\ ~(es = []) /\
       closSem_state_compile_oracle
     s1 = misc_shift_seq 1 (closSem_state_compile_oracle s0) /\
     first_n_exps (closSem_state_compile_oracle s0) 1 = [es] /\
     mglobals_extend (closSem_state_globals s0) EMPTY
       (closSem_state_globals s1)`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:705-709: ML code, not ported *)

let not_less_zero_imp = cake_theorem "not_less_zero_imp[local]"
  (fun () ->
    `~(i < ((&0):int)) ==> (?k. i = &k)`)
  CHEAT_TAC;;

let do_app_ssgc = cake_theorem "do_app_ssgc"
  (fun () ->
    `!opn args s0 res.
       do_app opn args s0 = res /\
       EVERY vsgc_free args /\ ssgc_free s0 ==>
       (!v s. res = Rval (v,s) ==>
              vsgc_free v /\ ssgc_free s /\
                closSem_state_compile_oracle
              s = closSem_state_compile_oracle s0 /\
              mglobals_extend (closSem_state_globals s0)
                (SET_OF_BAG (closProps_op_gbag opn))
                (closSem_state_globals s)) /\
       (!v. res = Rerr (Rraise v) ==> vsgc_free v)`)
  CHEAT_TAC;;

let dest_closure_Full_sgc_free =
  cake_theorem "dest_closure_Full_sgc_free"
  (fun () ->
    `dest_closure max_app loc_opt f (arg0 :: args) =
       SOME (Full_app fbody env rest_args) /\
     vsgc_free f /\ vsgc_free arg0 /\ EVERY vsgc_free args ==>
     closProps_set_globals fbody = EMPTY_BAG /\ EVERY vsgc_free
       env /\ EVERY vsgc_free rest_args`)
  CHEAT_TAC;;

let update_thunk_ssgc_free =
  cake_theorem "update_thunk_ssgc_free[local]"
  (fun () ->
    `ssgc_free s /\
     EVERY vsgc_free vs /\
     update_thunk [closSem_RefPtr v ptr] (state_refs s) vs = SOME
       refs ==>
       ssgc_free (state_refs_fupd (K refs) s)`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:883: ML code, not ported *)

(* Evaluate  *)
let evaluate_changed_globals_0 =
  cake_theorem "evaluate_changed_globals_0[local]"
  (fun () ->
    `(!es env (s0:('c,'ffi)closSem_state) res s.
         closSem_evaluate (es,env,s0) = (res,s) /\
         ssgc_free s0 /\ EVERY closProps_esgc_free es /\
         EVERY vsgc_free env ==>
           ssgc_free s /\ rsgc_free res /\
           (?n. closSem_state_compile_oracle
             s = misc_shift_seq n (closSem_state_compile_oracle s0)
               /\
             mglobals_extend (closSem_state_globals s0)
               (SET_OF_BAG (closProps_elist_globals es) UNION
                SET_OF_BAG (closProps_elist_globals (FLAT
                  (first_n_exps (closSem_state_compile_oracle s0) n))))
                  (closSem_state_globals s))) /\
      (!loc_opt f args (s0:('c,'ffi)closSem_state) res s.
         evaluate_app loc_opt f args s0 = (res,s) /\
         ssgc_free s0 /\ vsgc_free f /\ EVERY vsgc_free args ==>
           ssgc_free s /\ rsgc_free res /\
           (?n. closSem_state_compile_oracle
             s = misc_shift_seq n (closSem_state_compile_oracle s0)
               /\
             mglobals_extend (closSem_state_globals s0)
               (SET_OF_BAG (closProps_elist_globals (FLAT
                 (first_n_exps (closSem_state_compile_oracle s0) n))))
                 (closSem_state_globals s)))`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:1231-1232: a theorem that HOL4
   states as the value of an ML expression: evaluate_changed_globals *)

(* HOL4 clos_knownProofScript.sml:1234-1235: a theorem that HOL4
   states as the value of an ML expression:
   evaluate_app_changed_globals *)

let mk_Ticks_set_globals = cake_theorem "mk_Ticks_set_globals[simp]"
  (fun () ->
    `!t tc n exp. closProps_set_globals (mk_Ticks t tc n exp) =
  closProps_set_globals exp`)
  CHEAT_TAC;;

let gapprox_disjoint_def = cake_define
  `gapprox_disjoint g xs <=> DISJOINT (domain g) (SET_OF_BAG
  (closProps_elist_globals xs))`;;

let gapprox_disjoint_rw = cake_theorem "gapprox_disjoint_rw"
  (fun () ->
    `(gapprox_disjoint g (x :: y :: xs) <=>
        gapprox_disjoint g [x] /\ gapprox_disjoint g (y :: xs)) /\
     (gapprox_disjoint g [closLang_Op tr opn xs] <=>
        gapprox_disjoint g xs /\ DISJOINT (domain g) (SET_OF_BAG
          (closProps_op_gbag opn)))`)
  CHEAT_TAC;;

let oracle_gapprox_disjoint_def = cake_define
  `oracle_gapprox_disjoint g co <=> (!n. gapprox_disjoint g (FST (SND
  (co n))))`;;

let oracle_gapprox_disjoint_shift_seq =
  cake_theorem "oracle_gapprox_disjoint_shift_seq"
  (fun () ->
    `oracle_gapprox_disjoint g co ==>
     (!k. oracle_gapprox_disjoint g (misc_shift_seq k co))`)
  CHEAT_TAC;;

let oracle_gapprox_disjoint_evaluate =
  cake_theorem "oracle_gapprox_disjoint_evaluate"
  (fun () ->
    `!g s0 es env res s1.
       oracle_gapprox_disjoint g (closSem_state_compile_oracle s0)
         /\
       closSem_evaluate (es,env,s0) = (res,s1) ==>
       oracle_gapprox_disjoint g (closSem_state_compile_oracle
         s1)`)
  CHEAT_TAC;;

let oracle_gapprox_disjoint_first_n_exps =
  cake_theorem "oracle_gapprox_disjoint_first_n_exps"
  (fun () ->
    `!g co. oracle_gapprox_disjoint g co <=>
       (!n. gapprox_disjoint g (FLAT (first_n_exps co n)))`)
  CHEAT_TAC;;

let mk_Ticks_esgc_free = cake_theorem "mk_Ticks_esgc_free[simp]"
  (fun () ->
    `!t tc n exp. closProps_esgc_free (mk_Ticks t tc n exp) <=>
  closProps_esgc_free exp`)
  CHEAT_TAC;;

let known_op_preserves_esgc_free =
  cake_theorem "known_op_preserves_esgc_free"
  (fun () ->
    `!opn args g0 a g.
       known_op opn args g0 = (a,g) /\
       EVERY val_approx_sgc_free args /\
       globals_approx_sgc_free g0 ==>
       val_approx_sgc_free a /\ globals_approx_sgc_free g`)
  CHEAT_TAC;;

let elist_globals_empty = cake_theorem "elist_globals_empty"
  (fun () ->
    `!es. closProps_elist_globals es = EMPTY_BAG <=>
          (!e. MEM e es ==> closProps_set_globals e = EMPTY_BAG)`)
  CHEAT_TAC;;

let clos_gen_noinline_val_approx_sgc_free =
  cake_theorem "clos_gen_noinline_val_approx_sgc_free"
  (fun () ->
    `!n i fns. EVERY val_approx_sgc_free (clos_gen_noinline n i fns)`)
  CHEAT_TAC;;

let loptrel_def = cake_define
  `loptrel fv' numargs lopt1 lopt2 <=>
      lopt2 = lopt1 \/
      lopt1 = NONE /\
      (match (fv',lopt2) with (Closure (SOME loc1) ae _2 n bod,SOME
        loc2) ->
             loc1 = loc2 /\ n = numargs /\ ae = [] | (Recclosure
               (SOME loc1) ae _3 fns i,SOME loc2) ->
          i < LENGTH fns /\ loc2 = loc1 + 2 * i /\ numargs = FST (EL
            i fns) /\
          ae = [] | _4 -> F)`;;

let decide_inline_LetInline_IMP_Clos =
  cake_theorem "decide_inline_LetInline_IMP_Clos"
  (fun () ->
    `!c fapx lopt arity body.
       decide_inline c fapx lopt arity = inlD_LetInline body ==>
         (?m s. fapx = clos_known_Clos m arity body s)`)
  CHEAT_TAC;;

let decide_inline_LetInline_IMP_Clos_lopt =
  cake_theorem "decide_inline_LetInline_IMP_Clos_lopt"
  (fun () ->
    `!c fapx lopt arity body.
       decide_inline c fapx lopt arity = inlD_LetInline body ==>
         (?m s. fapx = clos_known_Clos m arity body s /\
               (lopt = NONE \/ lopt = SOME m))`)
  CHEAT_TAC;;

let known_preserves_esgc_free_0 =
  cake_theorem "known_preserves_esgc_free_0"
  (fun () ->
    `!c es aenv g0 eas1 g.
       known c es aenv g0 = (eas1,g) /\
       EVERY closProps_esgc_free es /\
       EVERY val_approx_sgc_free aenv /\
       globals_approx_sgc_free g0 ==>
       closProps_elist_globals (MAP FST eas1) <=
         closProps_elist_globals es /\
       EVERY closProps_esgc_free (MAP FST eas1) /\
       EVERY val_approx_sgc_free (MAP SND eas1) /\
       globals_approx_sgc_free g`)
  CHEAT_TAC;;

let known_preserves_esgc_free = cake_theorem "known_preserves_esgc_free"
  (fun () ->
    `!c es aenv g0 eas1 g.
       known c es aenv g0 = (eas1,g) /\
       EVERY closProps_esgc_free es /\
       EVERY val_approx_sgc_free aenv /\
       globals_approx_sgc_free g0 ==>
       EVERY closProps_esgc_free (MAP FST eas1) /\
       EVERY val_approx_sgc_free (MAP SND eas1) /\
       globals_approx_sgc_free g`)
  CHEAT_TAC;;

let known_elglobals_dont_grow = cake_theorem "known_elglobals_dont_grow"
  (fun () ->
    `!c es aenv g0 eas1 g.
       known c es aenv g0 = (eas1,g) /\
       EVERY closProps_esgc_free es /\
       EVERY val_approx_sgc_free aenv /\
       globals_approx_sgc_free g0 ==>
       closProps_elist_globals (MAP FST eas1) <=
         closProps_elist_globals es`)
  CHEAT_TAC;;

let known_preserves_pure = cake_theorem "known_preserves_pure"
  (fun () ->
    `!c es aenv g0 eas1 g.
       known c es aenv g0 = (eas1,g) /\
       EVERY pure es ==>
       EVERY pure (MAP FST eas1)`)
  CHEAT_TAC;;

let evaluate_mk_Ticks_rw = cake_theorem "evaluate_mk_Ticks_rw"
  (fun () ->
    `!t tc n exp env (s:('c,'ffi)closSem_state).
       closSem_evaluate ([mk_Ticks t tc n exp],env,s) =
       (if closSem_state_clock s < n then (Rerr (Rabort
         Rtimeout_error),closSem_state_clock_fupd (K 0) s) else
         closSem_evaluate ([exp],env,closSem_dec_clock n s))`)
  CHEAT_TAC;;

let evaluate_mk_Ticks_IMP = cake_theorem "evaluate_mk_Ticks_IMP"
  (fun () ->
    `!t tc n exp env (s0:('c,'ffi)closSem_state) res s.
       closSem_evaluate ([mk_Ticks t tc n exp],env,s0) = (res,s)
         ==>
       (res = Rerr (Rabort Rtimeout_error) /\ s =
         closSem_state_clock_fupd (K 0) s0) \/
       (closSem_evaluate ([exp],env,closSem_dec_clock n s0) =
         (res,s))`)
  CHEAT_TAC;;

let clos_gen_noinline_eq = cake_theorem "clos_gen_noinline_eq"
  (fun () ->
    `!n c fns.
     clos_gen_noinline n c fns =
     GENLIST (\i. clos_known_ClosNoInline (2 * (i + c) + n) (FST
       (EL i fns))) (LENGTH fns)`)
  CHEAT_TAC;;

let letrec_case_eq = cake_theorem "letrec_case_eq[local]"
  (fun () ->
    `!limit' loc fns.
     (match loc with
       NONE -> REPLICATE (LENGTH fns) clos_known_Other | SOME n ->
         clos_gen_noinline n 0 fns) =
     GENLIST (match loc with NONE -> K clos_known_Other |
                          SOME n -> (\i. clos_known_ClosNoInline
                            (n + 2 * i) (FST (EL i fns)))) (LENGTH
                            fns)`)
  CHEAT_TAC;;

let every_var_def = cake_define_list
  [`clos_knownProof_every_var P (db_vars_Empty:db_var_set) = T`;
   `clos_knownProof_every_var P (Var v:db_var_set) <=> P v`;
   `clos_knownProof_every_var P (Shift k d:db_var_set) <=>
  clos_knownProof_every_var (\v. k <= v ==> P (v - k)) d`;
   `clos_knownProof_every_var P (Union d1 d2:db_var_set) <=>
  clos_knownProof_every_var P d1 /\ clos_knownProof_every_var P d2`];;
hol4_overload "every_var" "clos_knownProof_every_var";;

let every_var_mk_Union = cake_theorem "every_var_mk_Union[simp]"
  (fun () ->
    `clos_knownProof_every_var P (mk_Union d1 d2) <=>
  clos_knownProof_every_var P d1 /\ clos_knownProof_every_var P d2`)
  CHEAT_TAC;;


let decide_inline_LetInline_IMP_Clos_fv_max =
  cake_theorem "decide_inline_LetInline_IMP_Clos_fv_max"
  (fun () ->
    `!c fapx lopt arity body.
       decide_inline c fapx lopt arity = inlD_LetInline body ==>
         (?m s. fapx = clos_known_Clos m arity body s /\
               fv_max arity [body])`)
  CHEAT_TAC;;

let known_preserves_fv_max = cake_theorem "known_preserves_fv_max"
  (fun () ->
    `!c es aenv g0 eas1 g n.
       known c es aenv g0 = (eas1,g) /\
       fv_max n es ==>
       fv_max n (MAP FST eas1)`)
  CHEAT_TAC;;

(* oracle_gapprox_subspt *)
let oracle_gapprox_subspt_def = cake_define
  `oracle_gapprox_subspt co <=>
     (!n. subspt (FST (FST (co n))) (FST (FST (co (SUC n)))))`;;

let oracle_gapprox_subspt_add = cake_theorem "oracle_gapprox_subspt_add"
  (fun () ->
    `oracle_gapprox_subspt co <=>
       (!(n:num) k. subspt (FST (FST (co n))) (FST (FST (co (n +
         k)))))`)
  CHEAT_TAC;;

let oracle_gapprox_subspt_alt = cake_theorem "oracle_gapprox_subspt_alt"
  (fun () ->
    `!co n k. oracle_gapprox_subspt co /\ n <= k ==>
       subspt (FST (FST (co n))) (FST (FST (co k)))`)
  CHEAT_TAC;;

let oracle_gapprox_subspt_shift_seq =
  cake_theorem "oracle_gapprox_subspt_shift_seq"
  (fun () ->
    `oracle_gapprox_subspt co ==> (!k. oracle_gapprox_subspt
  (misc_shift_seq k co))`)
  CHEAT_TAC;;

let oracle_gapprox_subspt_evaluate =
  cake_theorem "oracle_gapprox_subspt_evaluate"
  (fun () ->
    `!s0 xs env s0 res s.
       oracle_gapprox_subspt (closSem_state_compile_oracle s0) /\
       closSem_evaluate (xs,env,s0) = (res,s) ==>
       oracle_gapprox_subspt (closSem_state_compile_oracle s)`)
  CHEAT_TAC;;

(* oracle_state_sgc_free *)
let oracle_state_sgc_free_def = cake_define
  `oracle_state_sgc_free co = (!n. globals_approx_sgc_free (FST (FST
  (co n))))`;;

let oracle_state_sgc_free_shift_seq =
  cake_theorem "oracle_state_sgc_free_shift_seq"
  (fun () ->
    `!co. oracle_state_sgc_free co ==> (!n. oracle_state_sgc_free
  (misc_shift_seq n co))`)
  CHEAT_TAC;;

let next_g_def = cake_define
  `next_g (s:(val_approx spt#'c,'ffi)closSem_state) =
     FST (FST (closSem_state_compile_oracle s 0))`;;

(**)

let mglobals_disjoint_def = cake_define
  `mglobals_disjoint s xs <=> DISJOINT (mapped_globals s) (SET_OF_BAG
  (closProps_elist_globals xs))`;;

let mglobals_disjoint_rw = cake_theorem "mglobals_disjoint_rw"
  (fun () ->
    `(mglobals_disjoint s (x :: y :: xs) <=>
        mglobals_disjoint s [x] /\ mglobals_disjoint s (y :: xs))
          /\
     (mglobals_disjoint s [Let tr xs x] <=>
        mglobals_disjoint s xs /\ mglobals_disjoint s [x]) /\
     (mglobals_disjoint s [Handle tr x1 x2] <=>
        mglobals_disjoint s [x1] /\ mglobals_disjoint s [x2]) /\
     (mglobals_disjoint s [If tr x1 x2 x3] <=>
        mglobals_disjoint s [x1] /\ mglobals_disjoint s [x2] /\
          mglobals_disjoint s [x3]) /\
     (mglobals_disjoint s [Raise tr x] <=>
        mglobals_disjoint s [x]) /\
     (mglobals_disjoint s [closLang_Tick tr x] <=>
        mglobals_disjoint s [x]) /\
     (mglobals_disjoint s [closLang_Call tr ticks dest xs] <=>
        mglobals_disjoint s xs) /\
     (mglobals_disjoint s [closLang_Op tr opn xs] <=>
        mglobals_disjoint s xs /\ DISJOINT (mapped_globals s)
          (SET_OF_BAG (closProps_op_gbag opn))) /\
     (mglobals_disjoint s [App tr lopt x1 xs] <=>
        mglobals_disjoint s [x1] /\ mglobals_disjoint s xs) /\
     (mglobals_disjoint s [Letrec src_names lopt vs fns x1] <=>
        mglobals_disjoint s (MAP SND fns) /\ mglobals_disjoint s
          [x1])`)
  CHEAT_TAC;;

(**)

let known_changed_globals_cases =
  cake_theorem "known_changed_globals_cases"
  (fun () ->
    `!c xs aenv g0 alist g.
       known c xs aenv g0 = (alist,g) ==>
       (!k a. sptree_lookup k g = SOME a ==> sptree_lookup k g0 =
         SOME a \/ k IN SET_OF_BAG (closProps_elist_globals xs))`)
  CHEAT_TAC;;

let known_op_changed_globals_cases =
  cake_theorem "known_op_changed_globals_cases"
  (fun () ->
    `!opn aenv g0 ea g.
       known_op opn aenv g0 = (ea,g) ==>
       (!k a. sptree_lookup k g = SOME a ==> sptree_lookup k g0 =
         SOME a \/ k IN SET_OF_BAG (closProps_op_gbag opn))`)
  CHEAT_TAC;;


let state_globals_approx_known_mglobals_disjoint =
  cake_theorem "state_globals_approx_known_mglobals_disjoint"
  (fun () ->
    `!c xs aenv g0 eas g s.
     known c xs aenv g0 = (eas,g) /\
     mglobals_disjoint (closSem_state_globals s) xs /\
     state_globals_approx s g0 ==>
     state_globals_approx s g`)
  CHEAT_TAC;;

let mglobals_disjoint_evaluate =
  cake_theorem "mglobals_disjoint_evaluate"
  (fun () ->
    `!s0 xs ys env res s.
     closSem_evaluate (ys,env,s0) = (res,s) /\
     ssgc_free s0 /\ EVERY vsgc_free env /\ EVERY
       closProps_esgc_free ys /\
     unique_set_globals (xs ++ ys) (closSem_state_compile_oracle
       s0) /\
     mglobals_disjoint (closSem_state_globals s0) xs ==>
     mglobals_disjoint (closSem_state_globals s) xs`)
  CHEAT_TAC;;


let gapprox_extend_def = cake_define
  `gapprox_extend g1 gd g2 <=>
     (!i. i IN domain g2 /\ (i IN domain g1 ==> ~(sptree_lookup i g2
       = sptree_lookup i g1)) ==>
         i IN gd)`;;

let state_globals_approx_disjoint_extends =
  cake_theorem "state_globals_approx_disjoint_extends"
  (fun () ->
    `!s1 mgx s2 g1 gax g2.
       mglobals_extend (closSem_state_globals s1) mgx
         (closSem_state_globals s2) /\ gapprox_extend g1 gax g2 /\
       DISJOINT (mapped_globals (closSem_state_globals s1)) gax /\
         DISJOINT gax mgx /\
       state_globals_approx s2 g1 ==>
       state_globals_approx s2 g2`)
  CHEAT_TAC;;

let state_globals_approx_evaluate =
  cake_theorem "state_globals_approx_evaluate"
  (fun () ->
    `!xs env s0 res s c ys aenv g0 eas g.
     closSem_evaluate (xs,env,s0) = (res,s) /\
     known c ys aenv g0 = (eas,g) /\
     ssgc_free s0 /\ EVERY vsgc_free env /\ EVERY
       closProps_esgc_free xs /\
     mglobals_disjoint (closSem_state_globals s0) ys /\
     unique_set_globals (xs ++ ys) (closSem_state_compile_oracle
       s0) /\
     state_globals_approx s g0 ==>
     state_globals_approx s g`)
  CHEAT_TAC;;

let state_globals_approx_known_op_evaluate =
  cake_theorem "state_globals_approx_known_op_evaluate"
  (fun () ->
    `closSem_evaluate (xs,env,s0) = (res,s) /\
     known_op opn aargs g0 = (ea,g) /\
     ssgc_free s0 /\ EVERY vsgc_free env /\ EVERY
       closProps_esgc_free xs /\
     DISJOINT (mapped_globals (closSem_state_globals s0))
       (SET_OF_BAG (closProps_op_gbag opn)) /\
     unique_set_globals [closLang_Op tr opn xs]
       (closSem_state_compile_oracle s0) /\
     state_globals_approx s g0 ==>
     state_globals_approx s g`)
  CHEAT_TAC;;

let elist_globals_first_n_exps_lemma =
  cake_theorem "elist_globals_first_n_exps_lemma"
  (fun () ->
    `!i k co. BAG_IN i (closProps_elist_globals (FST (SND (co k)))) ==>
           (!n. k < n ==> BAG_IN i (closProps_elist_globals (FLAT
             (first_n_exps co n))))`)
  CHEAT_TAC;;

let elist_globals_first_n_exps_shift_seq_lemma =
  cake_theorem "elist_globals_first_n_exps_shift_seq_lemma"
  (fun () ->
    `!i k co. BAG_IN i (closProps_elist_globals (FST (SND (co k)))) ==>
           (!m n. m < k /\ k < m + n ==> BAG_IN i
             (closProps_elist_globals (FLAT (first_n_exps
             (misc_shift_seq m co) n))))`)
  CHEAT_TAC;;

let elist_globals_first_n_exps_exists =
  cake_theorem "elist_globals_first_n_exps_exists"
  (fun () ->
    `!i co n. BAG_IN i (closProps_elist_globals (FLAT (first_n_exps co
  n))) ==>
       (?k. k < n /\ BAG_IN i (closProps_elist_globals (FST (SND
         (co k)))))`)
  CHEAT_TAC;;

let oracle_gapprox_disjoint_Install =
  cake_theorem "oracle_gapprox_disjoint_Install"
  (fun () ->
    `!c co g0 eas g.
       known c (FST (SND (co 0))) [] g0 = (eas,g) /\
       unique_set_globals [] co /\
       oracle_gapprox_disjoint g0 co ==>
       oracle_gapprox_disjoint g (misc_shift_seq 1 co)`)
  CHEAT_TAC;;

let oracle_gapprox_disjoint_shift_seq_unique_set_globals =
  cake_theorem "oracle_gapprox_disjoint_shift_seq_unique_set_globals"
  (fun () ->
    `!c xs aenv g0 eas g s0 k.
       known c xs aenv g0 = (eas,g) /\
       unique_set_globals xs (closSem_state_compile_oracle s0) /\
       oracle_gapprox_disjoint g0 (closSem_state_compile_oracle s0)
         ==>
       oracle_gapprox_disjoint g (misc_shift_seq k
         (closSem_state_compile_oracle s0))`)
  CHEAT_TAC;;

(* essentially a duplicate of the above  *)
let oracle_gapprox_disjoint_lemma =
  cake_theorem "oracle_gapprox_disjoint_lemma"
  (fun () ->
    `!xs env s0 res s c aenv g0 eas g.
       closSem_evaluate (xs,env,s0) = (res,s) /\
       known c xs aenv g0 = (eas,g) /\
       unique_set_globals xs (closSem_state_compile_oracle s0) /\
       oracle_gapprox_disjoint g0 (closSem_state_compile_oracle s0)
         ==>
       oracle_gapprox_disjoint g (closSem_state_compile_oracle s)`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:1893: ML code, not ported *)

let known_correct_approx = cake_theorem "known_correct_approx"
  (fun () ->
    `!c xs aenv g0 eas g env extra (s0:(val_approx
  spt#'c,'ffi)closSem_state) res s.
     known c xs aenv g0 = (eas,g) /\
     closSem_evaluate (xs,env ++ extra,s0) = (res,s) /\
     // fv_max (LENGTH env) xs /\
     unique_set_globals xs (closSem_state_compile_oracle s0) /\
     LIST_REL val_approx_val aenv env /\
     state_globals_approx s0 g0 /\
     mglobals_disjoint (closSem_state_globals s0) xs /\
     oracle_gapprox_disjoint g0 (closSem_state_compile_oracle s0)
       /\
     ssgc_free s0 /\ EVERY vsgc_free (env ++ extra) /\ EVERY
       closProps_esgc_free xs /\
     EVERY val_approx_sgc_free aenv /\ globals_approx_sgc_free g0
       ==>
       state_globals_approx s g /\
       (!vs. res = Rval vs ==> LIST_REL val_approx_val (MAP SND
         eas) vs)`)
  CHEAT_TAC;;

let monotonic_gapprox_disjoint =
  cake_theorem "monotonic_gapprox_disjoint"
  (fun () ->
    `known c xs aenv LN = (ys,g) ==>
     oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o
       SND)
         (<) (SET_OF_BAG b) co ==>
     b = closProps_elist_globals xs ==>
     oracle_gapprox_disjoint g co`)
  CHEAT_TAC;;

let elist_globals_FLAT_APPEND_FOLDR =
  cake_theorem "elist_globals_FLAT_APPEND_FOLDR"
  (fun () ->
    `closProps_elist_globals (xs ++ FLAT ys) = ITLIST (BAG_UNION) (MAP
  closProps_elist_globals (xs :: ys)) EMPTY_BAG`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:2503-2504: a theorem that HOL4
   states as the value of an ML expression: elist_globals_FLAT_FOLDR *)

let monotonic_unique_set_globals =
  cake_theorem "monotonic_unique_set_globals"
  (fun () ->
    `oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o SND)
  (<)
         (SET_OF_BAG (closProps_elist_globals xs)) co ==>
     BAG_ALL_DISTINCT (closProps_elist_globals xs) /\
     (!n. BAG_ALL_DISTINCT (closProps_elist_globals (FST (SND (co
       n))))) ==>
     unique_set_globals xs co`)
  CHEAT_TAC;;

let pure_co_oracle_props = cake_theorem "pure_co_oracle_props"
  (fun () ->
    `oracle_gapprox_subspt (pure_co f o co) = oracle_gapprox_subspt co
  /\
     oracle_state_sgc_free (pure_co f o co) =
       oracle_state_sgc_free co`)
  CHEAT_TAC;;

let state_oracle_domain = cake_theorem "state_oracle_domain"
  (fun () ->
    `is_state_oracle (compile_inc c) co ==>
     BAG_OF_SET (domain (FST (FST (co n)))) <= (BAG_UNION)
       (BAG_OF_SET (domain (FST (FST (co 0)))))
       (closProps_elist_globals (FLAT (first_n_exps co n)))`)
  CHEAT_TAC;;

(* code relation *)

let exp_rel_def = cake_define
  `clos_knownProof_exp_rel c aenv g' e1 e2 <=>
     (?g0 g apx k.
       subspt g g' /\
       EVERY val_approx_sgc_free aenv /\
       globals_approx_sgc_free g0 /\
       known (clos_known_config_inline_factor_fupd (K k) c) [e1]
         aenv g0 = ([(e2,apx)],g))`;;
hol4_overload "exp_rel" "clos_knownProof_exp_rel";;

let exp_rel_dec_inline_factor =
  cake_theorem "exp_rel_dec_inline_factor[simp]"
  (fun () ->
    `clos_knownProof_exp_rel (dec_inline_factor c) aenv g e1 e2 <=>
  clos_knownProof_exp_rel c aenv g e1 e2`)
  CHEAT_TAC;;

(* value relation *)

let f_rel_def = cake_define
  `clos_knownProof_f_rel c aenv g (n1,e1) (n2,e2) <=>
      n1 = n2 /\ clos_knownProof_exp_rel c (REPLICATE n1
        clos_known_Other ++ aenv) g e1 e2`;;
hol4_overload "f_rel" "clos_knownProof_f_rel";;

(* HOL4 clos_knownProofScript.sml:2578-2582: a theorem whose
   statement the port cannot state yet: v1_size_append *)

let _ = size_thms "closSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_knownProofScript.sml:2614-2617: the tactic that proves
   the termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let v_rel_def = cake_define_list_try_tac (fun () ->
  `MEASURE (closSem_v_size o FST o SND o SND)`)
  CHEAT_TAC
  [`clos_knownProof_v_rel c g (closSem_Number i:closSem_v) v <=> v =
  (closSem_Number i:closSem_v)`;
   `clos_knownProof_v_rel c g (Word64 w:closSem_v) v <=> v = (Word64
  w:closSem_v)`;
   `clos_knownProof_v_rel c g (closSem_ByteVector ws) v <=> v =
  closSem_ByteVector ws`;
   `clos_knownProof_v_rel c g (closSem_RefPtr b n:closSem_v) v <=> v
  = (closSem_RefPtr b n:closSem_v)`;
   `clos_knownProof_v_rel c g (closSem_Block n xs:closSem_v) v <=>
         (?ys. v = closSem_Block n ys /\ LIST_REL
           (clos_knownProof_v_rel c g) xs ys)`;
   `clos_knownProof_v_rel c g (Closure loc_opt args1 env1 num_args
  e1:closSem_v) v <=>
         every_Fn_vs_NONE [e1] /\
         (?aenv env1a env1b args2 env2a env2b e2.
           if env1 = env1a ++ env1b then
           fv_max (num_args + LENGTH env1a) [e1] /\
           LIST_REL (clos_knownProof_v_rel c g) args1 args2 /\
           LIST_REL (clos_knownProof_v_rel c g) env1a env2a /\
           LIST_REL val_approx_val aenv env1a /\
           clos_knownProof_exp_rel c (REPLICATE num_args
             clos_known_Other ++ aenv) g e1 e2 /\
           v = Closure loc_opt args2 (env2a ++ env2b) num_args e2
             else F)`;
   `clos_knownProof_v_rel c g (Recclosure loc_opt args1 env1 funs1
  i:closSem_v) v <=>
         EVERY (\(n,e). every_Fn_vs_NONE [e]) funs1 /\
         (let clos = (match loc_opt with NONE -> REPLICATE (LENGTH
           funs1) clos_known_Other | SOME loc -> clos_gen_noinline loc 0
           funs1) in ?aenv env1a env1b args2 env2a env2b funs2.
           if env1 = env1a ++ env1b then
           EVERY (\(num_args,exp). fv_max (num_args + LENGTH funs1 +
             LENGTH env1a) [exp]) funs1 /\
           LIST_REL (clos_knownProof_v_rel c g) args1 args2 /\
           LIST_REL (clos_knownProof_v_rel c g) env1a env2a /\
           LIST_REL val_approx_val aenv env1a /\
           LIST_REL (f_rel c (clos ++ aenv) g) funs1 funs2 /\
           v = Recclosure loc_opt args2 (env2a ++ env2b) funs2
             i else F)`];;
hol4_overload "v_rel" "clos_knownProof_v_rel";;

(* HOL4 clos_knownProofScript.sml:2619-2620: a theorem that HOL4
   states as the value of an ML expression: v_rel_def *)

(* HOL4 clos_knownProofScript.sml:2622: ML code, not ported *)

let v_rel_app_def = cake_define_list
  [`v_rel_app c g (closSem_Number i:closSem_v) v args1 <=> v_rel c g
  ((closSem_Number i:closSem_v)) v`;
   `v_rel_app c g (Word64 w:closSem_v) v args1 <=> v_rel c g ((Word64
  w:closSem_v)) v`;
   `v_rel_app c g (closSem_ByteVector ws) v args1 <=> v_rel c g
  (closSem_ByteVector ws) v`;
   `v_rel_app c g (closSem_RefPtr b n:closSem_v) v args1 <=> v_rel c
  g ((closSem_RefPtr b n:closSem_v)) v`;
   `v_rel_app c g (closSem_Block n xs:closSem_v) v args1 <=> v_rel c
  g ((closSem_Block n xs:closSem_v)) v`;
   `v_rel_app c g (Closure loc_opt pargs1 env1 num_args e1:closSem_v) v
  args1 <=>
         every_Fn_vs_NONE [e1] /\
         (?aenv env1a env1b pargs2 env2a env2b e2 aargs.
           env1 = env1a ++ env1b /\
           fv_max (num_args + LENGTH env1a) [e1] /\
           LIST_REL (v_rel c g) pargs1 pargs2 /\
           LIST_REL (v_rel c g) env1a env2a /\
           LIST_REL val_approx_val aenv env1a /\
           (match args1 with NONE -> aargs = REPLICATE num_args
             clos_known_Other | SOME args1' -> LIST_REL val_approx_val
             aargs args1' /\
                              pargs1 = []) /\
           clos_knownProof_exp_rel c (aargs ++ aenv) g e1 e2 /\
           v = Closure loc_opt pargs2 (env2a ++ env2b) num_args
             e2)`;
   `v_rel_app c g (Recclosure loc_opt pargs1 env1 funs1 i:closSem_v) v
  args1 <=>
         v_rel c g ((Recclosure loc_opt pargs1 env1 funs1
           i:closSem_v)) v`];;

let v_rel_app_NONE = cake_theorem "v_rel_app_NONE"
  (fun () ->
    `v_rel_app c g v1 v2 NONE = v_rel c g v1 v2`)
  CHEAT_TAC;;

let exp_rel_upd_inline_factor = cake_theorem "exp_rel_upd_inline_factor"
  (fun () ->
    `clos_knownProof_exp_rel (clos_known_config_inline_factor_fupd (K
  k) c) = clos_knownProof_exp_rel c`)
  CHEAT_TAC;;

let f_rel_upd_inline_factor = cake_theorem "f_rel_upd_inline_factor"
  (fun () ->
    `f_rel (clos_known_config_inline_factor_fupd (K k) c) = f_rel c`)
  CHEAT_TAC;;

let v_rel_upd_inline_factor = cake_theorem "v_rel_upd_inline_factor"
  (fun () ->
    `!c. v_rel (clos_known_config_inline_factor_fupd (K k) c) = v_rel
  c`)
  CHEAT_TAC;;

let v_rel_Block = cake_theorem "v_rel_Block[simp]"
  (fun () ->
    `v_rel c g x (closSem_Block n ys:closSem_v) <=>
       (?xs. x = closSem_Block n xs /\ LIST_REL (v_rel c g) xs
         ys)`)
  CHEAT_TAC;;

let clos_knownProof_v_rel_Boolv = cake_theorem "v_rel_Boolv[simp]"
  (fun () ->
    `(v_rel c g (Boolv b) v <=> v = Boolv b) /\
     (v_rel c g v (Boolv b) <=> v = Boolv b)`)
  CHEAT_TAC;;

let clos_knownProof_v_rel_Unit = cake_theorem "v_rel_Unit[simp]"
  (fun () ->
    `(v_rel c g closSem_Unit v <=> v = closSem_Unit) /\ (v_rel c g v
  closSem_Unit <=> v = closSem_Unit)`)
  CHEAT_TAC;;

let clos_knownProof_v_rel_IMP_v_to_bytes_lemma =
  cake_theorem "v_rel_IMP_v_to_bytes_lemma[local]"
  (fun () ->
    `!x y c g.
       v_rel c g x y ==>
       (!ns. (v_to_list x = SOME (MAP (closSem_Number o (&) o
         (w2n:word8->num)) ns)) <=>
            (v_to_list y = SOME (MAP (closSem_Number o (&) o
              (w2n:word8->num)) ns)))`)
  CHEAT_TAC;;

let clos_knownProof_v_rel_IMP_v_to_bytes =
  cake_theorem "v_rel_IMP_v_to_bytes[local]"
  (fun () ->
    `v_rel c g x y ==> closSem_v_to_bytes y = closSem_v_to_bytes x`)
  CHEAT_TAC;;

let clos_knownProof_v_rel_IMP_v_to_words_lemma =
  cake_theorem "v_rel_IMP_v_to_words_lemma[local]"
  (fun () ->
    `!x y c g.
       v_rel c g x y ==>
       (!ns. (v_to_list x = SOME (MAP Word64 ns)) <=>
            (v_to_list y = SOME (MAP Word64 ns)))`)
  CHEAT_TAC;;

let clos_knownProof_v_rel_IMP_v_to_words =
  cake_theorem "v_rel_IMP_v_to_words[local]"
  (fun () ->
    `v_rel c g x y ==> closSem_v_to_words y = closSem_v_to_words x`)
  CHEAT_TAC;;

(* state relation *)

let ref_rel = cake_inductive
  `(!bs. clos_knownProof_ref_rel c g (closSem_ByteArray bs)
  (closSem_ByteArray bs)) /\
   (!xs ys.
     LIST_REL (v_rel c g) xs ys ==>
     clos_knownProof_ref_rel c g (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     v_rel c g v w ==>
       clos_knownProof_ref_rel c g (Thunk m v) (Thunk m w))`;;
hol4_overload "ref_rel" "clos_knownProof_ref_rel";;

(* HOL4 clos_knownProofScript.sml:2762-2766: a theorem that HOL4
   states as the value of an ML expression: ref_rel_simps *)

let ref_rel_upd_inline_factor = cake_theorem "ref_rel_upd_inline_factor"
  (fun () ->
    `ref_rel (clos_known_config_inline_factor_fupd (K k) c) = ref_rel
  c`)
  CHEAT_TAC;;

let state_rel_def = cake_define
  `clos_knownProof_state_rel c g (s:(val_approx
  spt#'c,'ffi)closSem_state) (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
     (!n. fv_max 0 (FST (SND (closSem_state_compile_oracle s n)))) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_clock
     s = closSem_state_clock t /\ closSem_state_ffi s =
       closSem_state_ffi t /\ closSem_state_max_app s =
       closSem_state_max_app t /\
     LIST_REL (OPTREL (v_rel c g)) (closSem_state_globals s)
       (closSem_state_globals t) /\
     fmap_rel (ref_rel c g) (closSem_state_refs s)
       (closSem_state_refs t) /\ closSem_state_compile
     s = state_cc (compile_inc c) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = state_co (compile_inc c) (closSem_state_compile_oracle s)`;;
hol4_overload "state_rel" "clos_knownProof_state_rel";;

let compile_inc_upd_inline_factor =
  cake_theorem "compile_inc_upd_inline_factor[local]"
  (fun () ->
    `compile_inc (clos_known_config_inline_factor_fupd (K k) c) =
  compile_inc c`)
  CHEAT_TAC;;

let state_rel_upd_inline_factor =
  cake_theorem "state_rel_upd_inline_factor"
  (fun () ->
    `state_rel (clos_known_config_inline_factor_fupd (K k) c) =
  state_rel c`)
  CHEAT_TAC;;

let v_rel_subspt = cake_theorem "v_rel_subspt"
  (fun () ->
    `!c g v1 v2 g'. v_rel c g v1 v2 /\ subspt g g' ==> v_rel c g' v1
  v2`)
  CHEAT_TAC;;

let v_rel_LIST_REL_subspt = cake_theorem "v_rel_LIST_REL_subspt"
  (fun () ->
    `!vs1 vs2. LIST_REL (v_rel c g) vs1 vs2 ==>
               (!g'. subspt g g' ==> LIST_REL (v_rel c g') vs1
                 vs2)`)
  CHEAT_TAC;;

let ref_rel_subspt = cake_theorem "ref_rel_subspt"
  (fun () ->
    `!c g r1 r2 g'. ref_rel c g r1 r2 /\ subspt g g' ==> ref_rel c g'
  r1 r2`)
  CHEAT_TAC;;

let state_rel_subspt = cake_theorem "state_rel_subspt"
  (fun () ->
    `!c g s1 s2 g'. state_rel c g s1 s2 /\ subspt g g' ==> state_rel c
  g' s1 s2`)
  CHEAT_TAC;;

let co_every_Fn_vs_NONE_def = cake_define
  `co_every_Fn_vs_NONE co =
     (!n exps aux. SND (co n) = (exps,aux) ==>
       every_Fn_vs_NONE exps /\
       every_Fn_vs_NONE (MAP (SND o SND) aux))`;;

let co_every_Fn_vs_NONE_shift_seq =
  cake_theorem "co_every_Fn_vs_NONE_shift_seq"
  (fun () ->
    `!co. co_every_Fn_vs_NONE co ==> (!n. co_every_Fn_vs_NONE
  (misc_shift_seq n co))`)
  CHEAT_TAC;;

let state_rel_co_elist_globals =
  cake_theorem "state_rel_co_elist_globals"
  (fun () ->
    `state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free
  (closSem_state_compile_oracle s) ==>
       closProps_elist_globals (FST (SND
         (closSem_state_compile_oracle t n))) <=
         closProps_elist_globals (FST (SND
         (closSem_state_compile_oracle s n)))`)
  CHEAT_TAC;;

let state_rel_first_n_exps = cake_theorem "state_rel_first_n_exps"
  (fun () ->
    `state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free
  (closSem_state_compile_oracle s) ==>
       closProps_elist_globals (FLAT (first_n_exps
         (closSem_state_compile_oracle t) n)) <=
         closProps_elist_globals (FLAT (first_n_exps
         (closSem_state_compile_oracle s) n))`)
  CHEAT_TAC;;

let state_rel_unique_set_globals =
  cake_theorem "state_rel_unique_set_globals"
  (fun () ->
    `!xs. state_rel c g s t /\ ssgc_free s /\ oracle_state_sgc_free
  (closSem_state_compile_oracle s) /\
     unique_set_globals xs (closSem_state_compile_oracle s) ==>
       unique_set_globals xs (closSem_state_compile_oracle t)`)
  CHEAT_TAC;;

let state_rel_get_global_IMP = cake_theorem "state_rel_get_global_IMP"
  (fun () ->
    `!c g s t n v1. state_rel c g s t /\ get_global n
  (closSem_state_globals s) = SOME (SOME v1) ==>
     (?v2. get_global n (closSem_state_globals t) = SOME (SOME
       v2) /\ v_rel c g v1 v2)`)
  CHEAT_TAC;;

let clos_knownProof_do_app_lemma = cake_theorem "do_app_lemma[local]"
  (fun () ->
    `!c g s t xs ys opp. state_rel c g s t /\ LIST_REL (v_rel c g) xs ys
  ==>
       (match do_app opp xs s with Rerr err1 -> (?err2. do_app opp
         ys t = Rerr err2 /\
                              exc_rel (v_rel c g) err1 err2) | Rval
                                (x,s1) -> (?y t1. v_rel c g x y /\
                                state_rel c g s1 t1 /\
                              do_app opp ys t = Rval (y,t1)))`)
  CHEAT_TAC;;

let evaluate_app_exact_rw = cake_theorem "evaluate_app_exact_rw"
  (fun () ->
    `~(args = []) /\ num_args = LENGTH args ==>
     evaluate_app (SOME loc) (Closure (SOME loc) [] env num_args
       body) args s =
     (if state_clock s < LENGTH args then
       (Rerr (Rabort Rtimeout_error),state_clock_fupd (K 0) s) else
       closSem_evaluate ([body],args ++ env,closSem_dec_clock
         num_args s))`)
  CHEAT_TAC;;

(* HOL4 clos_knownProofScript.sml:2960-2970: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_knownProofScript.sml:2972-2974: a theorem that HOL4
   states as the value of an ML expression: loptrel_arg1_SOME *)

(* HOL4 clos_knownProofScript.sml:2976-2978: a theorem that HOL4
   states as the value of an ML expression: loptrel_arg1_NONE *)

let clos_knownProof_dest_closure_SOME_IMP =
  cake_theorem "dest_closure_SOME_IMP"
  (fun () ->
    `dest_closure max_app loc_opt f2 xs = SOME x ==>
      (?loc arg_env clo_env num_args e. f2 = Closure loc arg_env
        clo_env num_args e) \/
      (?loc arg_env clo_env fns i. f2 = Recclosure loc arg_env
        clo_env fns i)`)
  CHEAT_TAC;;

let state_globals_approx_subspt =
  cake_theorem "state_globals_approx_subspt"
  (fun () ->
    `!g0 g s. subspt g0 g /\ state_globals_approx s g ==>
     state_globals_approx s g0`)
  CHEAT_TAC;;

let oracle_gapprox_disjoint_subspt =
  cake_theorem "oracle_gapprox_disjoint_subspt"
  (fun () ->
    `!g0 g co. subspt g0 g /\ oracle_gapprox_disjoint g co ==>
     oracle_gapprox_disjoint g0 co`)
  CHEAT_TAC;;

let decide_inline_inlD_LetInline_sgc_free =
  cake_theorem "decide_inline_inlD_LetInline_sgc_free"
  (fun () ->
    `!c a lopt n body. decide_inline c a lopt n = inlD_LetInline body
  /\ val_approx_sgc_free a ==> closProps_set_globals body = EMPTY_BAG`)
  CHEAT_TAC;;

let known_op_subspt = cake_theorem "known_op_subspt"
  (fun () ->
    `!opn aargs g0 a g.
       known_op opn aargs g0 = (a,g) /\
       BAG_DISJOINT (BAG_OF_SET (domain g0)) (closProps_op_gbag
         opn) ==>
       BAG_OF_SET (domain g) <= (BAG_UNION) (BAG_OF_SET (domain
         g0)) (closProps_op_gbag opn) /\
       subspt g0 g`)
  CHEAT_TAC;;

let known_subspt = cake_theorem "known_subspt"
  (fun () ->
    `!c xs aenv g0 eas g.
       known c xs aenv g0 = (eas,g) /\
       EVERY closProps_esgc_free xs /\ EVERY val_approx_sgc_free
         aenv /\ globals_approx_sgc_free g0 /\
       BAG_ALL_DISTINCT ((BAG_UNION) (BAG_OF_SET (domain g0))
         (closProps_elist_globals xs)) ==>
       BAG_OF_SET (domain g) <= (BAG_UNION) (BAG_OF_SET (domain
         g0)) (closProps_elist_globals xs) /\
       subspt g0 g`)
  CHEAT_TAC;;


(* Set globals in all future installs is disjoint from currently mapped globals. *)
let state_oracle_mglobals_disjoint_def = cake_define
  `state_oracle_mglobals_disjoint s <=> (!n. mglobals_disjoint
  (closSem_state_globals s) (FST (SND (closSem_state_compile_oracle s
  n))))`;;

let state_oracle_mglobals_disjoint_evaluate_suff =
  cake_theorem "state_oracle_mglobals_disjoint_evaluate_suff"
  (fun () ->
    `!xs env s0 res s. closSem_evaluate (xs,env,s0) = (res,s) /\
     ssgc_free s0 /\ EVERY closProps_esgc_free xs /\ EVERY
       vsgc_free env /\
     unique_set_globals xs (closSem_state_compile_oracle s0) /\
     mglobals_disjoint (closSem_state_globals s0) xs /\
     state_oracle_mglobals_disjoint s0 ==>
     state_oracle_mglobals_disjoint s`)
  CHEAT_TAC;;

let clos_knownProof_state_rel_opt_rel_refs =
  cake_theorem "state_rel_opt_rel_refs[local]"
  (fun () ->
    `(state_rel c g s1 s2 /\ FLOOKUP (state_refs s1) n = r1 ==>
        (?r2. FLOOKUP (state_refs s2) n = r2 /\ OPTREL (ref_rel c
          g) r1 r2)) /\
     (state_rel c g s1 s2 /\ FLOOKUP (state_refs s2) n = r2 ==>
        (?r1. FLOOKUP (state_refs s1) n = r1 /\ OPTREL (ref_rel c
          g) r1 r2))`)
  CHEAT_TAC;;

let clos_knownProof_rel_update_thunk =
  cake_theorem "rel_update_thunk[local]"
  (fun () ->
    `state_rel c g s1 s2 /\
     LIST_REL (v_rel c g) vs ys ==>
       (update_thunk [closSem_RefPtr v ptr] (state_refs s1) vs =
         SOME refs1 ==>
          (?refs2. update_thunk [closSem_RefPtr v ptr] (state_refs
            s2) ys = SOME refs2 /\
                  state_rel c g (state_refs_fupd (K refs1) s1)
                    (state_refs_fupd (K refs2) s2)))`)
  CHEAT_TAC;;


(* HOL4 clos_knownProofScript.sml:3185: ML code, not ported *)

let known_correct0 = cake_theorem "known_correct0[local]"
  (fun () ->
    `(!xs env1full (s0:(val_approx spt#'c,'ffi)closSem_state) res1 s
  env1 xenv1
       env2 xenv2 t0 c g0 g aenv eas.
        closSem_evaluate (xs,env1full,s0) = (res1,s) /\
        known c xs aenv g0 = (eas,g) /\
        state_rel c (next_g s0) s0 t0 /\
        every_Fn_vs_NONE xs /\
        co_every_Fn_vs_NONE (closSem_state_compile_oracle s0) /\
        mglobals_disjoint (closSem_state_globals s0) xs /\
        oracle_gapprox_disjoint (next_g s0)
          (closSem_state_compile_oracle s0) /\
        state_oracle_mglobals_disjoint s0 /\
        EVERY closProps_esgc_free xs /\ ssgc_free s0 /\
        EVERY vsgc_free env1full /\
        LIST_REL val_approx_val aenv env1 /\
        oracle_state_sgc_free (closSem_state_compile_oracle s0) /\
        globals_approx_sgc_free g0 /\
        EVERY val_approx_sgc_free aenv /\
        state_globals_approx s0 (next_g s0) /\
        subspt g0 g /\ subspt g (next_g s0) /\
        oracle_gapprox_subspt (closSem_state_compile_oracle s0) /\
        fv_max (LENGTH env1) xs /\
        LIST_REL (v_rel c (next_g s0)) env1 env2 /\
        unique_set_globals xs (closSem_state_compile_oracle s0) /\
        is_state_oracle (compile_inc c)
          (closSem_state_compile_oracle s0) /\
        env1full = env1 ++ xenv1 /\ ~(res1 = Rerr (Rabort
          Rtype_error)) ==>
        (?res2 t.
          closSem_evaluate (MAP FST eas,env2 ++ xenv2,t0) =
            (res2,t) /\
          semanticPrimitivesProps_result_rel (LIST_REL (v_rel c
            (next_g s))) (v_rel c (next_g s)) res1 res2 /\
          state_rel c (next_g s) s t /\
          state_globals_approx s (next_g s) /\
          is_state_oracle (compile_inc c)
            (closSem_state_compile_oracle s) /\
          oracle_gapprox_disjoint (next_g s)
            (closSem_state_compile_oracle s))) /\
     (!lopt1 f1 args1 (s0:(val_approx spt#'c,'ffi)closSem_state)
       res1 s lopt2 f2 args2 t0 c argsopt.
        evaluate_app lopt1 f1 args1 s0 = (res1,s) /\
        v_rel_app c (next_g s0) f1 f2 argsopt /\
        oracle_gapprox_disjoint (next_g s0)
          (closSem_state_compile_oracle s0) /\
        state_oracle_mglobals_disjoint s0 /\
        ssgc_free s0 /\ vsgc_free f1 /\ EVERY vsgc_free args1 /\
        oracle_state_sgc_free (closSem_state_compile_oracle s0) /\
        co_every_Fn_vs_NONE (closSem_state_compile_oracle s0) /\
        unique_set_globals [] (closSem_state_compile_oracle s0) /\
        is_state_oracle (compile_inc c)
          (closSem_state_compile_oracle s0) /\
        LIST_REL (v_rel c (next_g s0)) args1 args2 /\
        state_rel c (next_g s0) s0 t0 /\
        state_globals_approx s0 (next_g s0) /\
        oracle_gapprox_subspt (closSem_state_compile_oracle s0) /\
        loptrel f2 (LENGTH args1) lopt1 lopt2 /\
        (IS_SOME argsopt ==> argsopt = SOME args1 /\ ~(args1 = [])
          /\ (?exp env. dest_closure (closSem_state_max_app s0) lopt1 f1
          args1 = SOME (Full_app exp env []))) /\ ~(res1 = Rerr (Rabort
          Rtype_error)) ==>
        (?res2 t.
          evaluate_app lopt2 f2 args2 t0 = (res2,t) /\
          semanticPrimitivesProps_result_rel (LIST_REL (v_rel c
            (next_g s))) (v_rel c (next_g s)) res1 res2 /\
          state_rel c (next_g s) s t /\
          state_globals_approx s (next_g s) /\
          is_state_oracle (compile_inc c)
            (closSem_state_compile_oracle s) /\
          oracle_gapprox_disjoint (next_g s)
            (closSem_state_compile_oracle s)))`)
  CHEAT_TAC;;

let semantics_known = cake_theorem "semantics_known"
  (fun () ->
    `~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY co
          (state_cc (compile_inc c) cc) xs = ffi_Fail) ==>
        (!n. SND (SND (co n)) = []) /\
        (!n. fv_max 0 (FST (SND (co n)))) /\
        (!n exps aux. SND (co n) = (exps,aux) ==> EVERY
          closProps_esgc_free exps) /\
        every_Fn_vs_NONE xs /\
        co_every_Fn_vs_NONE co /\
        oracle_gapprox_subspt co /\
        oracle_state_sgc_free co /\
        is_state_oracle (compile_inc c) co /\
        unique_set_globals xs co /\
        EVERY closProps_esgc_free xs /\
        fv_max 0 xs /\
        FST (FST (co 0)) = g /\
        oracle_gapprox_disjoint g co /\
        known c xs [] LN = (eas,g) ==>
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          (state_co (compile_inc c) co) cc (MAP FST eas) =
        closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY
          co (state_cc (compile_inc c) cc) xs`)
  CHEAT_TAC;;

let code_locs_mk_Ticks = cake_theorem "code_locs_mk_Ticks[simp]"
  (fun () ->
    `!a b c d. code_locs [mk_Ticks a b c d] = code_locs [d]`)
  CHEAT_TAC;;

let contains_closures_code_locs =
  cake_theorem "contains_closures_code_locs"
  (fun () ->
    `!es. ~(contains_closures es) ==> code_locs es = []`)
  CHEAT_TAC;;

let code_locs_decide_inline = cake_theorem "code_locs_decide_inline"
  (fun () ->
    `decide_inline a b c d = inlD_LetInline e ==> code_locs [e] = []`)
  CHEAT_TAC;;

let known_code_locs_bag = cake_theorem "known_code_locs_bag"
  (fun () ->
    `!c xs aenv g0 eas g.
       known c xs aenv g0 = (eas,g) ==>
       LIST_TO_BAG (code_locs (MAP FST eas)) <= LIST_TO_BAG
         (code_locs xs)`)
  CHEAT_TAC;;

let compile_code_locs_bag = cake_theorem "compile_code_locs_bag"
  (fun () ->
    `clos_known_compile kc es = (kc',es') ==>
       LIST_TO_BAG (code_locs es') <= LIST_TO_BAG (code_locs es)`)
  CHEAT_TAC;;

let clos_knownProof_compile_LENGTH = cake_theorem "compile_LENGTH"
  (fun () ->
    `clos_known_compile kc es = (kc',es') ==> LENGTH es' = LENGTH es`)
  CHEAT_TAC;;

let syntax_ok_def = cake_define
  `clos_knownProof_syntax_ok xs <=>
     every_Fn_vs_NONE xs /\
     BAG_ALL_DISTINCT (closProps_elist_globals xs) /\
     EVERY closProps_esgc_free xs`;;
hol4_overload "syntax_ok" "clos_knownProof_syntax_ok";;

(* HOL4 clos_knownProofScript.sml:5010: the overload fvs_compile,
   which the port expands *)

(* HOL4 clos_knownProofScript.sml:5012: the ML values that the
   definitions below antiquote *)

let syntax_oracle_ok_def = cake_define
  `clos_knownProof_syntax_oracle_ok c xs co conf <=>
     clos_knownProof_syntax_ok xs /\
     is_state_oracle (compile_inc c) (pure_co
       (clos_fvs_compile_inc:closLang_exp list#(num#num#closLang_exp)
       list->closLang_exp list#(num#num#closLang_exp) list) o co) /\
     conf = FST (FST (co 0)) /\
     oracle_monotonic (SET_OF_BAG o closProps_elist_globals o FST o
       SND) (<)
       (SET_OF_BAG (closProps_elist_globals xs)) co /\
     (!n. clos_knownProof_syntax_ok (FST (SND (co n))) /\ SND (SND
       (co n)) = [])`;;
hol4_overload "syntax_oracle_ok" "clos_knownProof_syntax_oracle_ok";;

let known_cc_def = cake_define
  `known_cc known_conf cc =
     (match known_conf with SOME kcfg ->
        (pure_cc clos_fvs_compile_inc
          (state_cc (compile_inc kcfg)
            (pure_cc clos_ticks_compile_inc
              (pure_cc clos_letop_compile_inc
                (cc:'b->closLang_exp list#(num#num#closLang_exp)
                  list->(word8 list#word64 list#'b)
                  option):'b->closLang_exp
                  list#(num#num#closLang_exp) list->(word8
                  list#word64 list#'b) option):'b->closLang_exp
                  list#(num#num#closLang_exp) list->(word8
                  list#word64 list#'b) option))) | NONE -> (state_cc
                  (CURRY I) cc:val_approx spt#'b->closLang_exp
                  list#(num#num#closLang_exp) list->(word8
                  list#word64 list#val_approx spt#'b) option))`;;

let known_co_def = cake_define
  `known_co known_conf (co:num->(val_approx spt#'b)#closLang_exp
  list#(num#num#closLang_exp) list) =
     (match known_conf with SOME kcfg -> (pure_co
       clos_letop_compile_inc o
                        ((pure_co clos_ticks_compile_inc o
                           (state_co (compile_inc kcfg)
                             (pure_co clos_fvs_compile_inc o
                               co):num->'b#closLang_exp
                               list#(num#num#closLang_exp)
                               list)):num->'b#closLang_exp
                               list#(num#num#closLang_exp) list)) |
                               NONE -> ((state_co (CURRY I)
                               co):num->'b#closLang_exp
                               list#(num#num#closLang_exp) list))`;;

let known_co_eq_pure_state = cake_theorem "known_co_eq_pure_state"
  (fun () ->
    `known_co known_conf co =
       pure_co (if IS_SOME known_conf then
               clos_letop_compile_inc o
                 (clos_ticks_compile_inc:closLang_exp
                 list#(num#num#closLang_exp) list->closLang_exp
                 list#(num#num#closLang_exp) list) else I) o
       state_co (match known_conf with SOME kcfg -> compile_inc
         kcfg | NONE -> CURRY I)
       (pure_co (if IS_SOME known_conf then clos_fvs_compile_inc
         else I) o co)`)
  CHEAT_TAC;;

let known_mk_co_def = cake_define
  `known_mk_co kc kc' mk =
     add_state_co (if IS_SOME kc then clos_known_compile_inc (THE kc)
       else CURRY I)
     (option_val_approx_spt kc')
     (mk o pure_co_progs (if IS_SOME kc then
           clos_letop_compile_inc o
             (clos_ticks_compile_inc:closLang_exp
             list#(num#num#closLang_exp) list->closLang_exp
             list#(num#num#closLang_exp) list) else I)) o
             pure_co_progs (if IS_SOME kc then clos_fvs_compile_inc
             else I)`;;

let known_co_progs_def = cake_define
  `known_co_progs kc kc' =
     pure_co_progs (if IS_SOME kc then
           clos_letop_compile_inc o
             (clos_ticks_compile_inc:closLang_exp
             list#(num#num#closLang_exp) list->closLang_exp
             list#(num#num#closLang_exp) list) else I) o
     state_co_progs (if IS_SOME kc then clos_known_compile_inc
       (THE kc) else CURRY I) (match kc' with NONE -> LN | SOME kcfg
       -> clos_known_config_val_approx_spt kcfg) o pure_co_progs (if
       IS_SOME kc then clos_fvs_compile_inc else I)`;;

let known_co_known_mk_co = cake_theorem "known_co_known_mk_co"
  (fun () ->
    `known_co kc (syntax_to_full_oracle (known_mk_co kc kc' mk) co) =
     syntax_to_full_oracle mk (known_co_progs kc kc' co)`)
  CHEAT_TAC;;

let fvs_compile_uncurry = cake_theorem "fvs_compile_uncurry"
  (fun () ->
    `clos_fvs_compile_inc p = (remove_fvs 0 (FST p),[])`)
  CHEAT_TAC;;

let syntax_oracle_ok_state_sgc_free =
  cake_theorem "syntax_oracle_ok_state_sgc_free"
  (fun () ->
    `clos_knownProof_syntax_oracle_ok c xs co g ==>
     known c (clos_fvs_compile xs) [] LN = (ys,g) ==>
     oracle_state_sgc_free co`)
  CHEAT_TAC;;

let syntax_oracle_ok_gapprox_subspt =
  cake_theorem "syntax_oracle_ok_gapprox_subspt"
  (fun () ->
    `clos_knownProof_syntax_oracle_ok c xs co g ==>
     known c (clos_fvs_compile xs) [] LN = (ys,g) ==>
     oracle_gapprox_subspt co`)
  CHEAT_TAC;;

let clos_knownProof_semantics_compile = cake_theorem "semantics_compile"
  (fun () ->
    `~(closSem_semantics ffi max_app FEMPTY co cc1 xs = ffi_Fail) /\
     (cc1 = known_cc known_conf cc) /\
     (co1 = known_co known_conf co) /\
     (compile known_conf xs = (known_conf',es)) /\
     (IS_SOME known_conf ==>
        clos_knownProof_syntax_oracle_ok (THE known_conf) xs co
          (clos_known_config_val_approx_spt (THE known_conf')) /\
        1 <= max_app) ==>
     closSem_semantics ffi max_app FEMPTY co1 cc es =
     closSem_semantics ffi max_app FEMPTY co cc1 xs`)
  CHEAT_TAC;;

let every_Fn_SOME_mk_Ticks = cake_theorem "every_Fn_SOME_mk_Ticks"
  (fun () ->
    `!t tc n e. every_Fn_SOME [e] ==> every_Fn_SOME [mk_Ticks t tc n
  e]`)
  CHEAT_TAC;;

let every_Fn_vs_NONE_mk_Ticks = cake_theorem "every_Fn_vs_NONE_mk_Ticks"
  (fun () ->
    `!t tc n e. every_Fn_vs_NONE [e] ==> every_Fn_vs_NONE [mk_Ticks t
  tc n e]`)
  CHEAT_TAC;;

let _ = size_thms "val_approx";;
(* HOL4 clos_knownProofScript.sml:5264-5268: the tactic that proves
   the termination *)
let val_approx_every_Fn_SOME_def = cake_define_wf
  `MEASURE val_approx_size`
  `val_approx_every_Fn_SOME x1 =
        match x1 with
          (clos_known_Tuple _6 vs:val_approx) -> EVERY
            val_approx_every_Fn_SOME vs
        | (clos_known_Clos _7 _8 b _9) -> every_Fn_SOME [b]
        | _10 -> T`;;

let val_approx_every_Fn_SOME_merge =
  cake_theorem "val_approx_every_Fn_SOME_merge"
  (fun () ->
    `!a b. val_approx_every_Fn_SOME a /\ val_approx_every_Fn_SOME b ==>
       val_approx_every_Fn_SOME (merge a b)`)
  CHEAT_TAC;;

let decide_inline_every_Fn_SOME =
  cake_theorem "decide_inline_every_Fn_SOME"
  (fun () ->
    `val_approx_every_Fn_SOME b /\ decide_inline a b c d =
  inlD_LetInline e ==>
     every_Fn_SOME [e]`)
  CHEAT_TAC;;

let globals_approx_every_Fn_SOME_def = cake_define
  `globals_approx_every_Fn_SOME g =
     (!c d. sptree_lookup c g = SOME d ==>
       val_approx_every_Fn_SOME d)`;;

let known_op_every_Fn_SOME = cake_theorem "known_op_every_Fn_SOME"
  (fun () ->
    `known_op op x y = (a,b) /\
     EVERY val_approx_every_Fn_SOME x /\
     globals_approx_every_Fn_SOME y ==> val_approx_every_Fn_SOME a
       /\
        globals_approx_every_Fn_SOME b`)
  CHEAT_TAC;;

let clos_gen_no_inline_every_Fn_SOME =
  cake_theorem "clos_gen_no_inline_every_Fn_SOME"
  (fun () ->
    `!(xs:(num#closLang_exp) list) n x.
     EVERY val_approx_every_Fn_SOME (clos_gen_noinline x n xs)`)
  CHEAT_TAC;;

let known_every_Fn_SOME = cake_theorem "known_every_Fn_SOME"
  (fun () ->
    `!a b c d.
      every_Fn_SOME b /\ EVERY val_approx_every_Fn_SOME c /\
      globals_approx_every_Fn_SOME d ==>
      every_Fn_SOME (MAP FST (FST (known a b c d))) /\
      EVERY val_approx_every_Fn_SOME (MAP SND (FST (known a b c
        d))) /\
      globals_approx_every_Fn_SOME (SND (known a b c d))`)
  CHEAT_TAC;;

let _ = size_thms "val_approx";;
(* HOL4 clos_knownProofScript.sml:5383-5387: the tactic that proves
   the termination *)
let val_approx_every_Fn_vs_NONE_def = cake_define_wf
  `MEASURE val_approx_size`
  `val_approx_every_Fn_vs_NONE x1 =
        match x1 with
          (clos_known_Tuple _12 vs:val_approx) -> EVERY
            val_approx_every_Fn_vs_NONE vs
        | (clos_known_Clos _13 _14 b _15) -> every_Fn_vs_NONE [b]
        | _16 -> T`;;

let val_approx_every_Fn_vs_NONE_merge =
  cake_theorem "val_approx_every_Fn_vs_NONE_merge"
  (fun () ->
    `!a b. val_approx_every_Fn_vs_NONE a /\ val_approx_every_Fn_vs_NONE
  b ==>
       val_approx_every_Fn_vs_NONE (merge a b)`)
  CHEAT_TAC;;

let decide_inline_every_Fn_vs_NONE =
  cake_theorem "decide_inline_every_Fn_vs_NONE"
  (fun () ->
    `val_approx_every_Fn_vs_NONE b /\ decide_inline a b c d =
  inlD_LetInline e ==>
     every_Fn_vs_NONE [e]`)
  CHEAT_TAC;;

let globals_approx_every_Fn_vs_NONE_def = cake_define
  `globals_approx_every_Fn_vs_NONE g =
     (!c d. sptree_lookup c g = SOME d ==>
       val_approx_every_Fn_vs_NONE d)`;;

let known_op_every_Fn_vs_NONE = cake_theorem "known_op_every_Fn_vs_NONE"
  (fun () ->
    `known_op op x y = (a,b) /\
     EVERY val_approx_every_Fn_vs_NONE x /\
     globals_approx_every_Fn_vs_NONE y ==>
       val_approx_every_Fn_vs_NONE a /\
       globals_approx_every_Fn_vs_NONE b`)
  CHEAT_TAC;;

let clos_gen_no_inline_every_Fn_vs_NONE =
  cake_theorem "clos_gen_no_inline_every_Fn_vs_NONE"
  (fun () ->
    `!(xs:(num#closLang_exp) list) n x.
     EVERY val_approx_every_Fn_vs_NONE (clos_gen_noinline x n xs)`)
  CHEAT_TAC;;

let known_every_Fn_vs_NONE = cake_theorem "known_every_Fn_vs_NONE"
  (fun () ->
    `!a b c d.
      every_Fn_vs_NONE b /\ EVERY val_approx_every_Fn_vs_NONE c /\
      globals_approx_every_Fn_vs_NONE d ==>
      every_Fn_vs_NONE (MAP FST (FST (known a b c d))) /\
      EVERY val_approx_every_Fn_vs_NONE (MAP SND (FST (known a b c
        d))) /\
      globals_approx_every_Fn_vs_NONE (SND (known a b c d))`)
  CHEAT_TAC;;

(* no_Labels *)

let _ = size_thms "val_approx";;
let val_approx_no_Labels_def = cake_define_wf
  `MEASURE val_approx_size`
  `val_approx_no_Labels x1 =
        match x1 with
          clos_known_ClosNoInline m n -> T
        | (clos_known_Clos m n e s) -> no_Labels e
        | (clos_known_Tuple tag vas) -> EVERY val_approx_no_Labels
          vas
        | _17 -> T`;;
(* HOL4 clos_knownProofScript.sml:5516-5522: ML code, not ported *)

(* HOL4 clos_knownProofScript.sml:5524-5527: a theorem that HOL4
   states as the value of an ML expression: val_approx_no_Labels_simp *)

let decide_inline_no_Labels = cake_theorem "decide_inline_no_Labels"
  (fun () ->
    `val_approx_no_Labels b /\ decide_inline a b c d = inlD_LetInline e
  ==>
     no_Labels e`)
  CHEAT_TAC;;

let globals_approx_no_Labels_def = cake_define
  `globals_approx_no_Labels g =
     (!c d. sptree_lookup c g = SOME d ==> val_approx_no_Labels d)`;;

let val_approx_no_Labels_merge =
  cake_theorem "val_approx_no_Labels_merge"
  (fun () ->
    `!a b. val_approx_no_Labels a /\ val_approx_no_Labels b ==>
           val_approx_no_Labels (merge a b)`)
  CHEAT_TAC;;

let known_op_no_Labels = cake_theorem "known_op_no_Labels"
  (fun () ->
    `known_op op x y = (a,b) /\
     EVERY val_approx_no_Labels x /\
     globals_approx_no_Labels y ==> val_approx_no_Labels a /\
        globals_approx_no_Labels b`)
  CHEAT_TAC;;

let no_Labels_mk_Ticks = cake_theorem "no_Labels_mk_Ticks"
  (fun () ->
    `!t tc n e. no_Labels e ==> no_Labels (mk_Ticks t tc n e)`)
  CHEAT_TAC;;

let clos_gen_no_inline_no_Labels =
  cake_theorem "clos_gen_no_inline_no_Labels"
  (fun () ->
    `!(xs:(num#closLang_exp) list) n x.
     EVERY val_approx_no_Labels (clos_gen_noinline x n xs)`)
  CHEAT_TAC;;

let known_no_Labels = cake_theorem "known_no_Labels"
  (fun () ->
    `!a b c d.
      EVERY no_Labels b /\ EVERY val_approx_no_Labels c /\
      globals_approx_no_Labels d ==>
      EVERY no_Labels (MAP FST (FST (known a b c d))) /\
      EVERY val_approx_no_Labels (MAP SND (FST (known a b c d))) /\
      globals_approx_no_Labels (SND (known a b c d))`)
  CHEAT_TAC;;

let compile_no_Labels = cake_theorem "compile_no_Labels"
  (fun () ->
    `compile (SOME c) xs = (res,ys) /\ EVERY no_Labels xs ==>
      (?c1. res = SOME c1 /\ EVERY no_Labels ys /\
           globals_approx_no_Labels
             (clos_known_config_val_approx_spt c1))`)
  CHEAT_TAC;;

(* obeys_max_app *)

let _ = size_thms "val_approx";;
let val_approx_obeys_max_app_def = cake_define_wf
  `MEASURE (val_approx_size o SND)`
  `val_approx_obeys_max_app k x2 =
        match x2 with
          clos_known_ClosNoInline m n -> T
        | (clos_known_Clos m n e s) -> obeys_max_app k e
        | (clos_known_Tuple tag vas) -> EVERY
          (val_approx_obeys_max_app k) vas
        | _18 -> T`;;

let decide_inline_obeys_max_app =
  cake_theorem "decide_inline_obeys_max_app"
  (fun () ->
    `val_approx_obeys_max_app k b /\ decide_inline a b c d =
  inlD_LetInline e ==>
     obeys_max_app k e`)
  CHEAT_TAC;;

let globals_approx_obeys_max_app_def = cake_define
  `globals_approx_obeys_max_app k g =
     (!c d. sptree_lookup c g = SOME d ==>
       val_approx_obeys_max_app k d)`;;

let val_approx_obeys_max_app_merge =
  cake_theorem "val_approx_obeys_max_app_merge"
  (fun () ->
    `!a b. val_approx_obeys_max_app k a /\ val_approx_obeys_max_app k b
  ==>
           val_approx_obeys_max_app k (merge a b)`)
  CHEAT_TAC;;

let known_op_obeys_max_app = cake_theorem "known_op_obeys_max_app"
  (fun () ->
    `known_op op x y = (a,b) /\
     EVERY (val_approx_obeys_max_app k) x /\
     globals_approx_obeys_max_app k y ==> val_approx_obeys_max_app
       k a /\
       globals_approx_obeys_max_app k b`)
  CHEAT_TAC;;

let obeys_max_app_mk_Ticks = cake_theorem "obeys_max_app_mk_Ticks"
  (fun () ->
    `!t tc n e. obeys_max_app k e ==> obeys_max_app k (mk_Ticks t tc n
  e)`)
  CHEAT_TAC;;

let clos_gen_no_inline_obeys_max_app =
  cake_theorem "clos_gen_no_inline_obeys_max_app"
  (fun () ->
    `!(xs:(num#closLang_exp) list) n x.
     EVERY (val_approx_obeys_max_app k) (clos_gen_noinline x n
       xs)`)
  CHEAT_TAC;;

let known_IMP_LENGTH = cake_theorem "known_IMP_LENGTH"
  (fun () ->
    `known c xs vs g = (ys,g') ==> LENGTH ys = LENGTH xs`)
  CHEAT_TAC;;

let known_obeys_max_app = cake_theorem "known_obeys_max_app"
  (fun () ->
    `!a b c d.
      EVERY (obeys_max_app k) b /\ EVERY (val_approx_obeys_max_app
        k) c /\
      globals_approx_obeys_max_app k d ==>
      EVERY (obeys_max_app k) (MAP FST (FST (known a b c d))) /\
      EVERY (val_approx_obeys_max_app k) (MAP SND (FST (known a b c
        d))) /\
      globals_approx_obeys_max_app k (SND (known a b c d))`)
  CHEAT_TAC;;

let compile_obeys_max_app = cake_theorem "compile_obeys_max_app"
  (fun () ->
    `compile (SOME c) xs = (res,ys) /\ EVERY (obeys_max_app k) xs ==>
      (?c1. res = SOME c1 /\ EVERY (obeys_max_app k) ys /\
           globals_approx_obeys_max_app k
             (clos_known_config_val_approx_spt c1))`)
  CHEAT_TAC;;

let known_compile_IS_SOME = cake_theorem "known_compile_IS_SOME"
  (fun () ->
    `compile kc es = (kc',es') ==> (IS_SOME kc' <=> IS_SOME kc)`)
  CHEAT_TAC;;

(* names *)

let get_code_labels_mk_Ticks =
  cake_theorem "get_code_labels_mk_Ticks[simp]"
  (fun () ->
    `!a b c d. closProps_get_code_labels (mk_Ticks a b c d) =
  closProps_get_code_labels d`)
  CHEAT_TAC;;
