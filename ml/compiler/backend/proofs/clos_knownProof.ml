(* ======================================================== *)
(*  clos_knownProof: ported from HOL4's
    compiler/backend/proofs/clos_knownProofScript.sml
    A proof theory about clos_known.ml, with 40 definitions and 188
    theorems.  Needed by clos_to_bvlProof.ml.  *)
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
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 clos_knownProofScript.sml:21-22: ML code, not ported *)

(* fixeqs flips any equations in the assumption that have evaluate on the rhs *)
(* HOL4 clos_knownProofScript.sml:25: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_knownProofScript.sml:27: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_knownProofScript.sml:29: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_knownProofScript.sml:31: the ML values that the
   definitions below antiquote *)

(* simple properties of constants from clos_known: i.e., merge and known *)

(* Take the first n expression lists returned by the compile oracle. *)
let first_n_exps_def = cake_define
  `first_n_exps co n = GENLIST (FST o SND o co) n`;;

(* All globals set in the program and in code returned by
   the compile oracle are unique. *)
let unique_set_globals_def = cake_define
  `unique_set_globals es co <=>
     (!n. BAG_ALL_DISTINCT (closProps_elist_globals (es ++ FLAT
       (first_n_exps co n))))`;;

(* HOL4 clos_knownProofScript.sml:224: ML code, not ported *)


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

let state_globals_approx_def = cake_define
  `state_globals_approx s g <=>
     (!k v a.
       get_global k (closSem_state_globals s) = SOME (SOME v) /\
         sptree_lookup k g = SOME a ==> val_approx_val a v)`;;

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

(* fv_max *)

let fv_max_def = cake_define
  `fv_max n xs = (!v. fv v xs ==> v < n)`;;

(* HOL4 clos_knownProofScript.sml:612-615: a proof *)

(* HOL4 clos_knownProofScript.sml:705-709: the ML values that the
   definitions below antiquote *)

(* HOL4 clos_knownProofScript.sml:883: ML code, not ported *)

(* Evaluate  *)

let gapprox_disjoint_def = cake_define
  `gapprox_disjoint g xs <=> DISJOINT (domain g) (SET_OF_BAG
  (closProps_elist_globals xs))`;;

let oracle_gapprox_disjoint_def = cake_define
  `oracle_gapprox_disjoint g co <=> (!n. gapprox_disjoint g (FST (SND
  (co n))))`;;

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

let every_var_def = cake_define_list
  [`clos_knownProof_every_var P (db_vars_Empty:db_var_set) = T`;
   `clos_knownProof_every_var P (Var v:db_var_set) <=> P v`;
   `clos_knownProof_every_var P (Shift k d:db_var_set) <=>
  clos_knownProof_every_var (\v. k <= v ==> P (v - k)) d`;
   `clos_knownProof_every_var P (Union d1 d2:db_var_set) <=>
  clos_knownProof_every_var P d1 /\ clos_knownProof_every_var P d2`];;
hol4_overload "every_var" "clos_knownProof_every_var";;

(* oracle_gapprox_subspt *)
let oracle_gapprox_subspt_def = cake_define
  `oracle_gapprox_subspt co <=>
     (!n. subspt (FST (FST (co n))) (FST (FST (co (SUC n)))))`;;

(* oracle_state_sgc_free *)
let oracle_state_sgc_free_def = cake_define
  `oracle_state_sgc_free co = (!n. globals_approx_sgc_free (FST (FST
  (co n))))`;;

let next_g_def = cake_define
  `next_g (s:(val_approx spt#'c,'ffi)closSem_state) =
     FST (FST (closSem_state_compile_oracle s 0))`;;

(**)

let mglobals_disjoint_def = cake_define
  `mglobals_disjoint s xs <=> DISJOINT (mapped_globals s) (SET_OF_BAG
  (closProps_elist_globals xs))`;;

(**)


let gapprox_extend_def = cake_define
  `gapprox_extend g1 gd g2 <=>
     (!i. i IN domain g2 /\ (i IN domain g1 ==> ~(sptree_lookup i g2
       = sptree_lookup i g1)) ==>
         i IN gd)`;;

(* essentially a duplicate of the above  *)

(* HOL4 clos_knownProofScript.sml:1893: ML code, not ported *)

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

(* value relation *)

let f_rel_def = cake_define
  `clos_knownProof_f_rel c aenv g (n1,e1) (n2,e2) <=>
      n1 = n2 /\ clos_knownProof_exp_rel c (REPLICATE n1
        clos_known_Other ++ aenv) g e1 e2`;;
hol4_overload "f_rel" "clos_knownProof_f_rel";;

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

let state_rel_def = cake_define
  `clos_knownProof_state_rel c g (s:(val_approx
  spt#'c,'ffi)closSem_state) (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = []) /\
     (!n. fv_max 0 (FST (SND (closSem_state_compile_oracle s n)))) /\
       closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\ state_clock
     s = state_clock t /\ state_ffi s = state_ffi t /\
       closSem_state_max_app s = closSem_state_max_app t /\
     LIST_REL (OPTREL (v_rel c g)) (closSem_state_globals s)
       (closSem_state_globals t) /\
     fmap_rel (ref_rel c g) (state_refs s) (state_refs t) /\
       closSem_state_compile
     s = state_cc (compile_inc c) (closSem_state_compile t) /\
       closSem_state_compile_oracle
     t = state_co (compile_inc c) (closSem_state_compile_oracle s)`;;
hol4_overload "state_rel" "clos_knownProof_state_rel";;

let co_every_Fn_vs_NONE_def = cake_define
  `co_every_Fn_vs_NONE co =
     (!n exps aux. SND (co n) = (exps,aux) ==>
       every_Fn_vs_NONE exps /\
       every_Fn_vs_NONE (MAP (SND o SND) aux))`;;

(* HOL4 clos_knownProofScript.sml:2960-2970: the ML values that the
   definitions below antiquote *)


(* Set globals in all future installs is disjoint from currently mapped globals. *)
let state_oracle_mglobals_disjoint_def = cake_define
  `state_oracle_mglobals_disjoint s <=> (!n. mglobals_disjoint
  (closSem_state_globals s) (FST (SND (closSem_state_compile_oracle s
  n))))`;;


(* HOL4 clos_knownProofScript.sml:3185: ML code, not ported *)

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

let globals_approx_every_Fn_SOME_def = cake_define
  `globals_approx_every_Fn_SOME g =
     (!c d. sptree_lookup c g = SOME d ==>
       val_approx_every_Fn_SOME d)`;;

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

let globals_approx_every_Fn_vs_NONE_def = cake_define
  `globals_approx_every_Fn_vs_NONE g =
     (!c d. sptree_lookup c g = SOME d ==>
       val_approx_every_Fn_vs_NONE d)`;;

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

let globals_approx_no_Labels_def = cake_define
  `globals_approx_no_Labels g =
     (!c d. sptree_lookup c g = SOME d ==> val_approx_no_Labels d)`;;

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

let globals_approx_obeys_max_app_def = cake_define
  `globals_approx_obeys_max_app k g =
     (!c d. sptree_lookup c g = SOME d ==>
       val_approx_obeys_max_app k d)`;;

(* names *)
