(* ======================================================== *)
(*  clos_callProof: ported from HOL4's
    compiler/backend/proofs/clos_callProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_call
*)

needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* TODO These are the same. Put in closLang? *)

(* TODO: move *)

(* HOL4 clos_callProofScript.sml:32: ML code, not ported *)

(* HOL4 clos_callProofScript.sml:63-67: ML code, not ported *)

let is_Recclosure_def = cake_define
  `is_Recclosure x1 =
      match x1 with
        (Recclosure _6 _7 _8 _9 _10:closSem_v) -> T
      | _11 -> F`;;

let every_refv_def = cake_define
  `every_refv P x2 =
        match x2 with
          closSem_ValueArray vs -> EVERY P vs
        | (Thunk m v) -> P v
        | _12 -> T`;;

(* -- *)

(* correctness of free *)

(* value relation *)

let subg_def = cake_define
  `subg g0 g1 <=>
     subspt (FST g0) (FST g1) /\
     (!k v. ALOOKUP (SND g0) k = SOME v ==> ALOOKUP (SND g1) k = SOME
       v) /\
     ALL_DISTINCT (MAP FST (SND g1))`;;

let wfg'_def = cake_define
  `wfg' g <=>
     set_of_list (MAP FST (SND g)) SUBSET IMAGE SUC (domain (FST
       g))`;;

let wfg_def = cake_define
  `wfg g <=>
     set_of_list (MAP FST (SND g)) = IMAGE SUC (domain (FST g)) /\
     ALL_DISTINCT (MAP FST (SND g))`;;

let make_g_def = cake_define
  `make_g d code =
     (if IMAGE SUC (domain d) SUBSET (FDOM code) then
       SOME (d,MAP (\k. (FST k + 1,THE (FLOOKUP code (FST k +
         1)))) (toAList d)) else NONE)`;;

let recclosure_wf_def = cake_define
  `recclosure_wf loc fns <=>
     every_Fn_SOME (MAP SND fns) /\
     every_Fn_vs_NONE (MAP SND fns) /\
     DISJOINT (set_of_list (GENLIST (\i. 2 * i + loc) (LENGTH fns)))
       (set_of_list (code_locs (MAP SND fns))) /\
     ALL_DISTINCT (code_locs (MAP SND fns))`;;

let code_includes_def = cake_define
  `code_includes al code <=>
     (!k v. ALOOKUP al k = SOME v ==> FLOOKUP code k = SOME v)`;;

let recclosure_rel_def = cake_define
  `recclosure_rel g l code loc fns1 fns2 <=> (?g0.
      recclosure_wf loc fns1 /\
      wfg g0 /\
      DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
        (set_of_list (MAP FST (SND g0))) /\
      DISJOINT (set_of_list (GENLIST (\i. 2 * i + loc + 1) (LENGTH
        fns1))) (set_of_list (MAP FST (SND g0))) /\
      (let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH
        fns1) g0) in
      if EVERY2 (\(n,_13) p. !v. has_var v (SND (clos_call_free [p]))
        ==> v < n) fns1 es then
        (?tra n. fns2 = calls_list tra n loc fns1) /\
        subg (code_list loc (ZIP (MAP FST fns1) es) new_g) g /\
        set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST
          new_g) SUBSET l /\
        code_includes (SND (code_list loc (ZIP (MAP FST fns1) es)
          new_g)) code else
        let (es,new_g) = calls (MAP SND fns1) g0 in
        fns2 = ZIP (MAP FST fns1) es /\
        subg new_g g /\
        set_of_list (code_locs (MAP SND fns1)) DIFF domain (FST
          new_g) SUBSET l /\
        set_of_list (GENLIST (\i. 2 * i + loc) (LENGTH fns1)) SUBSET
          l /\
        code_includes (SND new_g) code))`;;

let env_rel_def = cake_define
  `clos_callProof_env_rel R env1 env2 a es <=>
     (if LENGTH env1 = LENGTH env2 then LIST_REL R env1 env2 else
     !x. EXISTS (\(n,p). fv1 (n + a + x) p) es ==>
         x < LENGTH env1 /\ x < LENGTH env2 /\
         R (EL x env1) (EL x env2))`;;
hol4_overload "env_rel" "clos_callProof_env_rel";;

let _ = size_thms "closSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_callProofScript.sml:330-333: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let v_rel_def = cake_define_list_try_tac (fun () ->
  `MEASURE (closSem_v_size o FST o SND o SND o SND)`)
  CHEAT_TAC
  [`clos_callProof_v_rel g l code (closSem_Number i:closSem_v) v <=>
  v = (closSem_Number i:closSem_v)`;
   `clos_callProof_v_rel g l code (Word64 w:closSem_v) v <=> v =
  (Word64 w:closSem_v)`;
   `clos_callProof_v_rel g l code (closSem_Block n vs:closSem_v) v <=>
        (?vs'. v = closSem_Block n vs' /\ LIST_REL
          (clos_callProof_v_rel g l code) vs vs')`;
   `clos_callProof_v_rel g l code (closSem_ByteVector ws) v <=> v =
  closSem_ByteVector ws`;
   `clos_callProof_v_rel g l code (closSem_RefPtr b n:closSem_v) v
  <=> v = (closSem_RefPtr b n:closSem_v)`;
   `clos_callProof_v_rel g l code (Closure loco vs1 env1 n
  bod1:closSem_v) v <=>
         (?loc vs2 env2 bod2.
           recclosure_rel g l code loc [(n,bod1)] [(n,bod2)] /\
           v = Closure (SOME loc) vs2 env2 n bod2 /\ loco = SOME loc
             /\
           LIST_REL (clos_callProof_v_rel g l code) vs1 vs2 /\
           clos_callProof_env_rel (clos_callProof_v_rel g l code)
             env1 env2 0 [(n,bod2)])`;
   `clos_callProof_v_rel g l code (Recclosure loco vs1 env1 fns1
  i:closSem_v) v <=>
         (?loc vs2 env2 fns2.
           recclosure_rel g l code loc fns1 fns2 /\
           v = Recclosure (SOME loc) vs2 env2 fns2 i /\ loco = SOME
             loc /\
           LIST_REL (clos_callProof_v_rel g l code) vs1 vs2 /\
           clos_callProof_env_rel (clos_callProof_v_rel g l
             code) env1 env2 (LENGTH fns2) fns2)`];;
hol4_overload "v_rel" "clos_callProof_v_rel";;

(* HOL4 clos_callProofScript.sml:335: ML code, not ported *)

let _ = size_thms "closSem_v";;
(* HOL4 clos_callProofScript.sml:350-353: the tactic that proves the
   termination *)
let wfv_def = cake_define_wf
  `MEASURE (closSem_v_size o SND o SND o SND)`
  `wfv g l code x4 =
        match x4 with
          (Closure NONE _18 _19 _20 _21:closSem_v) -> F
        | (Recclosure NONE _22 _23 _24 _25) -> F
        | (Closure (SOME loc) vs env n bod) ->
       EVERY (wfv g l code) vs /\ EVERY (wfv g l code) env /\
       (?fns2.
       recclosure_rel g l code loc [(n,bod)] fns2)
        | (Recclosure (SOME loc) vs env fns i) ->
       EVERY (wfv g l code) vs /\ EVERY (wfv g l code) env /\
       (?fns2.
       recclosure_rel g l code loc fns fns2)
        | (closSem_Block _26 vs) -> EVERY (wfv g l code) vs
        | _27 -> T`;;

(* HOL4 clos_callProofScript.sml:355: ML code, not ported *)

let wfv_state_def = cake_define
  `wfv_state g l code s <=>
     EVERY (OPTION_ALL (wfv g l code)) (closSem_state_globals s) /\
     FEVERY (every_refv (wfv g l code) o SND) (state_refs s) /\
       closSem_state_code
     s = FEMPTY`;;

new_type_abbrev("calls_state",`: 1 spt#(num#num#closLang_exp) list`);;
new_type_abbrev("abs_calls_state",`: 1 spt`);;

let state_rel_def = cake_define
  `clos_callProof_state_rel g l (s:(1 spt#'c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (state_ffi s = state_ffi t) /\
     (state_clock s = state_clock t) /\
     (closSem_state_max_app s = closSem_state_max_app t) /\
     LIST_REL (OPTREL (clos_callProof_v_rel g l (closSem_state_code
       t))) (closSem_state_globals s) (closSem_state_globals t) /\
     fmap_rel (closProps_ref_rel (clos_callProof_v_rel g l
       (closSem_state_code t))) (state_refs s) (state_refs t) /\
       closSem_state_code
     s = FEMPTY`;;
hol4_overload "state_rel" "clos_callProof_state_rel";;

(* syntactic properties of compiler *)

let insert_each'_def = cake_define_list
  [`insert_each' gt p 0 g = g`;
   `insert_each' gt p (SUC n) (g1,g2) =
       insert_each' gt (p + 2) n (sptree_insert p one g1,((p +
         1,THE (ALOOKUP gt (p + 1))) :: g2))`];;

(* HOL4 clos_callProofScript.sml:965: ML code, not ported *)

(* HOL4 clos_callProofScript.sml:1102-1114: a proof *)

(* properties of value relation *)

(* semantic functions respect relation *)

let syntax_ok_def = cake_define
  `clos_callProof_syntax_ok x <=> every_Fn_SOME x /\ every_Fn_vs_NONE
  x /\ ALL_DISTINCT (code_locs x)`;;
hol4_overload "syntax_ok" "clos_callProof_syntax_ok";;

let co_ok_def = cake_define
  `co_ok code co full_gs k <=>
     (if k = 0 then T else
       let g = FST (FST (co 0)) in
       let (cfg,exp,aux) = co 0 in
       let (g',exp',aux1) = clos_call_compile_inc g (exp,aux) in
         FST (FST (co 1)) = g' /\
         make_g g code = SOME (full_gs 0) /\
         (!i. subg (full_gs 0) (full_gs i)) /\
         (!x i. MEM x (code_locs exp) /\ ~(x IN domain g') ==> ~(
                x IN domain (FST (FST (co i))))) /\
         DISJOINT (set_of_list (code_locs exp)) (domain g) /\
         DISJOINT (FDOM code) (set_of_list (MAP FST aux1)) /\
         ALL_DISTINCT (MAP FST aux1) /\
         co_ok (code |++ aux1) (misc_shift_seq 1 co)
           (misc_shift_seq 1 full_gs) (k - 1))`;;

let code_inv_def = cake_define
  `code_inv g1_opt l1 (s_code:(num,num#closLang_exp)fmap)
         s_cc s_co t_code t_cc t_co <=>
     s_code = FEMPTY /\
     s_cc = state_cc clos_call_compile_inc t_cc /\
     t_co = state_co clos_call_compile_inc s_co /\
     (?g aux. wfg (g,aux) /\
         FST (FST (s_co 0)) = g /\
         oracle_monotonic (set_of_list o code_locs o FST o SND) (<)
             (domain g UNION l1) s_co /\
         t_code = alist_to_fmap aux /\
         (IS_SOME g1_opt ==> g1_opt = SOME (g,aux))) /\
     (!k. let (cfg,exp,aux) = s_co (k:num) in
         clos_callProof_syntax_ok exp /\ aux = [])`;;

(* HOL4 clos_callProofScript.sml:2113-2120: code that the source has
   in a comment *)

let includes_state_def = cake_define
  `includes_state g1 s_compile_oracle <=>
     (?(k:num). FST (FST (s_compile_oracle k)) = FST g1)`;;

(* HOL4 clos_callProofScript.sml:2145-2151: code that the source has
   in a comment *)

(* HOL4 clos_callProofScript.sml:2331-2381: code that the source has
   in a comment *)

let mk_code_g_def = cake_define
  `mk_code_g code = (list_to_num_set (MAP PRE (SET_TO_LIST (FDOM
  code))),
     fmap_to_alist code)`;;

(* HOL4 clos_callProofScript.sml:2400-2402: ML code, not ported *)

(* HOL4 clos_callProofScript.sml:2404-2405: ML code, not ported *)

(* compiler correctness *)

(* HOL4 clos_callProofScript.sml:2429: the ML values that the
   definitions below antiquote *)

(*
max_print_depth := 8
max_print_depth := 80
max_print_depth := 800
*)

(* HOL4 clos_callProofScript.sml:2437-2438: ML code, not ported *)

(* All code_locs come from the original code,
   and therefore, are all even
*)

(* the all distinctness of code_locs is preserved *)

let nth_code_def = cake_define_list
  [`clos_callProof_nth_code code co 0 = code`;
   `clos_callProof_nth_code code co (SUC k) =
      (let (cfg,exp,aux) = co 0 in
      let (g',exp',aux') = clos_call_compile_inc (FST cfg) (exp,aux)
        in
        clos_callProof_nth_code (code |++ aux') (misc_shift_seq
          1 co) k)`];;
hol4_overload "nth_code" "clos_callProof_nth_code";;

(* TODO: move *)

(* Preservation of some label properties
  every_Fn_SOME xs ∧ every_Fn_vs_NONE xs
*)

(* HOL4 clos_callProofScript.sml:4672-4684: code that the source has
   in a comment *)

(* obeys_max_app and no_Labels *)

let state_syntax_def = cake_define
  `state_syntax f ((g,xs):1 spt#(num#num#closLang_exp) list) = EVERY
  (\(x1,x2,x3). f x3) xs`;;

(* names *)

(* HOL4 clos_callProofScript.sml:4766-4909: code that the source has
   in a comment *)
