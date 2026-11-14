(* ======================================================== *)
(*  clos_callProof: ported from HOL4's
    compiler/backend/proofs/clos_callProofScript.sml
    A proof theory about clos_call.ml, with 22 definitions and 140
    theorems.  Needed by clos_to_bvlProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for clos_call
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/indexedLists.ml";;
needs "lib/sptree.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_callProof"
  ["backendProps"; "closProps"; "closSem"; "clos_call"; "db_vars"];;

let _ = do_list hide_constant ["C"; "vars"];;

(* TODO These are the same. Put in closLang? *)
(* HOL4 clos_callProofScript.sml:19-21: an overload that the source
   brings to the front: free, written out as clos_call_free *)
(* HOL4 clos_callProofScript.sml:19-21: an overload that the source
   brings to the front: closed, written out as clos_call_closed *)
(* HOL4 clos_callProofScript.sml:19-21: an overload that the source
   brings to the front: compile, written out as clos_call_compile *)

(* HOL4 clos_callProofScript.sml:23-28: an overload that the source
   brings to the front: lookup, written out as sptree_lookup *)
(* HOL4 clos_callProofScript.sml:23-28: an overload that the source
   brings to the front: insert, written out as sptree_insert *)
(* HOL4 clos_callProofScript.sml:23-28: an overload that the source
   brings to the front: delete, written out as sptree_delete *)
(* HOL4 clos_callProofScript.sml:23-28: an overload that the source
   brings to the front: map, written out as sptree_map *)
(* HOL4 clos_callProofScript.sml:23-28: an overload that the source
   brings to the front: wf, written out as sptree_wf *)
(* HOL4 clos_callProofScript.sml:23-28: an overload that the source
   brings to the front: domain *)

(* TODO: move *)

(* HOL4 clos_callProofScript.sml:32: ML code, not ported *)

(* HOL4 clos_callProofScript.sml:34-39: a theorem whose statement the
   port cannot state yet: v_size_lemma *)

(* [simp] *)
let code_locs_GENLIST_Var = prove
 (`!n t i. code_locs (GENLIST_Var t i n) = []`,
  CHEAT_TAC);;

let fv_GENLIST_Var_tra = prove
 (`!n tra i. fv v (GENLIST_Var tra i n) <=> v < n`,
  CHEAT_TAC);;

let evaluate_GENLIST_Var_tra = prove
 (`!n tr i.
   closSem_evaluate (GENLIST_Var tr i n,env,s) =
   (if n <= LENGTH env then (Rval (TAKE n env),s) else (Rerr
     (Rabort Rtype_error),s))`,
  CHEAT_TAC);;

(* HOL4 clos_callProofScript.sml:63-67: ML code, not ported *)

let is_Recclosure_def = new_definition
  `is_Recclosure x1 =
      match x1 with
        (closSem_Recclosure _6 _7 _8 _9 _10:closSem_v) -> T
      | _11 -> F`;;

let every_refv_def = new_definition
  `every_refv P x2 =
        match x2 with
          closSem_ValueArray vs -> ALL P vs
        | (closSem_Thunk m v) -> P v
        | _12 -> T`;;

(* [local] *)
let IMP_EXISTS_IFF = prove
 (`!xs. (!x. MEM x xs ==> (P x <=> Q x)) ==>
          (EX P xs <=> EX Q xs)`,
  CHEAT_TAC);;

(* -- *)

(* correctness of free *)

let free_thm = prove
 (`!xs.
     let (ys,l) = clos_call_free xs in
       !n. (fv n ys = has_var n l) /\
           (fv n xs = has_var n l)`,
  CHEAT_TAC);;

(* value relation *)

let subg_def = new_definition
  `subg g0 g1 <=>
     subspt (FST g0) (FST g1) /\
     (!k v. ALOOKUP (SND g0) k = SOME v ==> ALOOKUP (SND g1) k = SOME
       v) /\
     ALL_DISTINCT (MAP FST (SND g1))`;;

let subg_refl = prove
 (`!g. ALL_DISTINCT (MAP FST (SND g)) ==> subg g g`,
  CHEAT_TAC);;

let subg_trans = prove
 (`!g1 g2 g3. subg g1 g2 /\ subg g2 g3 ==> subg g1 g3`,
  CHEAT_TAC);;

let wfg'_def = new_definition
  `wfg' g <=>
     set_of_list (MAP FST (SND g)) SUBSET IMAGE SUC (domain (FST
       g))`;;

let wfg_def = new_definition
  `wfg g <=>
     set_of_list (MAP FST (SND g)) = IMAGE SUC (domain (FST g)) /\
     ALL_DISTINCT (MAP FST (SND g))`;;

let make_g_def = new_definition
  `make_g d code =
     (if IMAGE SUC (domain d) SUBSET (FDOM code) then
       SOME (d,MAP (\k. (FST k + 1,THE (FLOOKUP code (FST k +
         1)))) (toAList d)) else NONE)`;;

(* [local] *)
let ALL_DISTINCT_MAP_FST_ADD1 = prove
 (`!xs. ALL_DISTINCT (MAP (\k. FST k + 1) xs) =
        ALL_DISTINCT (MAP FST xs)`,
  CHEAT_TAC);;

let make_g_wfg = prove
 (`make_g d code = SOME g ==> wfg g`,
  CHEAT_TAC);;

let make_g_subg = prove
 (`make_g cfg (FEMPTY |++ aux) = SOME new /\ wfg (cfg,aux) ==>
    subg (cfg,aux) new`,
  CHEAT_TAC);;

let make_g_make_g_eq = prove
 (`!x1 x2 y1 y2 g0 g1.
      FST g0 = FST g1 /\ subg g0 g1 /\
      make_g x1 x2 = SOME g0 /\ make_g y1 y2 = SOME g1 ==> g0 = g1`,
  CHEAT_TAC);;

let make_g_IMP_subg = prove
 (`make_g (r0:1 spt) code = SOME g0 /\
    DISJOINT (FDOM code) (set_of_list (MAP FST progs1)) /\
    ALL_DISTINCT (MAP FST progs1) /\
    make_g r1 (code |++ progs1) = SOME g1 /\ subspt r0 r1 /\
    set_of_list (MAP FST progs1) SUBSET IMAGE SUC (domain r1) ==>
    subg (r1,APPEND progs1 (SND g0)) g1`,
  CHEAT_TAC);;

let recclosure_wf_def = new_definition
  `recclosure_wf loc fns <=>
     every_Fn_SOME (MAP SND fns) /\
     every_Fn_vs_NONE (MAP SND fns) /\
     DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc) (LENGTH
       fns))) (set_of_list (code_locs (MAP SND fns))) /\
     ALL_DISTINCT (code_locs (MAP SND fns))`;;

let code_includes_def = new_definition
  `code_includes al code <=>
     (!k v. ALOOKUP al k = SOME v ==> FLOOKUP code k = SOME v)`;;

let recclosure_rel_def = new_definition
  `recclosure_rel g l code loc fns1 fns2 <=> (?g0.
      recclosure_wf loc fns1 /\
      wfg g0 /\
      DISJOINT (IMAGE SUC (set_of_list (code_locs (MAP SND fns1))))
        (set_of_list (MAP FST (SND g0))) /\
      DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1)
        (LENGTH fns1))) (set_of_list (MAP FST (SND g0))) /\
      (let (es,new_g) = calls (MAP SND fns1) (insert_each loc (LENGTH
        fns1) g0) in
      if ALL2 (\(n,_13) p. !v. has_var v (SND (clos_call_free [p]))
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
        set_of_list (list_of_seq (\i. 2 * i + loc) (LENGTH fns1))
          SUBSET l /\
        code_includes (SND new_g) code))`;;

let clos_callProof_env_rel_def = new_definition
  `clos_callProof_env_rel R env1 env2 a es <=>
     (if LENGTH env1 = LENGTH env2 then ALL2 R env1 env2 else
     !x. EX (\(n,p). fv1 (n + a + x) p) es ==>
         x < LENGTH env1 /\ x < LENGTH env2 /\
         R (EL x env1) (EL x env2))`;;

(* [mono] *)
let env_rel_mono = prove
 (`(!x y. MEM x env1 /\ MEM y env2 /\ R x y ==> R' x y) ==>
   clos_callProof_env_rel R env1 env2 a es ==>
   clos_callProof_env_rel R' env1 env2 a es`,
  CHEAT_TAC);;

(* [defncong] *)
let env_rel_cong = prove
 (`(!x y. MEM x env1 /\ MEM y env2 ==> (R x y <=> R' x y)) ==>
  clos_callProof_env_rel R env1 env2 a es = clos_callProof_env_rel R'
  env1 env2 a es`,
  CHEAT_TAC);;

let clos_callProof_v_rel_def,clos_callProof_v_rel_ind =
  assume_definition_rec
  "termination (CHEAT_TAC)"
  [`clos_callProof_v_rel g l code (closSem_Number i:closSem_v) v <=>
  v = (closSem_Number i:closSem_v)`;
   `clos_callProof_v_rel g l code (closSem_Word64 w:closSem_v) v <=>
  v = (closSem_Word64 w:closSem_v)`;
   `clos_callProof_v_rel g l code (closSem_Block n vs:closSem_v) v <=>
        (?vs'. v = closSem_Block n vs' /\ ALL2
          (clos_callProof_v_rel g l code) vs vs')`;
   `clos_callProof_v_rel g l code (closSem_ByteVector ws) v <=> v =
  closSem_ByteVector ws`;
   `clos_callProof_v_rel g l code (closSem_RefPtr b n:closSem_v) v
  <=> v = (closSem_RefPtr b n:closSem_v)`;
   `clos_callProof_v_rel g l code (closSem_Closure loco vs1 env1 n
  bod1:closSem_v) v <=>
         (?loc vs2 env2 bod2.
           recclosure_rel g l code loc [(n,bod1)] [(n,bod2)] /\
           v = closSem_Closure (SOME loc) vs2 env2 n bod2 /\ loco =
             SOME loc /\
           ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
           clos_callProof_env_rel (clos_callProof_v_rel g l code)
             env1 env2 0 [(n,bod2)])`;
   `clos_callProof_v_rel g l code (closSem_Recclosure loco vs1 env1 fns1
  i:closSem_v) v <=>
         (?loc vs2 env2 fns2.
           recclosure_rel g l code loc fns1 fns2 /\
           v = closSem_Recclosure (SOME loc) vs2 env2 fns2 i /\ loco
             = SOME loc /\
           ALL2 (clos_callProof_v_rel g l code) vs1 vs2 /\
           clos_callProof_env_rel (clos_callProof_v_rel g l
             code) env1 env2 (LENGTH fns2) fns2)`];;

(* HOL4 clos_callProofScript.sml:335: ML code, not ported *)

let _ = size_thms "closSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_callProofScript.sml:350-353: the tactic that proves the
   termination *)
let wfv_def,wfv_ind = define_wf
  `MEASURE (closSem_v_size o SND o SND o SND)`
  [`wfv g l code x4 =
        match x4 with
          (closSem_Closure NONE _18 _19 _20 _21:closSem_v) -> F
        | (closSem_Recclosure NONE _22 _23 _24 _25) -> F
        | (closSem_Closure (SOME loc) vs env n bod) ->
       ALL (wfv g l code) vs /\ ALL (wfv g l code) env /\
       (?fns2.
       recclosure_rel g l code loc [(n,bod)] fns2)
        | (closSem_Recclosure (SOME loc) vs env fns i) ->
       ALL (wfv g l code) vs /\ ALL (wfv g l code) env /\
       (?fns2.
       recclosure_rel g l code loc fns fns2)
        | (closSem_Block _26 vs) -> ALL (wfv g l code) vs
        | _27 -> T`];;

(* HOL4 clos_callProofScript.sml:355: ML code, not ported *)

let wfv_state_def = new_definition
  `wfv_state g l code s <=>
     ALL (OPTION_ALL (wfv g l code)) (closSem_state_globals s) /\
     FEVERY (every_refv (wfv g l code) o SND) (state_refs s) /\
       closSem_state_code
     s = FEMPTY`;;

new_type_abbrev("calls_state",`: 1 spt#(num#num#closLang_exp) list`);;
new_type_abbrev("abs_calls_state",`: 1 spt`);;

let clos_callProof_state_rel_def = new_definition
  `clos_callProof_state_rel g l (s:(1 spt#'c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (closSem_state_ffi s = closSem_state_ffi t) /\
     (closSem_state_clock s = closSem_state_clock t) /\
     (closSem_state_max_app s = closSem_state_max_app t) /\
     ALL2 (OPTREL (clos_callProof_v_rel g l (closSem_state_code t)))
       (closSem_state_globals s) (closSem_state_globals t) /\
     fmap_rel (closProps_ref_rel (clos_callProof_v_rel g l
       (closSem_state_code t))) (closSem_state_refs s)
       (closSem_state_refs t) /\ closSem_state_code
     s = FEMPTY`;;

(* state_rel_max_app *)
let clos_callProof_state_rel_max_app = prove
 (`clos_callProof_state_rel g l s t ==> closSem_state_max_app s =
  closSem_state_max_app t`,
  CHEAT_TAC);;

let state_rel_clock = prove
 (`clos_callProof_state_rel g l s t ==> state_clock s = state_clock t`,
  CHEAT_TAC);;

(* state_rel_with_clock *)
let clos_callProof_state_rel_with_clock = prove
 (`clos_callProof_state_rel g l s t ==> clos_callProof_state_rel g l
  (state_clock_fupd (K k) s) (state_clock_fupd (K k) t)`,
  CHEAT_TAC);;

let state_rel_flookup_refs = prove
 (`clos_callProof_state_rel g l s t /\ FLOOKUP (state_refs s) k = SOME v
  ==>
   (?v'. FLOOKUP (state_refs t) k = SOME v' /\ closProps_ref_rel
     (clos_callProof_v_rel g l (closSem_state_code t)) v v')`,
  CHEAT_TAC);;

(* syntactic properties of compiler *)

(* [simp] *)
let FST_code_list = prove
 (`!loc fns g. FST (code_list loc fns g) = FST g`,
  CHEAT_TAC);;

(* [simp] *)
let SND_insert_each = prove
 (`!p n g. SND (insert_each p n g) = SND g`,
  CHEAT_TAC);;

let calls_list_MAPi = prove
 (`!loc tra n. calls_list t n loc = MAPi (\i p. (FST p,closLang_Call t
  0 (loc + 2 * i + 1) (GENLIST_Var t 1 (FST p))))`,
  CHEAT_TAC);;

(* [simp] *)
let calls_list_length = prove
 (`LENGTH (calls_list t n p fns) = LENGTH fns`,
  CHEAT_TAC);;

let domain_FST_insert_each = prove
 (`!p n g. domain (FST (insert_each p n g)) = set_of_list (list_of_seq
  (\i. 2 * i + p) n) UNION domain (FST g)`,
  CHEAT_TAC);;

let SND_code_list_change = prove
 (`!loc fns g g'. SND g = SND g' ==>
    SND (code_list loc fns g) = SND (code_list loc fns g')`,
  CHEAT_TAC);;

let MAP_FST_code_list = prove
 (`!loc fns g.
    MAP FST (SND (code_list loc fns g)) = APPEND (REVERSE
      (list_of_seq (\i. loc + i * 2 + 1) (LENGTH fns))) (MAP FST (SND
      g))`,
  CHEAT_TAC);;

let SND_code_list_ZIP = prove
 (`!loc fns g. SND (code_list loc fns g) = APPEND (REVERSE (ZIP
  (list_of_seq ((+) (loc + 1) o (*) 2) (LENGTH fns)) fns)) (SND g)`,
  CHEAT_TAC);;

let ALOOKUP_code_list = prove
 (`!loc fns g k.
    ALOOKUP (SND (code_list loc fns g)) k =
    (match some (\i. i < LENGTH fns /\ k = loc + 2 * i + 1) with
      SOME i -> SOME (EL i fns) | NONE -> ALOOKUP (SND g) k)`,
  CHEAT_TAC);;

let insert_each_subspt = prove
 (`!p n g. subspt (FST g) (FST (insert_each p n g))`,
  CHEAT_TAC);;

let code_list_IS_SUFFIX = prove
 (`!loc fns g. IS_SUFFIX (SND (code_list loc fns g)) (SND g)`,
  CHEAT_TAC);;

let calls_subspt = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==> subspt (FST g0) (FST g)`,
  CHEAT_TAC);;

let calls_code_subset = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
      IMAGE SUC (domain (FST g0)) SUBSET IMAGE SUC (domain (FST g))
        /\
      set_of_list (MAP FST (SND g0)) SUBSET set_of_list (MAP FST (SND
        g)) /\
      set_of_list (MAP FST (SND g)) SUBSET
        IMAGE SUC (domain (FST g)) UNION set_of_list (MAP FST (SND
          g0))`,
  CHEAT_TAC);;

let calls_IS_SUFFIX = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==> IS_SUFFIX (SND g) (SND g0)`,
  CHEAT_TAC);;

let calls_add_SUC_code_locs = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
    set_of_list (MAP FST (SND g)) SUBSET
    set_of_list (MAP FST (SND g0)) UNION IMAGE SUC (set_of_list
      (code_locs xs))`,
  CHEAT_TAC);;

let calls_ALL_DISTINCT = prove
 (`!xs g0 ys g.
    calls xs g0 = (ys,g) /\ ALL_DISTINCT (MAP FST (SND g0)) /\
    ALL_DISTINCT (code_locs xs) /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list
      (MAP FST (SND g0))) ==> ALL_DISTINCT (MAP FST (SND g))`,
  CHEAT_TAC);;

let compile_ALL_DISTINCT = prove
 (`clos_call_compile do_call x = (y,g,aux) /\
   ALL_DISTINCT (code_locs x) ==>
   ALL_DISTINCT (MAP FST aux)`,
  CHEAT_TAC);;

let calls_subg = prove
 (`!xs g0 ys g.
    calls xs g0 = (ys,g) /\
    ALL_DISTINCT (MAP FST (SND g0)) /\
    ALL_DISTINCT (code_locs xs) /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list
      (MAP FST (SND g0))) ==> subg g0 g`,
  CHEAT_TAC);;

let calls_domain = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
    domain (FST g) SUBSET domain (FST g0) UNION IMAGE PRE
      (set_of_list (MAP FST (SND g)))`,
  CHEAT_TAC);;

let calls_domain_locs = prove
 (`!xs g ys g2. calls xs g = (ys,g2) ==>
   domain (FST g2) SUBSET domain (FST g) UNION set_of_list
     (code_locs xs)`,
  CHEAT_TAC);;

let wfg'_insert_each = prove
 (`!n g loc. wfg' g ==> wfg' (insert_each loc n g)`,
  CHEAT_TAC);;

let wfg'_code_list = prove
 (`!ls g loc.
      wfg' g /\ set_of_list (list_of_seq (\i. loc + 2 * i) (LENGTH
        ls)) SUBSET domain (FST g) ==> wfg' (code_list loc ls g)`,
  CHEAT_TAC);;

let closed_Fn = prove
 (`clos_call_closed (closLang_Fn t loco vs args e) <=>
   (!v. has_var v (SND (clos_call_free [e])) ==> v < args)`,
  CHEAT_TAC);;

let closed_Fn_fv = prove
 (`clos_call_closed (closLang_Fn t loco vs args e) <=>
   (!v. fv v [e] ==> v < args)`,
  CHEAT_TAC);;

let calls_wfg' = prove
 (`!xs g0 ys g.
    calls xs g0 = (ys,g) /\
    every_Fn_SOME xs /\ wfg' g0 ==>
    wfg' g`,
  CHEAT_TAC);;

let calls_wfg = prove
 (`!xs g0 ys g.
    calls xs g0 = (ys,g) /\
    ALL_DISTINCT (code_locs xs) /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list
      (MAP FST (SND g0))) /\
    every_Fn_SOME xs /\ wfg g0 ==>
    wfg g`,
  CHEAT_TAC);;

let calls_fv1_subset = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
    ALL2 (\x y. (hol4_C fv1) y SUBSET (hol4_C fv1) x) xs ys`,
  CHEAT_TAC);;

let calls_fv_imp = prove
 (`calls xs g0 = (ys,g) /\ fv v ys ==> fv v xs`,
  CHEAT_TAC);;

let FST_insert_each_same = prove
 (`!p n g0 g0'.
    FST g0 = FST g0' ==> FST (insert_each p n g0) = FST
      (insert_each p n g0')`,
  CHEAT_TAC);;

let code_list_replace_SND = prove
 (`!loc fns g0 g g0' ls.
   code_list loc fns g0 = g /\
   FST g0 = FST g0' /\
   SND g = APPEND ls (SND g0) ==>
   code_list loc fns g0' = (FST g,APPEND ls (SND g0'))`,
  CHEAT_TAC);;

let calls_replace_SND = prove
 (`!xs g0 ys g g0' ls.
    calls xs g0 = (ys,g) /\
    FST g0 = FST g0' /\
    SND g = APPEND ls (SND g0) ==>
    calls xs g0' = (ys,(FST g,APPEND ls (SND g0')))`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let insert_each'_def,insert_each'_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). list_size (pair_size (\n. n) (\x. 0)) x0)`
  [`insert_each' gt p 0 g = g`;
   `insert_each' gt p (SUC n) (g1,g2) =
       insert_each' gt (p + 2) n (sptree_insert p one g1,(CONS
         (p + 1,THE (ALOOKUP gt (p + 1))) g2))`];;

(* HOL4 clos_callProofScript.sml:965: ML code, not ported *)

let wfg_insert_each' = prove
 (`!gt p n g.
    wfg g /\
    DISJOINT (set_of_list (list_of_seq (\i. p + 2 * i) n)) (domain
      (FST g)) ==> wfg (insert_each' gt p n g)`,
  CHEAT_TAC);;

let FST_insert_each' = prove
 (`!gt p n g. FST (insert_each' gt p n g) = FST (insert_each p n g)`,
  CHEAT_TAC);;

let MAP_FST_insert_each' = prove
 (`!gt p n g.
   MAP FST (SND (insert_each' gt p n g)) = APPEND (REVERSE
     (list_of_seq (\i. p + i * 2 + 1) n))
   (MAP FST (SND g))`,
  CHEAT_TAC);;

let SND_insert_each' = prove
 (`!gt p n g. SND (insert_each' gt p n g) = APPEND (REVERSE
  (list_of_seq (\i. (2 * i + p + 1,THE (ALOOKUP gt (2 * i + p + 1))))
  n)) (SND g)`,
  CHEAT_TAC);;

let calls_el_sing = prove
 (`!xs g0 ys g i.
    calls xs g0 = (ys,g) /\
    i < LENGTH xs /\
    ALL_DISTINCT (MAP FST (SND g0)) /\
    ALL_DISTINCT (code_locs xs) /\
    DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list
      (MAP FST (SND g0))) /\
    wfg g0 /\ every_Fn_SOME xs ==>
     (?ga gb.
       calls [EL i xs] ga = ([EL i ys],gb) /\
       subg g0 ga /\ subg ga gb /\ subg gb g /\ wfg ga /\ wfg gb /\
       DISJOINT (IMAGE SUC (set_of_list (code_locs [EL i xs])))
         (set_of_list (MAP FST (SND ga))) /\
       set_of_list (MAP FST (SND ga)) SUBSET set_of_list (MAP FST
         (SND g0)) UNION IMAGE SUC (set_of_list (code_locs (TAKE i xs)))
         /\
       (set_of_list (code_locs [EL i xs]) DIFF (domain (FST gb)))
         SUBSET (set_of_list (code_locs xs) DIFF (domain (FST g))))`,
  CHEAT_TAC);;

(* HOL4 clos_callProofScript.sml:1102-1114: a proof *)

let insert_each_pair_arg = prove
 (`insert_each x y (p,q) = (FST (insert_each x y (p,q')),q)`,
  CHEAT_TAC);;

(* [local] *)
let calls_acc_0 = prove
 (`!xs tmp x r. APPEND x r = SND tmp ==>
      calls xs tmp = (I ## I ## (hol4_C APPEND r)) (calls xs (FST
        tmp,x))`,
  CHEAT_TAC);;

let calls_acc = prove
 (`!xs d old res d1 aux.
      calls xs (d,[]) = (res,d1,aux) ==>
      calls xs (d,old) = (res,d1,APPEND aux old)`,
  CHEAT_TAC);;

(* properties of value relation *)

let v_rel_exists = prove
 (`!v1. wfv g l code v1 ==> (?v2. clos_callProof_v_rel g l code v1 v2)`,
  CHEAT_TAC);;

let v_rel_subg = prove
 (`!g l code v1 v2 g' l'.
    clos_callProof_v_rel g l code v1 v2 /\ subg g g' /\ l SUBSET l'
      ==>
    clos_callProof_v_rel g' l' code v1 v2`,
  CHEAT_TAC);;

let code_includes_subg = prove
 (`subg g1 g2 ==> code_includes (SND g2) code ==> code_includes (SND
  g1) code`,
  CHEAT_TAC);;

let code_includes_ALOOKUP = prove
 (`code_includes al code /\ ALOOKUP al loc = SOME r ==> FLOOKUP code
  loc = SOME r`,
  CHEAT_TAC);;

let dest_closure_v_rel_lookup = prove
 (`dest_closure max_app (SOME loc) v1 env1 = SOME x /\
   clos_callProof_v_rel g l code v1 v2 /\
   ALL2 (clos_callProof_v_rel g l code) env1 env2 /\
   wfg g /\ loc IN domain (FST g) /\ ~(loc IN l) ==>
   (?e l1 xs n ls g01 g1 l1' tra i.
     x = Full_app e (APPEND env1 l1) [] /\ EL n xs = (LENGTH env1,e)
       /\
     calls (MAP SND xs) g01 = (ls,g1) /\ n < LENGTH ls /\
     subg (code_list (loc - 2 * n) (ZIP (MAP FST xs) ls) g1) g /\
     ALOOKUP (SND g) (loc + 1) = SOME (LENGTH env1,EL n ls) /\
     dest_closure max_app (SOME loc) v2 env2 =
       SOME (Full_app (closLang_Call tra 0 (loc + 1)
         (GENLIST_Var tra 1 (LENGTH env1))) (APPEND env2 l1') []) /\
     code_includes (SND (code_list (loc - 2 * n) (ZIP (MAP FST xs)
       ls) g1)) code)`,
  CHEAT_TAC);;

let dest_closure_v_rel = prove
 (`dest_closure max_app loco v1 env1 = SOME x1 /\
   clos_callProof_v_rel g l code v1 v2 /\
   ALL2 (clos_callProof_v_rel g l code) env1 env2 ==>
   (?x2.
   dest_closure max_app loco v2 env2 = SOME x2 /\
   (match x1 with Partial_app c1 ->
     (?c2. x2 = Partial_app c2 /\ clos_callProof_v_rel g l code c1
       c2) | Full_app e1 args1 rest1 ->
      (?fns1 loc i fns2 args2 rest2 n.
        x2 = Full_app (SND (EL i fns2)) args2 rest2 /\
        (let m = (if is_Recclosure v2 then LENGTH fns2 else 0) in
         n + m <= LENGTH args1 /\ n + m <= LENGTH args2 /\
         ALL2 (clos_callProof_v_rel g l code) (TAKE (n + m) args1)
           (TAKE (n + m) args2) /\
         clos_callProof_env_rel (clos_callProof_v_rel g l code) (DROP
           (n + m) args1)
                              (DROP (n + m) args2) m [EL i fns2]) /\
        ALL2 (clos_callProof_v_rel g l code) rest1 rest2 /\
        recclosure_rel g l code loc fns1 fns2 /\
        i < LENGTH fns1 /\
        EL i fns1 = (n,e1))))`,
  CHEAT_TAC);;

let dest_closure_partial_wfv = prove
 (`dest_closure max_app loco v env = SOME (Partial_app x) /\
   ALL (wfv g l code) env /\ wfv g l code v ==> wfv g l code x`,
  CHEAT_TAC);;

let dest_closure_full_wfv = prove
 (`dest_closure max_app loco v env = SOME (Full_app e args rest) /\
   wfv g l code v /\ ALL (wfv g l code) env ==>
   (?ys g01 loc fns1 fns2 i.
     ALL (wfv g l code) args /\ ALL (wfv g l code) rest /\
     recclosure_rel g l code loc fns1 fns2 /\
     SND (EL i fns1) = e /\ i < LENGTH fns1)`,
  CHEAT_TAC);;

let env_rel_DROP = prove
 (`clos_callProof_env_rel R (DROP x l1) (DROP x l2) x es /\
   ALL2 R (TAKE x l1) (TAKE x l2) /\
   x <= LENGTH l1 /\ x <= LENGTH l2 ==>
   clos_callProof_env_rel R l1 l2 0 es`,
  CHEAT_TAC);;

let env_rel_DROP_args = prove
 (`clos_callProof_env_rel R (DROP n l1) (DROP n l2) a [(n,e)] /\
   ALL2 R (TAKE n l1) (TAKE n l2) /\
   n <= LENGTH l1 /\ n <= LENGTH l2 ==>
   clos_callProof_env_rel R l1 l2 a [(0,e)]`,
  CHEAT_TAC);;

let subg_insert_each' = prove
 (`!gb fns1 es g1.
      subg gb (FST new_g,APPEND l (SND (insert_each' g1 loc (LENGTH
        fns1) g))) /\
      SND new_g = APPEND l (SND g) /\
      LENGTH fns1 = LENGTH es /\ wfg g /\
      DISJOINT (set_of_list (list_of_seq (\i. 2 * i + loc + 1)
        (LENGTH fns1))) (IMAGE SUC (domain (FST g))) /\
      DISJOINT (set_of_list (MAP FST l)) (IMAGE SUC (domain (FST g)))
        /\
      (!i. i < LENGTH fns1 ==> ALOOKUP g1 (2 * i + loc + 1) = SOME
        (FST (EL i fns1),EL i es)) ==>
      subg (FST new_g,APPEND l (SND (insert_each' g1 loc (LENGTH
        fns1) g)))
        (code_list loc (ZIP (MAP FST fns1) es) new_g)`,
  CHEAT_TAC);;

(* [local] *)
let code_includes_SUBMAP = prove
 (`code_includes x y1 /\ y1 SUBMAP y2 ==> code_includes x y2`,
  CHEAT_TAC);;

let wfv_subg = prove
 (`!g l code v g' l' code'.
     wfv g l code v /\ code SUBMAP code' /\ subg g g' /\ l SUBSET
       l' ==> wfv g' l' code' v`,
  CHEAT_TAC);;

let wfv_SUBMAP = prove
 (`!g1 l1 code v code1.
      wfv g1 l1 code v /\ code SUBMAP code1 ==> wfv g1 l1 code1 v`,
  CHEAT_TAC);;

let EVERY_wfv_SUBMAP = prove
 (`ALL (wfv g1 l1 code) env /\ code SUBMAP code1 ==>
    ALL (wfv g1 l1 code1) env`,
  CHEAT_TAC);;

let EVERY_wfv_subg = prove
 (`ALL (wfv g l code) env /\ code SUBMAP code2 /\ subg g g2 /\ l SUBSET
  l2 ==>
     ALL (wfv g2 l2 code2) env`,
  CHEAT_TAC);;

let every_refv_mono = prove
 (`(!x. P x ==> P' x) ==> every_refv P v ==> every_refv P' v`,
  CHEAT_TAC);;

let wfv_state_subg = prove
 (`wfv_state g l code s /\ code SUBMAP code2 /\ subg g g2 /\ l SUBSET l2
  ==>
       wfv_state g2 l2 code2 s`,
  CHEAT_TAC);;

let wfv_state_SUBMAP = prove
 (`!g1 l1 code s code1.
        wfv_state g1 l1 code s /\ code SUBMAP code1 ==>
       wfv_state g1 l1 code1 s`,
  CHEAT_TAC);;

let v_rel_SUBMAP = prove
 (`!g1 l1 code v1 v2 code1.
      clos_callProof_v_rel g1 l1 code v1 v2 /\ code SUBMAP code1
        ==> clos_callProof_v_rel g1 l1 code1 v1 v2`,
  CHEAT_TAC);;

let v_rel_SUBMAP_subg = prove
 (`clos_callProof_v_rel g l code v1 v2 /\ code SUBMAP code' /\ l SUBSET
  l' /\ subg g g' ==>
     clos_callProof_v_rel g' l' code' v1 v2`,
  CHEAT_TAC);;

let LIST_REL_v_rel_SUBMAP = prove
 (`!g1 l1 code v1 v2 code1.
       ALL2 (clos_callProof_v_rel g1 l1 code) v1 v2 /\ code SUBMAP
         code1 ==>
       ALL2 (clos_callProof_v_rel g1 l1 code1) v1 v2`,
  CHEAT_TAC);;

let LIST_REL_v_rel_subg = prove
 (`ALL2 (clos_callProof_v_rel g l code) xs ys /\ subg g g2 /\ l SUBSET
  l2 /\ code SUBMAP code2 ==> ALL2 (clos_callProof_v_rel g2 l2 code2)
  xs ys`,
  CHEAT_TAC);;

let env_rel_SUBMAP = prove
 (`!code code' g1 l1 env1 env2 n vars'.
       clos_callProof_env_rel (clos_callProof_v_rel g1 l1 code) env1
         env2 n vars' /\ code SUBMAP code' ==>
       clos_callProof_env_rel (clos_callProof_v_rel g1 l1 code')
         env1 env2 n vars'`,
  CHEAT_TAC);;

let env_rel_subg = prove
 (`clos_callProof_env_rel (clos_callProof_v_rel g l code) env1 env2 n
  vars /\ subg g g2 /\ l SUBSET l2 /\
     code SUBMAP code2 ==>
   clos_callProof_env_rel (clos_callProof_v_rel g2 l2 code2) env1
     env2 n vars`,
  CHEAT_TAC);;

(* semantic functions respect relation *)

(* v_rel_Unit[simp] *)
let clos_callProof_v_rel_Unit = prove
 (`clos_callProof_v_rel g1 l1 code closSem_Unit closSem_Unit`,
  CHEAT_TAC);;

let v_to_list_thm = prove
 (`!h h' x.
      closSem_v_to_list h = SOME x /\ clos_callProof_v_rel g1 l1 code
        h h' ==>
      (?x'. closSem_v_to_list h' = SOME x' /\ ALL2
        (clos_callProof_v_rel g1 l1 code) x x')`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_IMP_v_to_bytes_lemma = prove
 (`!x y c g code.
     clos_callProof_v_rel c g code x y ==>
     (!ns. (closSem_v_to_list x = SOME (MAP (closSem_Number o (&) o
       (w2n:word8->num)) ns)) <=>
          (closSem_v_to_list y = SOME (MAP (closSem_Number o (&) o
            (w2n:word8->num)) ns)))`,
  CHEAT_TAC);;

(* [local] *)
let v_rel_IMP_v_to_words_lemma = prove
 (`!x y c g.
     clos_callProof_v_rel c g code x y ==>
     (!ns. (closSem_v_to_list x = SOME (MAP closSem_Word64 ns)) <=>
          (closSem_v_to_list y = SOME (MAP closSem_Word64 ns)))`,
  CHEAT_TAC);;

let v_to_bytes_thm = prove
 (`!h h' x.
      closSem_v_to_bytes h = SOME x /\ clos_callProof_v_rel g1 l1
        code h h' ==>
      closSem_v_to_bytes h' = SOME x`,
  CHEAT_TAC);;

let v_to_words_thm = prove
 (`!h h' x.
      closSem_v_to_words h = SOME x /\ clos_callProof_v_rel g1 l1
        code h h' ==>
      closSem_v_to_words h' = SOME x`,
  CHEAT_TAC);;

let v_to_list_wfv = prove
 (`!h x. closSem_v_to_list h = SOME x /\ wfv g1 l1 code h ==> ALL (wfv
  g1 l1 code) x`,
  CHEAT_TAC);;

let wfv_Boolv = prove
 (`wfv g1 l1 code (closSem_Boolv b) /\ wfv g1 l1 code closSem_Unit`,
  CHEAT_TAC);;

let vrel_list_to_v = prove
 (`!xs1 xs2 ys1 ys2.
     ALL2 (clos_callProof_v_rel g l code) xs1 xs2 /\
     ALL2 (clos_callProof_v_rel g l code) ys1 ys2 /\
     clos_callProof_v_rel g l code (closSem_list_to_v xs1)
       (closSem_list_to_v xs2) /\
     clos_callProof_v_rel g l code (closSem_list_to_v ys1)
       (closSem_list_to_v ys2) ==>
       clos_callProof_v_rel g l code (closSem_list_to_v (APPEND xs1
         ys1)) (closSem_list_to_v (APPEND xs2 ys2))`,
  CHEAT_TAC);;

let vrel_v2l_l2v = prove
 (`!x y xs ys.
     clos_callProof_v_rel g l code x y /\
     closSem_v_to_list x = SOME xs /\
     closSem_v_to_list y = SOME ys ==>
       clos_callProof_v_rel g l code (closSem_list_to_v xs)
         (closSem_list_to_v ys)`,
  CHEAT_TAC);;

let wfv_v2l_l2v = prove
 (`!x y xs ys. wfv g l code x /\ closSem_v_to_list x = SOME xs ==>
               wfv g l code (closSem_list_to_v xs)`,
  CHEAT_TAC);;

let wfv_v2l = prove
 (`!x y xs ys.
   wfv g l code x /\ wfv g l code y /\
   closSem_v_to_list x = SOME xs /\ closSem_v_to_list y = SOME ys ==>
     (?z. wfv g l code z /\ closSem_v_to_list z = SOME (APPEND xs
       ys))`,
  CHEAT_TAC);;

(* do_app_thm *)
let clos_callProof_do_app_thm = prove
 (`match closSem_do_app op (REVERSE a) (r:(1 spt#'c,'ffi)closSem_state)
  with
      Rerr (Rraise _28) -> F | Rerr (Rabort e) ->
      (e = Rtype_error \/
       (?f.
            e = Rffi_error f /\ (
            ALL2 (clos_callProof_v_rel g2 l2 (closSem_state_code t))
              a v /\ clos_callProof_state_rel g2 l2 r t ==>
              closSem_do_app op (REVERSE v) t = Rerr (Rabort (Rffi_error
              f))))) | Rval (w,s) ->
       (wfv_state g2 l2 (closSem_state_code t) r /\ ALL (wfv g2 l2
         (closSem_state_code t)) a ==>
        wfv_state g2 l2 (closSem_state_code t) s /\ wfv g2 l2
          (closSem_state_code t) w) /\
       (ALL2 (clos_callProof_v_rel g2 l2 (closSem_state_code t)) a v
         /\ clos_callProof_state_rel g2 l2 r t ==>
        (?w' s'. (closSem_do_app op (REVERSE v) t = Rval (w',s')) /\
                clos_callProof_v_rel g2 l2 (closSem_state_code t) w
                  w' /\ clos_callProof_state_rel g2 l2 s s'))`,
  CHEAT_TAC);;

let NOT_IN_domain_FST_g = prove
 (`ALL_DISTINCT (APPEND (code_locs xs) (code_locs ys)) ==>
    calls ys g' = (e2,g) ==>
    wfg g' ==>
    MEM x (code_locs xs) ==> ~(x IN domain (FST g')) ==> ~(x IN
      domain (FST g))`,
  CHEAT_TAC);;

(* v_rel_Boolv[simp] *)
let clos_callProof_v_rel_Boolv = prove
 (`clos_callProof_v_rel g1 l1 code (closSem_Boolv b) v <=> (v =
  closSem_Boolv b)`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_Op_Install = prove
 (`clos_callProof_env_rel r env env2 0 [0,(closLang_Op v6
  closLang_Install e1:closLang_exp)] <=>
   clos_callProof_env_rel r env env2 0 (MAP (\x. (0,x)) e1)`,
  CHEAT_TAC);;

let syntax_ok_def = new_definition
  `clos_callProof_syntax_ok x <=> every_Fn_SOME x /\ every_Fn_vs_NONE
  x /\ ALL_DISTINCT (code_locs x)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let co_ok_def,co_ok_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). (\n. n) x3)`
  [`co_ok code co full_gs k <=>
     (if k = 0 then T else
       let g = FST (FST (co 0)) in
       let (cfg,exp,aux) = co 0 in
       let (g',exp',aux1) = clos_call_compile_inc g (exp,aux) in
         FST (FST (co 1)) = g' /\
         make_g g code = SOME (full_gs 0) /\
         (!i. subg (full_gs 0) (full_gs i)) /\
         (!x i. MEM x (code_locs exp) /\ ~(x IN domain g') ==> ~(x
           IN domain (FST (FST (co i))))) /\
         DISJOINT (set_of_list (code_locs exp)) (domain g) /\
         DISJOINT (FDOM code) (set_of_list (MAP FST aux1)) /\
         ALL_DISTINCT (MAP FST aux1) /\
         co_ok (code |++ aux1) (misc_shift_seq 1 co)
           (misc_shift_seq 1 full_gs) (k - 1))`];;

let co_ok_IMP_full_gs_eq_shift_seq = prove
 (`!k code co g full_gs.
      co_ok code co full_gs (k + 1) ==>
      FST (FST (misc_shift_seq k co 0)) = FST (full_gs k)`,
  CHEAT_TAC);;

let co_ok_IMP_wfg_full_gs = prove
 (`!k code co g full_gs. co_ok code co full_gs (k + 1) ==> wfg
  (full_gs k)`,
  CHEAT_TAC);;

let co_ok_IMP_make_g = prove
 (`!k code co g full_gs.
      co_ok code co full_gs (k + 1) ==>
      (?x1 x2. make_g x1 x2 = SOME (full_gs k))`,
  CHEAT_TAC);;

let code_inv_def = new_definition
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

let code_inv_k = prove
 (`!k. code_inv g l s_code s_cc s_co t_code t_cc t_co ==>
   (match s_co k with (cfg,exp,aux) -> clos_callProof_syntax_ok exp
     /\ aux = [])`,
  CHEAT_TAC);;

(* HOL4 clos_callProofScript.sml:2113-2120: code that the source has
   in a comment *)

let SUBMAP_FUPDATE_LIST = prove
 (`!f xs. ALL_DISTINCT (MAP FST xs) /\ DISJOINT (FDOM f) (set_of_list
  (MAP FST xs)) ==> f SUBMAP (f |++ xs)`,
  CHEAT_TAC);;

let includes_state_def = new_definition
  `includes_state g1 s_compile_oracle <=>
     (?(k:num). FST (FST (s_compile_oracle k)) = FST g1)`;;

let includes_state_EX = prove
 (`includes_state g1 s_co ==>
     (?k cfg2 exps aux. s_co k = ((FST g1,cfg2),exps,aux))`,
  CHEAT_TAC);;

(* HOL4 clos_callProofScript.sml:2145-2151: code that the source has
   in a comment *)

let code_rel_state_rel_install = prove
 (`code_inv (SOME g1) l1 (closSem_state_code
       r) (closSem_state_compile r) (closSem_state_compile_oracle r)
         (closSem_state_code t) (closSem_state_compile t)
         (closSem_state_compile_oracle t) /\
     clos_callProof_state_rel g1 l1 r t /\ closSem_state_compile
     r cfg (exps,aux) =
         SOME (bytes,data,next_cfg) /\ closSem_state_compile_oracle
     r 0 = (cfg,exps,aux) /\ closSem_state_compile_oracle
     t 0 = (cfg',progs) /\
     next_cfg = FST (misc_shift_seq 1 (closSem_state_compile_oracle
       r) 0) /\
     DISJOINT l1 (domain (FST g1)) ==>
     DISJOINT (FDOM (closSem_state_code t)) (set_of_list (MAP FST
       (SND progs))) /\
     ALL_DISTINCT (MAP FST (SND progs)) /\
     (?exp1 aux1 g2 l2 next_cfg'. closSem_state_compile
     t cfg' progs = SOME (bytes,data,next_cfg') /\
       progs = (exp1,aux1) /\
       next_cfg' = FST (misc_shift_seq 1
         (closSem_state_compile_oracle t) 0) /\
       subg g1 g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain (FST g2)) /\
       set_of_list (code_locs exps) DIFF domain (FST g2) SUBSET l2 /\
       calls exps g1 = (exp1,g2) /\
       clos_callProof_state_rel g2 l2
        (closSem_state_code_fupd (K (closSem_state_code r |++ aux))
          (closSem_state_compile_oracle_fupd (K (misc_shift_seq 1
          (closSem_state_compile_oracle r))) r))
        (closSem_state_code_fupd (K (closSem_state_code t |++ aux1))
          (closSem_state_compile_oracle_fupd (K (misc_shift_seq 1
          (closSem_state_compile_oracle t))) t)) /\
       code_inv (SOME g2) l2 (closSem_state_code r |++ aux)
         (closSem_state_compile r) (misc_shift_seq 1
         (closSem_state_compile_oracle r))
                (closSem_state_code t |++ aux1)
                  (closSem_state_compile t) (misc_shift_seq 1
                  (closSem_state_compile_oracle t)) /\
                  closSem_state_code
       t SUBMAP (closSem_state_code t |++ aux1) /\
       DISJOINT (IMAGE SUC (set_of_list (code_locs exps))) (FDOM
         (closSem_state_code t)))`,
  CHEAT_TAC);;

let fv_GENLIST_Var_alt = prove
 (`!n i tra. fv v (GENLIST_Var tra i n) <=> v < n`,
  CHEAT_TAC);;

let env_rel_env_exists = prove
 (`!vars'. ALL (wfv g1 l1 code) env ==>
           (?env5. clos_callProof_env_rel (clos_callProof_v_rel g1 l1
             code) env env5 0 vars' /\
                  LENGTH env5 = LENGTH env)`,
  CHEAT_TAC);;

let evaluate_includes_state = prove
 (`!xs env s res s1 g1.
      includes_state g1 (closSem_state_compile_oracle s1) /\
      closSem_evaluate (xs,env,s) = (res,s1) ==>
      includes_state g1 (closSem_state_compile_oracle s)`,
  CHEAT_TAC);;

let evaluate_app_includes_state = prove
 (`!xs env s res s1 g1.
      includes_state g1 (closSem_state_compile_oracle s1) /\
      evaluate_app loco x vs s = (res,s1) ==>
      includes_state g1 (closSem_state_compile_oracle s)`,
  CHEAT_TAC);;

let evaluate_app_mono = prove
 (`evaluate_app x y z s1 = (vs,s2) ==> closSem_state_code s1 SUBMAP
  closSem_state_code s2`,
  CHEAT_TAC);;

let calls_pure = prove
 (`!xs g es g1.
    ALL pure xs /\ calls xs g = (es,g1) ==> ALL pure es`,
  CHEAT_TAC);;

let calls_pure_sing = prove
 (`pure x1 /\ calls [x1] g = ([e1],g1) ==> pure e1`,
  CHEAT_TAC);;

(* HOL4 clos_callProofScript.sml:2331-2381: code that the source has
   in a comment *)

let wfg_subg_refl = prove
 (`wfg g ==> subg g g`,
  CHEAT_TAC);;

let wfg_subg_EX_helper = prove
 (`wfg g /\ P g ==> (?g2. subg g g2 /\ P g2)`,
  CHEAT_TAC);;

let mk_code_g_def = new_definition
  `mk_code_g code = (list_to_num_set (MAP PRE (SET_TO_LIST (FDOM
  code))),
     fmap_to_alist code)`;;

(* HOL4 clos_callProofScript.sml:2400-2402: ML code, not ported *)

(* HOL4 clos_callProofScript.sml:2404-2405: ML code, not ported *)

let pure_correct_eq = prove
 (`pure e /\ closSem_evaluate ([e],env,s) = (res,s') ==>
     (match res with Rval vs -> s' = s /\ LENGTH vs = 1 | Rerr
       (Rraise _29) -> F | Rerr (Rabort a) -> a = Rtype_error)`,
  CHEAT_TAC);;

(* state_rel_opt_rel_refs[local] *)
let clos_callProof_state_rel_opt_rel_refs = prove
 (`(clos_callProof_state_rel g l s1 s2 /\ FLOOKUP (state_refs s1) n = r1
  ==>
      (?r2. FLOOKUP (state_refs s2) n = r2 /\
           OPTREL (closProps_ref_rel (clos_callProof_v_rel g l
             (closSem_state_code s2))) r1 r2)) /\
   (clos_callProof_state_rel g l s1 s2 /\ FLOOKUP (state_refs s2) n =
     r2 ==>
      (?r1. FLOOKUP (state_refs s1) n = r1 /\
           OPTREL (closProps_ref_rel (clos_callProof_v_rel g l
             (closSem_state_code s2))) r1 r2))`,
  CHEAT_TAC);;

(* compiler correctness *)

(* HOL4 clos_callProofScript.sml:2429: the ML values that the
   definitions below antiquote *)

(*
max_print_depth := 8
max_print_depth := 80
max_print_depth := 800
*)

(* HOL4 clos_callProofScript.sml:2437-2438: ML code, not ported *)

let calls_correct = prove
 (`(!tmp xs env1 s0 g0 g env2 (t0:('c,'ffi)closSem_state) ys res s l l1
  g1.
     tmp = (xs,env1,s0) /\
     closSem_evaluate (xs,env1,s0) = (res,s) /\ ~(res = Rerr (Rabort
       Rtype_error)) /\
     calls xs g0 = (ys,g) /\
     code_inv (SOME g1) l1 (closSem_state_code s0)
       (closSem_state_compile s0) (closSem_state_compile_oracle s0)
       (closSem_state_code
                           t0) (closSem_state_compile t0)
                             (closSem_state_compile_oracle t0) /\
     every_Fn_SOME xs /\ every_Fn_vs_NONE xs /\
     ALL (wfv g1 l1 (closSem_state_code t0)) env1 /\ wfv_state g1 l1
       (closSem_state_code t0) s0 /\ wfg g0 /\
     ALL_DISTINCT (code_locs xs) /\
     DISJOINT (IMAGE SUC (set_of_list (code_locs xs))) (set_of_list
       (MAP FST (SND g0))) /\
     l = set_of_list (code_locs xs) DIFF domain (FST g) /\
     subg g g1 /\ l SUBSET l1 /\ DISJOINT l1 (domain (FST g1)) /\ wfg
       g1 /\
     clos_callProof_env_rel (clos_callProof_v_rel g1 l1
       (closSem_state_code t0)) env1 env2 0 (MAP (\x. (0,x)) ys) /\
     clos_callProof_state_rel g1 l1 s0 t0 /\ code_includes (SND g)
       (closSem_state_code t0) ==>
     (?ck res' t g2 l2.
       code_inv (SOME g2) l2 (closSem_state_code s)
         (closSem_state_compile s) (closSem_state_compile_oracle s)
         (closSem_state_code
                             t) (closSem_state_compile t)
                               (closSem_state_compile_oracle t) /\
       wfv_state g2 l2 (closSem_state_code t) s /\
       subg g1 g2 /\ wfg g2 /\ l1 SUBSET l2 /\ DISJOINT l2 (domain
         (FST g2)) /\
       every_result (ALL (wfv g2 l2 (closSem_state_code t))) (wfv g2
         l2 (closSem_state_code t)) res /\
       closSem_evaluate (ys,env2,closSem_state_clock_fupd (K
         (closSem_state_clock t0 + ck)) t0) = (res',t) /\
       clos_callProof_state_rel g2 l2 s t /\
       semanticPrimitivesProps_result_rel (ALL2 (clos_callProof_v_rel
         g2 l2 (closSem_state_code t))) (clos_callProof_v_rel g2 l2
         (closSem_state_code t)) res res')) /\
   (!loco f args s0 loc g l (t0:('c,'ffi)closSem_state) res s f'
     args'.
     evaluate_app loco f args s0 = (res,s) /\ ~(res = Rerr (Rabort
       Rtype_error)) /\
     code_inv (SOME g) l (closSem_state_code s0)
       (closSem_state_compile s0) (closSem_state_compile_oracle s0)
       (closSem_state_code
                         t0) (closSem_state_compile t0)
                           (closSem_state_compile_oracle t0) /\
     wfv g l (closSem_state_code t0) f /\ ALL (wfv g l
       (closSem_state_code t0)) args /\
     wfv_state g l (closSem_state_code t0) s0 /\
     wfg g /\ DISJOINT l (domain (FST g)) /\
     clos_callProof_v_rel g l (closSem_state_code t0) f f' /\ ALL2
       (clos_callProof_v_rel g l (closSem_state_code t0)) args args' /\
     clos_callProof_state_rel g l s0 t0 ==>
     (?ck res' t g2 l2.
       code_inv (SOME g2) l2 (closSem_state_code s)
         (closSem_state_compile s) (closSem_state_compile_oracle s)
         (closSem_state_code
                             t) (closSem_state_compile t)
                               (closSem_state_compile_oracle t) /\
       wfv_state g2 l2 (closSem_state_code t) s /\
       every_result (ALL (wfv g2 l2 (closSem_state_code t))) (wfv g2
         l2 (closSem_state_code t)) res /\
       evaluate_app loco f' args' (closSem_state_clock_fupd (K
         (closSem_state_clock t0 + ck)) t0) = (res',t) /\
       clos_callProof_state_rel g2 l2 s t /\
       subg g g2 /\ wfg g2 /\ l SUBSET l2 /\ DISJOINT l2 (domain (FST
         g2)) /\
       semanticPrimitivesProps_result_rel (ALL2
         (clos_callProof_v_rel g2 l2 (closSem_state_code t)))
         (clos_callProof_v_rel g2 l2 (closSem_state_code t)) res
         res'))`,
  CHEAT_TAC);;

(* [local] *)
let code_locs_calls_list = prove
 (`!ls n tr i. code_locs (MAP SND (calls_list tr i n ls)) = []`,
  CHEAT_TAC);;

(* [local] *)
let code_locs_code_list_MEM = prove
 (`!ls n rest x.
   MEM x (code_locs (MAP (SND o SND) (SND (code_list n ls rest))))
     <=>
   MEM x (code_locs (APPEND (MAP (SND o SND) (SND rest)) (MAP SND
     ls)))`,
  CHEAT_TAC);;

(* [local] *)
let code_locs_code_list_ALL_DISTINCT = prove
 (`!ls n rest.
   ALL_DISTINCT (code_locs (MAP (SND o SND) (SND (code_list n ls
     rest)))) <=>
   ALL_DISTINCT (code_locs (APPEND (MAP (SND o SND) (SND rest))
     (MAP SND ls)))`,
  CHEAT_TAC);;

(* All code_locs come from the original code,
   and therefore, are all even
*)
let calls_code_locs_MEM = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
   (!x.
    (MEM x (code_locs ys) \/
    MEM x (code_locs (MAP (SND o SND) (SND g)))) ==>
    (MEM x (code_locs xs) \/
    MEM x (code_locs (MAP (SND o SND) (SND g0)))))`,
  CHEAT_TAC);;

(* the all distinctness of code_locs is preserved *)
let calls_code_locs_ALL_DISTINCT = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
    ALL_DISTINCT (APPEND (code_locs xs) (code_locs (MAP (SND o SND)
      (SND g0)))) ==>
    ALL_DISTINCT (APPEND (code_locs ys) (code_locs (MAP (SND o SND)
      (SND g))))`,
  CHEAT_TAC);;

let oracle_monotonic_init_UNION = prove
 (`oracle_monotonic f R (A UNION B) co <=>
     oracle_monotonic f R A co /\ oracle_monotonic f R B co`,
  CHEAT_TAC);;

let semantics_calls = prove
 (`~(closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY co cc x =
  ffi_Fail) ==>
      clos_call_compile T x = (y,g0,aux) /\ every_Fn_SOME x /\
        every_Fn_vs_NONE x /\
      ALL_DISTINCT (code_locs x) /\
      FST (FST (co 0)) = g0 /\
      code_inv NONE (set_of_list (code_locs x)) FEMPTY cc co (FEMPTY
        |++ aux) cc1 co1 ==>
      closSem_semantics (ffi:'ffi ffi_state) max_app (FEMPTY |++ aux)
        co1 cc1 y =
      closSem_semantics (ffi:'ffi ffi_state) max_app FEMPTY co cc x`,
  CHEAT_TAC);;

let semantics_compile = prove
 (`~(closSem_semantics ffi max_app FEMPTY co cc x = ffi_Fail) /\
      clos_call_compile do_call x = (y,g1,aux) /\
      (if do_call then
       clos_callProof_syntax_ok x /\ g1 = FST (FST (co 0)) /\
       code_inv NONE (set_of_list (code_locs x)) FEMPTY cc co (FEMPTY
         |++ aux) cc1 co1 else cc = state_cc (CURRY I) cc1 /\
            co1 = state_co (CURRY I) co) ==>
      closSem_semantics ffi max_app (FEMPTY |++ aux) co1 cc1 y =
      closSem_semantics ffi max_app FEMPTY co cc x`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let nth_code_def,nth_code_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x2)`
  [`clos_callProof_nth_code code co 0 = code`;
   `clos_callProof_nth_code code co (SUC k) =
      (let (cfg,exp,aux) = co 0 in
      let (g',exp',aux') = clos_call_compile_inc (FST cfg) (exp,aux)
        in
        clos_callProof_nth_code (code |++ aux') (misc_shift_seq
          1 co) k)`];;

(* TODO: move *)
let FUNION_FEMPTY_FUPDATE_LIST = prove
 (`DISJOINT (FDOM code) (set_of_list (MAP FST aux)) ==>
    FUNION code (FEMPTY |++ aux) = code |++ aux`,
  CHEAT_TAC);;

(* Preservation of some label properties
  every_Fn_SOME xs ∧ every_Fn_vs_NONE xs
*)
let every_Fn_GENLIST_Var = prove
 (`!n i t. every_Fn_SOME (GENLIST_Var t i n) /\
       every_Fn_vs_NONE (GENLIST_Var t i n)`,
  CHEAT_TAC);;

let every_Fn_calls_list = prove
 (`!ls n i t. every_Fn_SOME (MAP SND (calls_list t i n ls)) /\
         every_Fn_vs_NONE (MAP SND (calls_list t i n ls))`,
  CHEAT_TAC);;

let every_Fn_code_list = prove
 (`!ls n rest.
   (every_Fn_SOME (MAP (SND o SND) (SND (code_list n ls rest))) <=>
   every_Fn_SOME (MAP SND ls) /\
   every_Fn_SOME (MAP (SND o SND) (SND rest))) /\
   (every_Fn_vs_NONE (MAP (SND o SND) (SND (code_list n ls rest)))
     <=>
   every_Fn_vs_NONE (MAP SND ls) /\
   every_Fn_vs_NONE (MAP (SND o SND) (SND rest)))`,
  CHEAT_TAC);;

let calls_preserves_every_Fn_SOME = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
    every_Fn_SOME xs /\ every_Fn_SOME (MAP (SND o SND) (SND g0)) ==>
    every_Fn_SOME ys /\ every_Fn_SOME (MAP (SND o SND) (SND g))`,
  CHEAT_TAC);;

let calls_preserves_every_Fn_vs_NONE = prove
 (`!xs g0 ys g. calls xs g0 = (ys,g) ==>
    every_Fn_vs_NONE xs /\ every_Fn_vs_NONE (MAP (SND o SND) (SND
      g0)) ==>
    every_Fn_vs_NONE ys /\ every_Fn_vs_NONE (MAP (SND o SND) (SND
      g))`,
  CHEAT_TAC);;

(* HOL4 clos_callProofScript.sml:4672-4684: code that the source has
   in a comment *)

(* obeys_max_app and no_Labels *)

let state_syntax_def = new_definition
  `state_syntax f ((g,xs):1 spt#(num#num#closLang_exp) list) = ALL
  (\(x1,x2,x3). f x3) xs`;;

let state_syntax_insert_each = prove
 (`!k1 loc g.
      state_syntax f (insert_each loc k1 g) = state_syntax f g`,
  CHEAT_TAC);;

let state_syntax_code_list = prove
 (`!n xs g.
      state_syntax f (code_list n xs g) <=>
      state_syntax f g /\ ALL f (MAP SND xs)`,
  CHEAT_TAC);;

let obeys_max_app_GENLIST_Var = prove
 (`!n l w. ALL (obeys_max_app k) (GENLIST_Var n l w)`,
  CHEAT_TAC);;

let obeys_max_app_calls_list = prove
 (`!t k1 loc fns. ALL (obeys_max_app k) (MAP SND (calls_list t k1 loc
  fns))`,
  CHEAT_TAC);;

let calls_obeys_max_app = prove
 (`!xs g ys g1.
      calls xs g = (ys,g1) /\ state_syntax (obeys_max_app k) g /\
      ALL (obeys_max_app k) xs ==>
      ALL (obeys_max_app k) ys /\ state_syntax (obeys_max_app k) g1`,
  CHEAT_TAC);;

let no_Labels_GENLIST_Var = prove
 (`!n l w. ALL no_Labels (GENLIST_Var n l w)`,
  CHEAT_TAC);;

let no_Labels_calls_list = prove
 (`!t k1 loc fns. ALL no_Labels (MAP SND (calls_list t k1 loc fns))`,
  CHEAT_TAC);;

let calls_no_Labels = prove
 (`!xs g ys g1.
      calls xs g = (ys,g1) /\ state_syntax no_Labels g /\
      ALL no_Labels xs ==>
      ALL no_Labels ys /\ state_syntax no_Labels g1`,
  CHEAT_TAC);;

(* names *)

(* HOL4 clos_callProofScript.sml:4766-4909: code that the source has
   in a comment *)

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "vars"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
