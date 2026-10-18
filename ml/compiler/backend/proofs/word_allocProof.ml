(* ======================================================== *)
(*  word_allocProof: ported from HOL4's
    compiler/backend/proofs/word_allocProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_alloc
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/reg_alloc/linear_scan.ml";;
needs "compiler/backend/reg_alloc/proofs/linear_scanProof.ml";;
needs "compiler/backend/reg_alloc/proofs/reg_allocProof.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_alloc.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* Ensures we have the correct ML bindings *)
(* HOL4 word_allocProofScript.sml:13-15: ML code, not ported *)

(*TODO: Move?*)
(* TODO: can we have a global for this *)
let hide_def = cake_define
  `word_allocProof_hide x = x`;;
hol4_overload "hide" "word_allocProof_hide";;

(* word_alloc proofs
  1. correctness theorem about colouring_ok
  2. get_clash_sets (TODO: redundant)
  3. connect check_clash_tree to colouring_ok
  4. word_alloc_correct (connect 1 and 3)
  5. ssa_cc_trans correctness proof (including an invariant property),
    followed by full_ssa_cc_trans correctness
  6. ssa syntactic things (pre_alloc_conventions, wf_cutsets)
  7. word_alloc syntactic things
  8. misc
 *)

(* colouring_ok correctness proof *)
let colouring_ok_def = cake_define
  `colouring_ok f prog live lt =
        match prog with
          wordLang_Seq s1 s2 ->
       (let s2_live = get_live s2 live lt in
       let s1_live = get_live s1 s2_live lt in
         INJ f (domain s1_live) UNIV /\
         colouring_ok f s2 live lt /\ colouring_ok f s1 s2_live lt)
        | (If cmp r1 ri e2 e3) ->
       (let e2_live = get_live e2 live lt in
       let e3_live = get_live e3 live lt in
       let union_live = sptree_union e2_live e3_live in
       let merged = (match ri with Reg r2 -> sptree_insert r2 one
         (sptree_insert r1 one union_live) | _1 -> sptree_insert r1 one
         union_live) in
         INJ f (domain merged) UNIV /\
         colouring_ok f e2 live lt /\ colouring_ok f e3 live lt)
        | (Call (SOME (v,cutset,ret_handler,l1,l2)) dest args h) ->
       (let args_set = numset_list_insert args LN in
       let all_names' = sptree_union (SND cutset) (FST cutset) in
       INJ f (domain (sptree_union all_names' args_set)) UNIV /\
       INJ f (domain (numset_list_insert v all_names')) UNIV /\
       colouring_ok f ret_handler live lt /\
       (match h with NONE -> T | SOME (v,prog,l1,l2) ->
           INJ f (domain (sptree_insert v one all_names')) UNIV /\
           colouring_ok f prog live lt))
        | (wordLang_MustTerminate p) ->
       colouring_ok f p live lt
        | (Loop names body exit_names) ->
       (INJ f (domain names) UNIV /\
       INJ f (domain exit_names) UNIV /\
       colouring_ok f body names ((names,exit_names) :: lt))
        | prog ->
       (let lset = get_live prog live lt in
       let iset = sptree_union (get_writes prog) live in
         INJ f (domain lset) UNIV /\ INJ f (domain iset) UNIV)`;;

(*Equivalence on everything except permutation and locals*)
(* should we add local_size here? may be no, as locals are not included
   *)
(*TODO this definition is bad for automation remove it with
t = s with (...)*)
let word_state_eq_rel_def = cake_define
  `word_state_eq_rel (s:('a,'c,'ffi)wordSem_state)
  (t:('a,'c,'ffi)wordSem_state) <=> wordSem_state_fp_regs
   t = wordSem_state_fp_regs s /\ wordSem_state_store
   t = wordSem_state_store s /\ wordSem_state_locals_size
   t = wordSem_state_locals_size s /\ stack
   t = stack s /\ wordSem_state_stack_limit
   t = wordSem_state_stack_limit s /\ wordSem_state_stack_max
   t = wordSem_state_stack_max s /\ wordSem_state_stack_size
   t = wordSem_state_stack_size s /\ wordSem_state_memory
   t = wordSem_state_memory s /\ wordSem_state_mdomain
   t = wordSem_state_mdomain s /\ wordSem_state_sh_mdomain
   t = wordSem_state_sh_mdomain s /\ wordSem_state_gc_fun
   t = wordSem_state_gc_fun s /\ wordSem_state_handler
   t = wordSem_state_handler s /\ state_clock
   t = state_clock s /\ wordSem_state_code
   t = wordSem_state_code s /\ state_ffi
   t = state_ffi s /\ wordSem_state_be
   t = wordSem_state_be s /\ wordSem_state_termdep
   t = wordSem_state_termdep s /\ wordSem_state_compile
   t = wordSem_state_compile s /\ wordSem_state_compile_oracle
   t = wordSem_state_compile_oracle s /\ wordSem_state_code_buffer
   t = wordSem_state_code_buffer s /\ wordSem_state_data_buffer
   t = wordSem_state_data_buffer s`;;


(*tlocs is a supermap of slocs under f for everything in a given
  live set*)

let strong_locals_rel_def = cake_define
  `strong_locals_rel f ls slocs tlocs <=>
   (!n v.
     n IN ls /\ sptree_lookup n slocs = SOME v ==>
     sptree_lookup (f n) tlocs = SOME v)`;;

(* HOL4 word_allocProofScript.sml:265: ML code, not ported *)

(*For any 2 lists that are permutations of each other,
  We can give a list_rearranger that permutes one to the other*)

(* HOL4 word_allocProofScript.sml:432: ML code, not ported *)

(*Main theorem for permute oracle usage!
  This shows that we can push locals that are exactly matching using
  any desired permutation
  and we can choose the final permutation to be anything we want
  (In Alloc we choose it to be cst.permute, in Call something
   given by the IH)
*)

(*Proves s_val_eq and some extra conditions on the resulting lists*)

(*TODO: Maybe move to props?
gc doesn't touch other components*)

(* Convenient rewrite for pop_env
  TODO: do we need more on lsz'?
*)

(*Less powerful form*)

(* HOL4 word_allocProofScript.sml:657: the ML values that the
   definitions below antiquote *)

(*Main proof of liveness theorem starts here*)
(* HOL4 word_allocProofScript.sml:734-742: code that the source has
   in a comment *)

(*Frequently used tactics*)
(* HOL4 word_allocProofScript.sml:798-800: a proof *)

(* HOL4 word_allocProofScript.sml:802-809: a proof *)

(* HOL4 word_allocProofScript.sml:811-813: a proof *)

(*liveness theorem*)

(* HOL4 word_allocProofScript.sml:1165-1167: a proof *)

(* HOL4 word_allocProofScript.sml:1169-1193: a proof *)
  (*NONE:
  Therefore n is not in l but it is in live and so it is not deleted
  *)
(* HOL4 word_allocProofScript.sml:1197-1223: a proof *)

(* HOL4 word_allocProofScript.sml:1225-1374: a proof *)
  (* All the FP cases *)
(* HOL4 word_allocProofScript.sml:1376-1394: a proof *)

(* HOL4 word_allocProofScript.sml:1396-1403: a proof *)

(* HOL4 word_allocProofScript.sml:1405-1411: a proof *)

(* HOL4 word_allocProofScript.sml:1413-1419: a proof *)

(* HOL4 word_allocProofScript.sml:1421-1431: a proof *)

(* HOL4 word_allocProofScript.sml:1433-1447: a proof *)

(* HOL4 word_allocProofScript.sml:1449-1480: a proof *)
  (*Returning calls*)
(* HOL4 word_allocProofScript.sml:1482-1592: a proof *)
  (*Result*)
(* HOL4 word_allocProofScript.sml:1594-1608: a proof *)
  (*finally using IH*)
(* HOL4 word_allocProofScript.sml:1610-1629: a proof *)
  (* Strong locals rel *)
(* HOL4 word_allocProofScript.sml:1631-1663: a proof *)
  (*Exception*)
(* HOL4 word_allocProofScript.sml:1665-1673: a proof *)
  (*No handler*)
(* HOL4 word_allocProofScript.sml:1675-1702: a proof *)
  (*Handler*)
(* HOL4 word_allocProofScript.sml:1704-1758: a proof *)
  (*Use IH*)
(* HOL4 word_allocProofScript.sml:1760-1769: a proof *)
  (* Strong locals rel *)
(* HOL4 word_allocProofScript.sml:1771-1799: a proof *)
  (*Remaining Cases*)
(* HOL4 word_allocProofScript.sml:1801-1809: a proof *)

(* HOL4 word_allocProofScript.sml:1811-1831: a proof *)

(* HOL4 word_allocProofScript.sml:1833-1881: a proof *)

(* HOL4 word_allocProofScript.sml:1883-1892: a proof *)

(* HOL4 word_allocProofScript.sml:1894-1976: a proof *)
      (* Strong locals rel *)
(* HOL4 word_allocProofScript.sml:1978-2022: a proof *)

(* HOL4 word_allocProofScript.sml:2024-2060: a proof *)

(* HOL4 word_allocProofScript.sml:2062-2067: a proof *)

(* HOL4 word_allocProofScript.sml:2069-2084: a proof *)

(* HOL4 word_allocProofScript.sml:2086-2090: a proof *)

(* HOL4 word_allocProofScript.sml:2092-2096: a proof *)

(* HOL4 word_allocProofScript.sml:2098-2100: a proof *)

(* HOL4 word_allocProofScript.sml:2102-2117: a proof *)

(* HOL4 word_allocProofScript.sml:2119-2131: a proof *)

(* HOL4 word_allocProofScript.sml:2133-2162: a proof *)

(* HOL4 word_allocProofScript.sml:2164-2171: a proof *)

(* HOL4 word_allocProofScript.sml:2173-2180: a proof *)

(* HOL4 word_allocProofScript.sml:2182-2205: a proof *)

(* HOL4 word_allocProofScript.sml:2207-2266: a proof *)

(* HOL4 word_allocProofScript.sml:2268: a proof *)

(* TODO: get_clash_sets, made redundant by clash tree *)

(* HOL4 word_allocProofScript.sml:2272-2383: code that the source has
   in a comment *)

(* HOL4 word_allocProofScript.sml:2398-2589: code that the source has
   in a comment *)

(* Proofs for check_clash_tree *)

(*TODO: This is true without wf*)

(* HOL4 word_allocProofScript.sml:2791-2799: a proof *)

(* HOL4 word_allocProofScript.sml:2801-2804: a proof *)

(* HOL4 word_allocProofScript.sml:3270-3279: a proof *)

(* HOL4 word_allocProofScript.sml:3281-3289: a proof *)

(* HOL4 word_allocProofScript.sml:3291-3299: a proof *)

(* HOL4 word_allocProofScript.sml:3301: a proof *)

(*Actually, it should probably be exactly 0,2,4,6...*)
let even_starting_locals_def = cake_define
  `even_starting_locals (locs:('a word_loc) spt) <=>
     (!x. x IN domain locs ==> is_phy_var x)`;;

(* HOL4 word_allocProofScript.sml:3309: ML code, not ported *)

(*Prove the full correctness theorem for word_alloc*)

(* Dead code removal *)
let live_store_rel_def = cake_define
  `live_store_rel nlive sstore tstore <=>
   (!n. ~(
     n IN set_of_list nlive) ==>
     FLOOKUP sstore n = FLOOKUP tstore n)`;;

let nlive_store_def = cake_define
  `nlive_store nlive x2 =
        match x2 with
          wordLang_Op _3 ls ->
         EVERY (nlive_store nlive) ls
        | (wordLang_Lookup s) -> ~(
       s IN set_of_list nlive)
        | (Load e) ->
       nlive_store nlive e
        | (Shift _4 e1 e2) ->
       nlive_store nlive e1 /\ nlive_store nlive e2
        | _5 -> T`;;

(* HOL4 word_allocProofScript.sml:3958-4029: a proof *)

(* HOL4 word_allocProofScript.sml:4031-4071: a proof *)

(* HOL4 word_allocProofScript.sml:4073-4088: a proof *)

(* HOL4 word_allocProofScript.sml:4090-4114: a proof *)

(* HOL4 word_allocProofScript.sml:4116-4121: a proof *)

(* HOL4 word_allocProofScript.sml:4123-4135: a proof *)

(* HOL4 word_allocProofScript.sml:4137-4155: a proof *)

(* HOL4 word_allocProofScript.sml:4157-4168: a proof *)

(* HOL4 word_allocProofScript.sml:4170-4173: a proof *)
  (* Reg: resolve get_var for register operand, then apply IH *)
(* HOL4 word_allocProofScript.sml:4175-4193: a proof *)
  (* Imm: apply IH directly *)
(* HOL4 word_allocProofScript.sml:4195-4210: a proof *)

(* HOL4 word_allocProofScript.sml:4212-4266: a proof *)

(* HOL4 word_allocProofScript.sml:4268-4279: a proof *)

(* HOL4 word_allocProofScript.sml:4281-4289: a proof *)

(* HOL4 word_allocProofScript.sml:4291-4294: a proof *)

(* HOL4 word_allocProofScript.sml:4296-4299: a proof *)

(* HOL4 word_allocProofScript.sml:4301-4318: a proof *)

(* HOL4 word_allocProofScript.sml:4320-4324: a proof *)

(* HOL4 word_allocProofScript.sml:4326-4332: a proof *)

(* HOL4 word_allocProofScript.sml:4334-4336: a proof *)

(* HOL4 word_allocProofScript.sml:4338-4345: a proof *)

(* HOL4 word_allocProofScript.sml:4347-4350: a proof *)

(* HOL4 word_allocProofScript.sml:4352-4374: a proof *)

(* HOL4 word_allocProofScript.sml:4376-4391: a proof *)

(* HOL4 word_allocProofScript.sml:4393-4408: a proof *)

(* HOL4 word_allocProofScript.sml:4410-4436: a proof *)

(* HOL4 word_allocProofScript.sml:4438-4469: a proof *)

(* HOL4 word_allocProofScript.sml:4471: a proof *)

(*SSA Proof*)

(* HOL4 word_allocProofScript.sml:4506: ML code, not ported *)

(*This might not be the optimal invariant.. because it is very
  restrictive on the ssa_mapping*)
let ssa_locals_rel_def = cake_define
  `ssa_locals_rel na ssa st_locs cst_locs =
   ((!x y. sptree_lookup x ssa = SOME y ==> y IN domain cst_locs) /\
   (!x y. sptree_lookup x st_locs = SOME y ==>
     x IN domain ssa /\
     sptree_lookup (THE (sptree_lookup x ssa)) cst_locs = SOME y /\
     (is_alloc_var x ==> x < na)))`;;

(*ssa_map_ok specifies the form of ssa_maps we care about
  1) The remapped keys are ALL_DISTINCT
  2) The remap keyset is bounded, and no phy vars
*)
let ssa_map_ok_def = cake_define
  `ssa_map_ok na ssa =
   (!x y. sptree_lookup x ssa = SOME y ==>
     ~is_phy_var y /\ y < na)`;;

(* HOL4 word_allocProofScript.sml:4594-4596: a proof *)

(*Characterize result of merge_moves*)

(*Another frame proof about unchanged lookups*)

(*Don't know a neat way to prove this for both sides at once neatly,
Also, the cases are basically copy pasted... *)

(*Swapping lemma that allows us to swap in ssaL for ssaR
  after we are done fixing them*)

(* HOL4 word_allocProofScript.sml:5318-5325: ML code, not ported *)

(* HOL4 word_allocProofScript.sml:5667-5671: a proof *)

(*ordered such that its easy to drule*)

(*ordered such that its easy to drule*)

(*ordered such that its easy to drule*)

(* HOL4 word_allocProofScript.sml:5834-5836: a proof *)

(* HOL4 word_allocProofScript.sml:5857-5860: ML code, not ported *)

(* HOL4 word_allocProofScript.sml:5876: the ML values that the
   definitions below antiquote *)

(* HOL4 word_allocProofScript.sml:5878-5892: ML code, not ported *)

(*ordered such that its easy to drule*)


(*Prove the properties that hold of ssa_cc_trans independent of
   semantics*)

(* HOL4 word_allocProofScript.sml:6177-6200: a proof *)

(* HOL4 word_allocProofScript.sml:6202-6204: a proof *)

(* HOL4 word_allocProofScript.sml:6206-6208: a proof *)

(* HOL4 word_allocProofScript.sml:6210: a proof *)

(* HOL4 word_allocProofScript.sml:6294-6303: a proof *)

(* HOL4 word_allocProofScript.sml:6305-6308: a proof *)
(*TODO move*)

let lt_ok_def = cake_define
  `lt_ok lt <=>
     EVERY (\(tgt_ssa,names,exit_names).
       INJ (option_lookup tgt_ssa) (domain names) UNIV /\
       INJ (option_lookup tgt_ssa) (domain exit_names) UNIV) lt`;;

(* Evaluating a chain of fake_move r writes 0 to each register in rs,
   leaves the rest of state untouched. *)

(* Bundles the (extend, fake_init, refresh) Loop-entry setup.
   Establishes
   ssa_locals_rel under ssa_refreshed and INJ on names/exit_names
     domains
   by construction. *)

(* If P evaluates to (NONE, t), Seq P Q evaluates as Q from t. *)

(* fromAList (MAP f (toAList LN)) behaves like LN in cut_env. *)

(* Helper for Loop iter; target is the INNER Loop (not the full
   translation),
   so the clock-IH recursive call lines up with the inner Loop's
     STOP-recursion
   without re-running the outer fake_prog + refresh_mov setup each iter.
     *)

(* HOL4 word_allocProofScript.sml:7736-7738: a proof *)

(* HOL4 word_allocProofScript.sml:7740-7751: a proof *)
    (* The ssa'' map would have been fine to return without
      forcing the renames too *)
(* HOL4 word_allocProofScript.sml:7754-7823: a proof *)
    (* but we force some new mappings *)
(* HOL4 word_allocProofScript.sml:7825-7858: a proof *)

(* HOL4 word_allocProofScript.sml:7860-7955: a proof *)
        (* is_x64 *)
(* HOL4 word_allocProofScript.sml:7957-7982: a proof *)
(* HOL4 word_allocProofScript.sml:7983-7996: code that the source has
   in a comment *)
(* HOL4 word_allocProofScript.sml:7997-8182: a proof *)
          (* Nasty special case for 32-bit FPMovFromReg *)
(* HOL4 word_allocProofScript.sml:8184-8207: a proof *)
      (* Special case for two writes *)
(* HOL4 word_allocProofScript.sml:8209-8222: a proof *)

(* HOL4 word_allocProofScript.sml:8224-8226: a proof *)

(* HOL4 word_allocProofScript.sml:8228-8230: a proof *)

(* HOL4 word_allocProofScript.sml:8232-8234: a proof *)

(* HOL4 word_allocProofScript.sml:8236-8249: a proof *)

(* HOL4 word_allocProofScript.sml:8251-8266: a proof *)

(* HOL4 word_allocProofScript.sml:8268-8296: a proof *)

(* HOL4 word_allocProofScript.sml:8298-8338: a proof *)
    (*Establish invariants about ssa_cut to use later*)
(* HOL4 word_allocProofScript.sml:8340-8351: a proof *)
    (*Probably need to case split here to deal with the 2 cases*)
(* HOL4 word_allocProofScript.sml:8353-8383: a proof *)
      (*Important preservation step*)
(* HOL4 word_allocProofScript.sml:8385-8392: a proof *)
      (*Try to use cut_envs_lemma from word_live*)
(* HOL4 word_allocProofScript.sml:8394-8458: a proof *)
        (*Backwards chaining*)
(* HOL4 word_allocProofScript.sml:8460-8468: a proof *)
        (*This went missing somewhere..*)
(* HOL4 word_allocProofScript.sml:8470-8474: ML code, not ported *)
        (*Now is a good place to establish the invariant
           ssa_locals_rel*)
(* HOL4 word_allocProofScript.sml:8476-8546: a proof *)
        (*We set the return variables but it is never in the
          locals so the ssa_locals_rel property is preserved*)
(* HOL4 word_allocProofScript.sml:8549-8631: a proof *)
        (*"Hot-swap" the suffix of perm, maybe move into lemma*)
(* HOL4 word_allocProofScript.sml:8633-8645: a proof *)
        (*Excepting without handler*)
(* HOL4 word_allocProofScript.sml:8647-8677: a proof *)
        (* 4 subgoals *)
(* HOL4 word_allocProofScript.sml:8679-8685: a proof *)
    (*Handler reasoning*)
(* HOL4 word_allocProofScript.sml:8687-8719: a proof *)
    (*Important preservation lemma*)
(* HOL4 word_allocProofScript.sml:8721-8733: a proof *)
    (*Try to use cut_env_lemma from word_live*)
(* HOL4 word_allocProofScript.sml:8735-8786: a proof *)
    (*More props theorems that will be useful*)
(* HOL4 word_allocProofScript.sml:8788-9191: a proof *)
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
(* HOL4 word_allocProofScript.sml:9193-9226: a proof *)

(* HOL4 word_allocProofScript.sml:9228-9261: a proof *)

(* HOL4 word_allocProofScript.sml:9263-9331: a proof *)

(* HOL4 word_allocProofScript.sml:9333-9459: a proof *)
    (*Establish invariants about ssa_cut to use later*)
(* HOL4 word_allocProofScript.sml:9461-9606: a proof *)

(* HOL4 word_allocProofScript.sml:9608-9647: a proof *)

(* HOL4 word_allocProofScript.sml:9649-9654: a proof *)

(* HOL4 word_allocProofScript.sml:9656-9687: a proof *)

(* HOL4 word_allocProofScript.sml:9689-9692: a proof *)

(* HOL4 word_allocProofScript.sml:9694-9704: a proof *)

(* HOL4 word_allocProofScript.sml:9706-9708: a proof *)

(* HOL4 word_allocProofScript.sml:9710-9858: a proof *)

(* HOL4 word_allocProofScript.sml:9860-9862: a proof *)

(* HOL4 word_allocProofScript.sml:9864-9866: a proof *)

(* HOL4 word_allocProofScript.sml:9868: a proof *)
    (*FFI*)
(* HOL4 word_allocProofScript.sml:9870-10010: a proof *)

(* HOL4 word_allocProofScript.sml:10012-10045: a proof *)

(* HOL4 word_allocProofScript.sml:10047-10096: a proof *)

(* HOL4 word_allocProofScript.sml:10098-10115: a proof *)

(* HOL4 word_allocProofScript.sml:10117-10134: a proof *)

(* HOL4 word_allocProofScript.sml:10136: a proof *)

(*For starting up*)

(*Full correctness theorem*)

(* Prove that the ssa form sets up pre_alloc_conventions
   and preserves some syntactic conventions
*)

(*Prove that the transform sets up arbitrary programs with
  the appropriate conventions*)

(* HOL4 word_allocProofScript.sml:10716-10731: a proof *)

(* HOL4 word_allocProofScript.sml:10733-10736: a proof *)

(* HOL4 word_allocProofScript.sml:10738-10741: a proof *)

(* HOL4 word_allocProofScript.sml:10743: a proof *)

(* HOL4 word_allocProofScript.sml:10922-10939: a proof *)

(* HOL4 word_allocProofScript.sml:10941-10944: a proof *)

(* HOL4 word_allocProofScript.sml:10946-10949: a proof *)

(* HOL4 word_allocProofScript.sml:10951: a proof *)

(* HOL4 word_allocProofScript.sml:11124-11140: a proof *)

(* HOL4 word_allocProofScript.sml:11142-11145: a proof *)

(* HOL4 word_allocProofScript.sml:11147-11150: a proof *)

(* HOL4 word_allocProofScript.sml:11152: a proof *)

(* word_alloc syntactic stuff *)

(* HOL4 word_allocProofScript.sml:11176-11180: a proof *)

(*Composing with a function using apply_colour*)

(* HOL4 word_allocProofScript.sml:11302-11305: a proof *)

(*word_alloc preserves syntactic conventions*)

(* HOL4 word_allocProofScript.sml:11437-11448: code that the source
   has in a comment *)
