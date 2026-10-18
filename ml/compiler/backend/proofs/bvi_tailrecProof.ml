(* ======================================================== *)
(*  bvi_tailrecProof: ported from HOL4's
    compiler/backend/proofs/bvi_tailrecProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_tailrec
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

(* TODO

   - It should be possible to prove that we can replace the simplified
     compile_exp by the old compile_exp without touching the evaluate-
     theorem. Benefits:
       * Less code duplication
       * Can inline auxiliary calls more easily
*)

(* HOL4 bvi_tailrecProofScript.sml:22-25: ML code, not ported *)

let ty_rel_def = cake_define
  `ty_rel = LIST_REL
     (\v t. (t = Int ==> (?k. v = bvlSem_Number k)) /\
            (t = List ==> (?ys. bvlSem_v_to_list v = SOME ys)))`;;

(* HOL4 bvi_tailrecProofScript.sml:120-122: the ML values that the
   definitions below antiquote *)

(* HOL4 bvi_tailrecProofScript.sml:133-135: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:171-175: ML code, not ported *)

let op_id_val_def = cake_define_list
  [`op_id_val bvi_tailrec_Plus = bvlSem_Number (&0)`;
   `op_id_val bvi_tailrec_Times = bvlSem_Number (&1)`;
   `op_id_val (Append:assoc_op) = bvlSem_Block nil_tag []`;
   `op_id_val bvi_tailrec_Noop = bvlSem_Number (&6333)`];;

let env_rel_def = cake_define
  `bvi_tailrecProof_env_rel ty opt acc env1 env2 <=>
     isPREFIX env1 env2 /\
     (opt ==>
       LENGTH env1 = acc /\
       LENGTH env2 > acc /\
       (match ty with
         Int -> (?k. EL acc env2 = bvlSem_Number k) | List ->
           (?ys. bvlSem_v_to_list (EL acc env2) = SOME ys) |
           bvi_tailrec_Any -> F))`;;
hol4_overload "env_rel" "bvi_tailrecProof_env_rel";;

(* HOL4 bvi_tailrecProofScript.sml:274: the overload in_ns_2, which
   the port expands *)

let code_rel_def = cake_define
  `bvi_tailrecProof_code_rel c1 c2 <=>
     (!loc arity exp op.
       sptree_lookup loc c1 = SOME (arity,exp) ==>
       (check_exp loc arity exp = NONE ==>
         sptree_lookup loc c2 = SOME (arity,exp)) /\
       (check_exp loc arity exp = SOME op ==>
         (?n.
           !exp_aux exp_opt.
           compile_exp loc n arity exp = SOME (exp_aux,exp_opt) ==>
             sptree_lookup loc c2 = SOME (arity,exp_aux) /\
             sptree_lookup n c2 = SOME (arity + 1,exp_opt))))`;;
hol4_overload "code_rel" "bvi_tailrecProof_code_rel";;

let optimized_code_def = cake_define
  `optimized_code loc arity exp n c op =
     (?exp_aux exp_opt.
         compile_exp loc n arity exp = SOME (exp_aux,exp_opt) /\
         check_exp loc arity exp = SOME op /\
         sptree_lookup loc c = SOME (arity,exp_aux) /\
         sptree_lookup n c = SOME (arity + 1,exp_opt))`;;

let free_names_def = cake_define
  `bvi_tailrecProof_free_names n (name:num) <=> (!k. ~(n +
  bvl_to_bvi_namespaces * k = name))`;;
hol4_overload "free_names" "bvi_tailrecProof_free_names";;

let namespace_rel_def = cake_define
  `bvi_tailrecProof_namespace_rel (c1:'a spt) (c2:'a spt) <=>
     (!n. n IN domain c2 /\ bvl_num_stubs <= n ==> (if (\n. n MOD
       bvl_to_bvi_namespaces = 2) n then ~(n IN domain c1) else n IN
       domain c1)) /\
     (!n. n IN domain c1 /\ bvl_num_stubs <= n ==> ~((\n. n MOD
       bvl_to_bvi_namespaces = 2) n)) /\
     (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;
hol4_overload "namespace_rel" "bvi_tailrecProof_namespace_rel";;

let input_condition_def = cake_define
  `bvi_tailrecProof_input_condition next' prog <=>
     EVERY (bvi_tailrecProof_free_names next' o FST) prog /\
    ALL_DISTINCT (MAP FST prog) /\
    EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 2) o FST) (FILTER
      ((<=) bvl_num_stubs o FST) prog) /\
    bvl_num_stubs <= next' /\ (\n. n MOD bvl_to_bvi_namespaces =
      2) next'`;;
hol4_overload "input_condition" "bvi_tailrecProof_input_condition";;

let state_rel_def = cake_define
  `bvi_tailrecProof_state_rel s (t:('a,'ffi)bviSem_state) <=> state_refs
     t = state_refs s /\ state_clock
     t = state_clock s /\ bviSem_state_global
     t = bviSem_state_global s /\ state_ffi
     t = state_ffi s /\ compile_oracle
     t = state_co bvi_tailrec_compile_each (compile_oracle s) /\
       compile
     s = state_cc bvi_tailrec_compile_each (compile t) /\
     bvi_tailrecProof_code_rel (state_code s) (state_code t) /\
     bvi_tailrecProof_namespace_rel (state_code s) (state_code t) /\
     (!n. let ((next',cfg),prog) = compile_oracle s n in
             bvi_tailrecProof_input_condition next' prog) /\
     (!n. n IN domain (state_code t) /\ (\n. n MOD
       bvl_to_bvi_namespaces = 2) n ==> n < FST (FST (compile_oracle
       s 0)))`;;
hol4_overload "state_rel" "bvi_tailrecProof_state_rel";;

(* HOL4 bvi_tailrecProofScript.sml:1349-1351: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:1353-1379: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:1381-1386: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:1388-1403: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:1405-1413: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:1415-1466: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:1468-1681: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:1683-1857: ML code, not ported *)
(* HOL4 bvi_tailrecProofScript.sml:1858: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1859: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1860: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1861-1868: ML code, not ported *)
(* HOL4 bvi_tailrecProofScript.sml:1869: code that the source has in
   a comment *)
(* HOL4 bvi_tailrecProofScript.sml:1870-2050: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:2052-2132: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:2134-2332: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:2334-2342: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:2344-2439: ML code, not ported *)

(* HOL4 bvi_tailrecProofScript.sml:2441: ML code, not ported *)
