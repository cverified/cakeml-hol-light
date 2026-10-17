(* ======================================================== *)
(*  clos_annotateProof: ported from HOL4's
    compiler/backend/proofs/clos_annotateProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_annotate
*)

needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 ML code, not ported:
val EVERY2_EL = LIST_REL_EL_EQN |> SPEC_ALL |> EQ_IMP_RULE |> fst
                |> UNDISCH |> CONJUNCT2 |> DISCH_ALL;
*)

(* alternative definition of free_vars (fv) function *)

let alt_fv_def = cake_define
  `alt_fv n xs = has_var n (SND (alt_free xs))`;;

let alt_fv1_def = cake_define
  `alt_fv1 v e = alt_fv v [e]`;;

(* value relation *)

(* HOL4 overload (expanded in the port):
     alt_fv_set = λx y. alt_fv y x *)

let v_rel = cake_inductive
  `(clos_annotateProof_v_rel (closSem_Number j) (closSem_Number j)) /\
   (clos_annotateProof_v_rel (Word64 w) (Word64 w)) /\
   (EVERY2 clos_annotateProof_v_rel (xs:closSem_v list) (ys:closSem_v
     list) ==>
    clos_annotateProof_v_rel (closSem_Block t xs) (closSem_Block t
      ys)) /\
   (clos_annotateProof_v_rel (closSem_ByteVector ws)
     (closSem_ByteVector ws)) /\
   (clos_annotateProof_v_rel (closSem_RefPtr b r1) (closSem_RefPtr b
     r1)) /\
   ((clos_annotate_shift (FST (alt_free [c])) m num_args i = [c']) /\
    (!n. (\x y. alt_fv y x) [c] n /\ num_args <= n ==>
         env_ok m 0 i env env' (n - num_args)) /\
    every_Fn_vs_NONE [c] /\
    (LENGTH env = m) /\ EVERY2 clos_annotateProof_v_rel vals vals'
      ==>
    clos_annotateProof_v_rel (Closure p vals env num_args c) (Closure
      p vals' env' num_args c')) /\
   (EVERY2 (\(num_args,c1) (num_args',c1').
      ?m i.
        (num_args' = num_args) /\
        (clos_annotate_shift (FST (alt_free [c1])) m (LENGTH cs +
          num_args) i = [c1']) /\
        (!n. (\x y. alt_fv y x) [c1] n /\ num_args + LENGTH cs <= n
          ==>
           env_ok m 0 i env env' (n - (num_args + LENGTH cs))) /\
        every_Fn_vs_NONE [c1] /\
        (LENGTH env = m)) cs cs' /\
    EVERY2 clos_annotateProof_v_rel vals vals' /\ index < LENGTH cs
      ==>
    clos_annotateProof_v_rel (Recclosure p vals env cs index)
      (Recclosure p vals' env' cs' index)) /\
   (l + m <= n ==>
    env_ok m l i (env2:closSem_v list) (env2':closSem_v list) n) /\
   (n < l /\ clos_annotateProof_v_rel (EL n env2) (EL n env2') /\
    n < LENGTH env2 /\ n < LENGTH env2' ==>
    env_ok m l i env2 env2' n) /\
   (l <= n /\ n < l + m /\
    n < l + m /\ (sptree_lookup (n - l) i = SOME v) /\
    n < LENGTH env2 /\
    l + v < LENGTH env2' /\
    clos_annotateProof_v_rel (EL n env2) (EL (l + v) env2') ==>
    env_ok m l i env2 env2' n)`;;
hol4_overload "v_rel" "clos_annotateProof_v_rel";;

(* HOL4 ML code, not ported:
val env_ok_def = v_rel_cases |> CONJUNCT2
*)

(* HOL4 ML code, not ported:
val env_ok_cons = env_ok_EXTEND
  |> Q.INST [`env1`|->`[v1]`,`env2`|->`[v2]`] |> Q.GEN `l1`
  |> SIMP_RULE (srw_ss()) []
*)

(* HOL4 ML code, not ported:
val env_ok_1 = env_ok_EXTEND
  |> Q.INST [`env1`|->`[v1]`,`env2`|->`[v2]`,`l`|->`0`] |> Q.GEN `l1`
  |> SIMP_RULE (srw_ss()) []
*)

(* HOL4 ML code, not ported:
val env_ok_some = env_ok_EXTEND
  |> DISCH ``l + LENGTH (env1:closSem$v list) = k``
  |> Q.GEN `l1` |> SIMP_RULE std_ss []
  |> REWRITE_RULE [AND_IMP_INTRO] |> GEN_ALL
*)

(* HOL4 ML code, not ported:
val env_ok_append = env_ok_EXTEND
  |> GSYM |> Q.INST [`l`|->`0`]
  |> SIMP_RULE (srw_ss()) []
*)

let state_rel_def = cake_define
  `clos_annotateProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (state_clock s = state_clock t) /\
     (state_ffi s = state_ffi t) /\
     (closSem_state_max_app s = closSem_state_max_app t) /\
     (closSem_state_compile_oracle t = (I ## (clos_annotate_annotate
       0) ## clos_annotate_compile) o closSem_state_compile_oracle s) /\
     (closSem_state_compile s = (\cfg (es,aux). closSem_state_compile
       t cfg (clos_annotate_annotate 0 es,clos_annotate_compile aux)))
       /\
     EVERY2 (OPTREL clos_annotateProof_v_rel) (closSem_state_globals
       s) (closSem_state_globals t) /\
     (FDOM (state_refs s) = FDOM (state_refs t)) /\
     (!n r1.
       (FLOOKUP (state_refs s) n = SOME r1) ==>
       (?r2. (FLOOKUP (state_refs t) n = SOME r2) /\
         closProps_ref_rel clos_annotateProof_v_rel r1 r2)) /\
     (FDOM (closSem_state_code s) = FDOM (closSem_state_code t)) /\
     (!name arity c.
       (FLOOKUP (closSem_state_code s) name = SOME (arity,c)) ==>
       (?c2.
         (clos_annotate_shift (FST (alt_free [c])) 0 arity LN = [c2])
           /\
         (FLOOKUP (closSem_state_code t) name = SOME (arity,c2))))`;;
hol4_overload "state_rel" "clos_annotateProof_state_rel";;

(* some syntactic properties of the compiler *)

(* semantic functions respect relation *)

(* compiler correctness *)

(*
Theorem MAPi_MAPi:
   !xs. MAPi f (MAPi g xs) = MAPi (\i x. f i (g i x)) xs
Proof
  ...
QED
*)

(* HOL4 ML code, not ported:
val every_Fn_vs_NONE_EVERY_MAP =
  every_Fn_vs_NONE_EVERY
  |> Q.SPEC`MAP f ls`
  |> SIMP_RULE std_ss [EVERY_MAP]
  |> GSYM
*)

(* HOL4 ML code, not ported:
val code_tac =
    imp_res_tac evaluate_code
    \\ fs[DISTINCT_FUPDATE_LIST_UNION,DISJOINT_FEVERY_FUNION,
          ALL_DISTINCT_FEVERY_alist_to_fmap,EVERY_FLAT,
          EVERY_MAP,EVERY_GENLIST,shift_seq_def]
    \\ fs[every_Fn_vs_NONE_EVERY_MAP,o_DEF];
*)

(* more correctness properties *)

(* HOL4 ML code, not ported:
val IF_MAP_EQ = MAP_EQ_f |> SPEC_ALL |> EQ_IMP_RULE |> snd;
*)

(* semantics preservation *)

(* more syntactic properties *)
