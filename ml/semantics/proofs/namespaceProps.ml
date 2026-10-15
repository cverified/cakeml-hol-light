(* ======================================================== *)
(*  namespaceProps: ported from HOL4's
    semantics/proofs/namespacePropsScript.sml  *)
(* ======================================================== *)

(*
  Proofs about the namespace datatype.
*)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;

(* ----------- Monotonicity for ind rel ------------ *)

(* ---------- Automatic simps involving empty envs -------------- *)

(* ------------- Other simple automatic theorems --------- *)

(* -------------- nsLookup ------------------ *)

(* -------------- alist_to_ns --------------- *)

(* -------------- nsLift --------------- *)

(* --------------- nsAppend ------------- *)

(* -------------- nsAll ---------------- *)

(* -------------- nsSub ---------------- *)

let alist_rel_restr_def = cake_define_list
  [`alist_rel_restr R l1 l2 [] <=> T`;
   `alist_rel_restr R l1 l2 (k1 :: keys) <=>
        (match ALOOKUP l1 k1 with NONE -> F | SOME v1 ->
          (match ALOOKUP l2 k1 with NONE -> F | SOME v2 -> R k1
            v1 v2 /\ alist_rel_restr R l1 l2 keys))`];;

let alistSub_def = cake_define
  `alistSub R e1 e2 <=> alist_rel_restr R e1 e2 (MAP FST e1)`;;

(* HOL4 ML code, not ported:
val _ = DefnBase.export_cong "alistSub_cong";
*)

(* TERMINATION: wf_rel_tac `measure (\(p,r,env,_). namespace_size (\x.0)
   (\x.0) (\x.0) env)`
 >> rw []
 >> Induct_on `e1M`
 >> rw [namespace_size_def]
 >> PairCases_on `h`
 >> fs [ALOOKUP_def]
 >> every_case_tac
 >> fs []
 >> rw [namespace_size_def,basicSizeTheory.pair_size_def] *)
let nsSub_compute_def = cake_define
  `nsSub_compute path' R (Bind e1V e1M) (Bind e2V e2M) <=>
     alistSub (\k v1 v2. R (mk_id (REVERSE path') k) v1 v2) e1V e2V
       /\
     alistSub (\k v1 v2. nsSub_compute (k :: path') R v1 v2) e1M
       e2M`;;

(*
Theorem nsSub_compute_thm_general:
   !p R e1 e2.
    nsSub R (FOLDR nsLift e1 (REVERSE p)) (FOLDR nsLift e2 (REVERSE p))
      ⇔
    nsSub_compute p R e1 e2
Proof
 ho_match_mp_tac (theorem "nsSub_compute_ind")
 >> rw [nsSub_def, nsSub_compute_def, alistSub_def, alist_rel_restr_thm,
   nsLookup_def]
 >> eq_tac
 >> rw []
 >- (
   `?v1. ALOOKUP e1V k = SOME v1` by metis_tac [option_nchotomy,
     ALOOKUP_NONE]
   >> last_x_assum (qspec_then `mk_id (REVERSE p) k` mp_tac)
   >> simp [nsLookup_FOLDR_nsLift, nsLookup_def])
 >- (
   `?v1. ALOOKUP e1M k = SOME v1` by metis_tac [option_nchotomy,
     ALOOKUP_NONE]
   >> last_assum (qspec_then `REVERSE (k::p)` assume_tac)
   >> fs [nsLookupMod_FOLDR_nsLift_none, nsLookupMod_def]
   >> every_case_tac
   >> fs []
   >> first_x_assum drule
   >> disch_then drule
   >> disch_then (strip_assume_tac o GSYM)
   >> simp []
   >> pop_assum kall_tac
   >> rw []
   >- (
     fs [nsLookup_FOLDR_nsLift_some]
     >> first_x_assum (qspec_then `mk_id (REVERSE p++[k]++p2) n` mp_tac)
     >> Cases_on `p=[]`
     >> simp [nsLookup_def, mk_id_def])
   >> fs []
   >> rw []
   >- (
     `p3 = []`
       by (
         fs [IS_PREFIX_THM]
         >> `LENGTH p3 = 0` by decide_tac
         >> Cases_on `p3`
         >> fs [])
     >> fs [nsLookupMod_def])
   >- (
     fs [nsLookupMod_FOLDR_nsLift_none]
     >> rw []
     >> fs []
     >> rw []
     >> last_x_assum (qspec_then `REVERSE p++[k]++p3` mp_tac)
     >> rw []
     >> fs [nsLookupMod_def]
     >> every_case_tac
     >> fs []
     >> rw []
     >> metis_tac [IS_PREFIX_APPEND3, APPEND_ASSOC]))
 >- (
   fs [nsLookup_FOLDR_nsLift_some]
   >> rw []
   >> fs [mk_id_def]
   >- (
     Cases_on `id`
     >> fs [nsLookup_def]
     >- (
       drule ALOOKUP_MEM
       >> rw []
       >> fs [MEM_MAP, PULL_EXISTS]
       >> first_x_assum drule
       >> simp [])
     >> every_case_tac
     >> fs []
     >> drule ALOOKUP_MEM
     >> strip_tac
     >> fs [MEM_MAP, PULL_EXISTS]
     >> first_x_assum drule
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> disch_then (strip_assume_tac o GSYM)
     >> simp []
     >> pop_assum kall_tac
     >> rw []
     >> metis_tac [mk_id_surj])
   >- (
     Cases_on `p2`
     >> fs [nsLookup_def, mk_id_def]
     >- (
       drule ALOOKUP_MEM
       >> rw []
       >> fs [MEM_MAP, PULL_EXISTS]
       >> first_x_assum drule
       >> simp [])
     >> every_case_tac
     >> fs []
     >> drule ALOOKUP_MEM
     >> strip_tac
     >> fs [MEM_MAP, PULL_EXISTS]
     >> first_x_assum drule
     >> fs []
     >> first_x_assum drule
     >> disch_then drule
     >> disch_then (strip_assume_tac o GSYM)
     >> simp []
     >> pop_assum kall_tac
     >> rw []
     >> first_x_assum drule
     >> rw []
     >> full_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]))
 >- (
   fs [nsLookupMod_FOLDR_nsLift_none]
   >> rw []
   >> fs []
   >> rw []
   >> fs []
   >- (
     `p3 = []`
       by (
         fs [IS_PREFIX_THM]
         >> `LENGTH p3 = 0` by decide_tac
         >> Cases_on `p3`
         >> fs [])
      >> fs [nsLookupMod_def])
   >> CCONTR_TAC
   >> fs []
   >> `?x. nsLookupMod (Bind e1V e1M) p3 = SOME x` by metis_tac
     [option_nchotomy]
   >> fs []
   >> pop_assum mp_tac
   >> Cases_on `p3`
   >> fs [nsLookupMod_def]
   >> CASE_TAC
   >> rw []
   >> fs [MEM_MAP, PULL_EXISTS]
   >> drule ALOOKUP_MEM
   >> rw []
   >> first_x_assum drule
   >> rw []
   >> fs []
   >> first_x_assum drule
   >> disch_then drule
   >> disch_then (strip_assume_tac o GSYM)
   >> fs []
   >> pop_assum kall_tac
   >> first_x_assum (qspec_then `REVERSE p ++ [h] ++ t` mp_tac)
   >> rw [])
QED

Theorem nsSub_compute_thm:
   !R e1 e2. nsSub R e1 e2 ⇔ nsSub_compute [] R e1 e2
Proof
 rw [GSYM nsSub_compute_thm_general]
QED
*)

(* -------------- nsAll2 ---------------- *)

(* -------------- nsMap --------------- *)

(* --------------- nsDom --------------- *)
