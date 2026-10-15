(* ======================================================== *)
(*  word_copyProof: ported from HOL4's
    compiler/backend/proofs/word_copyProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_copy
*)

needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_copy.ml";;
needs "lib/sptree.ml";;

(* HOL4 ML code, not ported:
val s = ``s:('a,'c,'ffi) wordSem$state``
*)

let CPstate_inv_def = cake_define
  `CPstate_inv cs = (
    (!v c. sptree_lookup v (copy_state_to_eq cs) = SOME c ==> c <
      copy_state_next cs) /\
    (!c. c IN domain (copy_state_from_eq cs) ==> c < copy_state_next
      cs) /\
    (!s c. ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==> c <
      copy_state_next cs) /\
    (!c v. sptree_lookup c (copy_state_from_eq cs) = SOME v ==>
      sptree_lookup v (copy_state_to_eq cs) = SOME c))`;;

(* As a corollary, different classes have different representatives *)
(* unused *)

let both_alloc_vars_def = cake_define
  `both_alloc_vars (t,s) = (is_alloc_var t /\ is_alloc_var s)`;;

(* t := s *)

let CPstate_models_def = cake_define
  `CPstate_models cs S <=>
   (!v c vrep.
     sptree_lookup v (copy_state_to_eq cs) = SOME c ==>
     sptree_lookup c (copy_state_from_eq cs) = SOME vrep ==>
     sptree_lookup v (wordSem_state_locals S) = sptree_lookup vrep
       (wordSem_state_locals S)) /\
   (!s c vrep.
     ALOOKUP (copy_state_store_to_eq cs) s = SOME c ==>
     sptree_lookup c (copy_state_from_eq cs) = SOME vrep ==>
     FLOOKUP (wordSem_state_store S) s = sptree_lookup vrep
       (wordSem_state_locals S))`;;

(* unused *)
(*
Theorem lookup_alist_insert_same:
  ¬MEM k kk ⇒
  LENGTH vv = LENGTH kk ⇒
  lookup k (alist_insert kk vv m) = lookup k m
Proof
  qid_spec_tac‘vv’>>
  Induct_on‘kk’>-rw[alist_insert_def]>>
  Cases_on‘vv’>>rw[alist_insert_def,lookup_insert]
QED
*)

(* HOL4 ML code, not ported:
fun word_exp_cong_tac (asl,c) =
  let
    val (t,_) = dest_eq c
    val (r, d) = strip_comb t
    val (rname, _) = dest_const r
    val tac = case rname of
      "get_var" =>
      metis_tac[CPstate_modelsD_get_var]
    | "get_vars" =>
      irule MAP_get_var_eqD>>simp[]
      >>metis_tac[CPstate_modelsD_get_var]
    | "word_exp" =>
      let
        val (exp_rator, _) = strip_comb $ el 2 d
        val (exp_rator_name, exp_rator_ty) = dest_const exp_rator
        fun use_cong cong = irule cong>>rw[]
      in
        case exp_rator_name of
          "Op" => use_cong word_exp_cong_Op
        | "Shift" => use_cong word_exp_cong_Shift
        | "Load" => use_cong word_exp_cong_Load
        | "Var" => use_cong word_exp_cong_Var
        | "reg_imm_CASE" =>
          metis_tac[CPstate_modelsD_lookup_eq_imm]
*)
(*
          let
            val (xty,_) = dom_rng exp_rator_ty
            val case_rand = ISPEC (mk_comb (r, el 1 d)) $
              TypeBase.case_rand_of xty
          in
            rw[case_rand]
          end
*)
(* HOL4 ML code, not ported:
      end
    | _ =>
      if TypeBase.is_case t then
*)
        (* use appropriate case_cong *)
(* HOL4 ML code, not ported:
        let
          val cong = TypeBase.case_cong_of (#1(dom_rng(type_of r)))
        in
          irule cong>>rw[]
        end
      else NO_TAC
  in
    tac (asl,c)
  end;
*)

(* "inst" is constant wordSem$inst *)

(*
Theorem remove_eq_model_sh_mem_set_var:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  sh_mem_set_var x t st = (err, st') ⇒
  CPstate_models (remove_eq cs t) st'
Proof
  namedCases_on‘x’["","fr"]>-
  (rw[sh_mem_set_var_def]>>
  irule remove_eq_model >>
  first_x_assum (irule_at Any))
  >> Cases_on‘fr’ >> rw[sh_mem_set_var_def]
  >-(fs[] >> metis_tac[remove_eq_model_set_var])
  >-(fs[flush_state_def] >> fs[] >> fs[CPstate_models_def])
QED
*)

(* Conditional body congruence for Loop: if the body transformation
   preserves semantics when the body doesn't error, then the Loop
   transformation preserves semantics when the Loop doesn't error. *)

(* HOL4 ML code, not ported:
Resume copy_prop_correct[Loop]:
  rpt gen_tac >> strip_tac >>
  gvs[copy_prop_prog_def] >> rpt (pairarg_tac >> gvs[]) >>
  conj_tac
  >- (irule evaluate_Loop_body_cong_err >> fs [] >>
      qexists_tac `prog` >> fs [] >> rw [] >>
      first_x_assum (qspecl_then [`empty_eq`,`v`,`c'`,`_0`,`res`,`s'`]
        mp_tac) >>
      simp [empty_eq_inv, empty_eq_model])
  >- simp[empty_eq_model]
QED
*)

(* HOL4 ML code, not ported:
Finalise copy_prop_correct;
*)

(* Main semantics result *)
