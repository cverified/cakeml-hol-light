(* ======================================================== *)
(*  bvi_tmcProof: ported from HOL4's
    compiler/backend/proofs/bvi_tmcProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_tailrec
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_tmc.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 ML code, not ported:
val s = “s : (num # γ, 'ffi) bviSem$state”;
*)

(* HOL4 overload (expanded in the port):
     in_ns_3 = λn. n MOD bvl_to_bvi_namespaces = 3 *)

let v_rel = cake_inductive
  `!f i.
   v_rel f (Number i) (Number i) /\
   (!f w.
   v_rel f (Word64 w) (Word64 w) /\
   (!f n xs ys.
     LIST_REL (v_rel f) xs ys ==>
     v_rel f (Block n xs) (Block n ys) /\
   (!f n.
   v_rel f (bvlSem_CodePtr n) (bvlSem_CodePtr n) /\
   (!f n m b.
     FLOOKUP f n = SOME m ==>
     v_rel f (RefPtr b n) (RefPtr b m)))))`;;

let ref_rel = cake_inductive
  `ref_rel f (ByteArray b bs) (ByteArray b bs) /\
   LIST_REL (v_rel f) xs ys ==>
   ref_rel f (ValueArray xs) (ValueArray ys) /\
   v_rel f x y ==>
   ref_rel f (Thunk tm x) (Thunk tm y)`;;

let env_rel_def = cake_define
  `bvi_tmcProof_env_rel opt f env1 env2 <=>
   (?xs ys.
     env2 = xs ++ ys /\
     LIST_REL (v_rel f) env1 xs /\
     (opt ==>
       LENGTH ys = 2 /\
       (?hole_ptr hole_idx.
         EL 0 ys = RefPtr F hole_ptr /\
         EL 1 ys = Number hole_idx /\
         small_enough_int hole_idx)))`;;
hol4_overload "env_rel" "bvi_tmcProof_env_rel";;

let no_mutcons_op_def = cake_define
  `no_mutcons_op op <=> (!tag i. ~(op = closLang_MemOp
  (closLang_MutCons tag i)))`;;

let no_mutcons_def = cake_define_list
  [`no_mutcons (Var n:flatLang_exp) <=> T`;
   `no_mutcons (If x1 x2 x3:flatLang_exp) <=> no_mutcons x1 /\
  no_mutcons x2 /\ no_mutcons x3`;
   `no_mutcons (Let xs x:flatLang_exp) <=> EVERY no_mutcons xs /\
  no_mutcons x`;
   `no_mutcons (Raise x:flatLang_exp) <=> no_mutcons x`;
   `no_mutcons (Tick x:flatLang_exp) <=> no_mutcons x`;
   `no_mutcons (Call ticks dest xs handler:flatLang_exp) <=>
         EVERY no_mutcons xs /\ (match handler with NONE -> T |
           SOME x -> no_mutcons x)`;
   `no_mutcons (Force loc n:flatLang_exp) <=> T`;
   `no_mutcons (bvi_LetCall rets ticks dest xs y) <=> EVERY
  no_mutcons xs /\ no_mutcons y`;
   `no_mutcons (bvi_Return xs) <=> EVERY no_mutcons xs`;
   `no_mutcons (Op op xs:flatLang_exp) <=> no_mutcons_op op /\ EVERY
  no_mutcons xs`];;

let code_rel_def = cake_define
  `bvi_tmcProof_code_rel c1 c2 <=>
     (!loc arity exp.
       sptree_lookup loc c1 = SOME (arity,exp) ==>
       no_mutcons exp /\
       (?n.
         (compile_exp loc n arity exp = NONE ==>
          sptree_lookup loc c2 = SOME (arity,exp)) /\
         (!wrap work.
           compile_exp loc n arity exp = SOME (wrap,work) ==>
           sptree_lookup loc c2 = SOME (arity,wrap) /\
           sptree_lookup n c2 = SOME (arity + 2,work))))`;;
hol4_overload "code_rel" "bvi_tmcProof_code_rel";;

let free_names_def = cake_define
  `bvi_tmcProof_free_names n (name:num) <=> (!k. ~(n +
  bvl_to_bvi_namespaces * k = name))`;;
hol4_overload "free_names" "bvi_tmcProof_free_names";;

let namespace_rel_def = cake_define
  `bvi_tmcProof_namespace_rel (c1:'a spt) (c2:'a spt) <=>
     (!n. n IN domain c2 /\ bvl_num_stubs <= n ==> (if (\n. n MOD
       bvl_to_bvi_namespaces = 3) n then ~(n IN domain c1) else n IN
       domain c1)) /\
     (!n. n IN domain c1 /\ bvl_num_stubs <= n ==> ~((\n. n MOD
       bvl_to_bvi_namespaces = 3) n)) /\
     (!n. n IN domain c2 /\ n < bvl_num_stubs ==> n IN domain c1)`;;
hol4_overload "namespace_rel" "bvi_tmcProof_namespace_rel";;

(* This should say: expression in prog satisfies no-mutblock property *)
let input_condition_def = cake_define
  `bvi_tmcProof_input_condition next prog <=>
     EVERY (bvi_tmcProof_free_names next o FST) prog /\
     EVERY (no_mutcons o SND o SND) prog /\
     ALL_DISTINCT (MAP FST prog) /\
     EVERY ((~) o (\n. n MOD bvl_to_bvi_namespaces = 3) o FST)
       (FILTER ((<=) bvl_num_stubs o FST) prog) /\
     bvl_num_stubs <= next /\ (\n. n MOD bvl_to_bvi_namespaces =
       3) next`;;
hol4_overload "input_condition" "bvi_tmcProof_input_condition";;

let state_ref_rel_def = cake_define
  `state_ref_rel f (s_refs:(num,bvlSem_v bvlSem_ref)fmap)
  (t_refs:(num,bvlSem_v bvlSem_ref)fmap) <=>
     FDOM f = FDOM s_refs /\
     (!i v.
       FLOOKUP s_refs i = SOME v ==>
        (?j w. FLOOKUP f i = SOME j /\
              ref_rel f v w /\
              FLOOKUP t_refs j = SOME w))`;;

let fmap_inj_def = cake_define
  `fmap_inj (f:(num,num)fmap) <=>
     (!p1 p2 q. FLOOKUP f p1 = SOME q /\ FLOOKUP f p2 = SOME q ==>
       p1 = p2)`;;

let state_rel_def = cake_define
  `bvi_tmcProof_state_rel f s (t:('a,'ffi)bviSem_state) <=>
     state_ref_rel f (refs s) (refs t) /\ clock
     t = clock s /\
     OPTREL (\p p'. FLOOKUP f p = SOME p') (bviSem_state_global s)
       (bviSem_state_global t) /\ ffi
     t = ffi s /\ compile_oracle
     t = state_co bvi_tmc_compile_each (compile_oracle s) /\ compile
     s = state_cc bvi_tmc_compile_each (compile t) /\
     bvi_tmcProof_code_rel (code s) (code t) /\
     bvi_tmcProof_namespace_rel (code s) (code t) /\
     (!n. let ((next,cfg),prog) = compile_oracle s n in
             bvi_tmcProof_input_condition next prog) /\
     (!n. n IN domain (code t) /\ (\n. n MOD bvl_to_bvi_namespaces =
       3) n ==> n < FST (FST (compile_oracle s 0))) /\
     fmap_inj f`;;
hol4_overload "state_rel" "bvi_tmcProof_state_rel";;

(* Structural facts about compile_each and the namespace allocation.
   These follow bvi_tailrecProof; they only depend on the recursion
     shape of
   compile_each (NONE keeps an entry, SOME emits wrapper + worker). *)

let eor_rel_def = cake_define
  `eor_rel f x2 x3 =
        match (x2,x3) with
          (Exn v1,Exn v2) -> v_rel f v1 v2
        | ((Ret vs1),(Ret vs2)) -> LIST_REL (v_rel f) vs1 vs2
        | (_1,_2) -> F`;;

let opt_res_rel_def = cake_define
  `opt_res_rel f (r1:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result) (r2:(bvlSem_v
  list,exn_or_ret)semanticPrimitives_result) =
   (match (r1,r2) with (Rval v1,Rval [Block 0 []]) -> T | (Rerr
     e1,Rerr e2) -> exc_rel (eor_rel f) e1 e2 | _3 -> F)`;;

(* not a strict equality anymore! *)

let hole_has_val_def = cake_define
  `hole_has_val (f:(num,num)fmap) (env1:bvlSem_v list) (env2:bvlSem_v
  list) (refs:(num,bvlSem_v bvlSem_ref)fmap) c <=>
   LENGTH env2 = LENGTH env1 + 2 /\
   (?hole_ptr tag finalised left right. EL (LENGTH env1)
     env2 = RefPtr F hole_ptr /\ EL (LENGTH env1 + 1)
     env2 = Number (&(LENGTH left)) /\
     small_enough_int (&(LENGTH left)) /\ ~(
     hole_ptr IN FRANGE f) /\
     FLOOKUP refs hole_ptr = SOME (bvlSem_MutBlock tag finalised
       left c right))`;;

let holes_unchanged_except_def = cake_define
  `holes_unchanged_except f refs refs' changed <=>
     (!ptr tag finalised left child right. ~(
        ptr IN FRANGE f) /\
        FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag finalised left
          child right) ==>
        (?finalised' child'.
          FLOOKUP refs' ptr = SOME (bvlSem_MutBlock tag finalised'
            left child' right) /\
          (~(ptr IN changed) ==> child = child')))`;;

let hole_not_finalised_def = cake_define
  `hole_not_finalised refs ptr <=>
     (?tag left child right.
       FLOOKUP refs ptr = SOME (bvlSem_MutBlock tag F left child
         right))`;;

let holes_still_not_finalised_def = cake_define
  `holes_still_not_finalised f (refs:('gb,'gc bvlSem_ref)fmap)
  (refs':('gb,'gc bvlSem_ref)fmap) <=>
     (!ptr. ~(
       ptr IN FRANGE f) /\
       hole_not_finalised refs ptr ==>
       hole_not_finalised refs' ptr)`;;

let only_fresh_def = cake_define
  `only_fresh (f:(num,num)fmap) (f':(num,num)fmap)
  (refs_old:(num,bvlSem_v bvlSem_ref)fmap) =
   (!n. n IN FRANGE f' /\ ~(n IN FRANGE f) ==> ~(n IN FDOM
     refs_old))`;;

(* TERMINATION: wf_rel_tac ‘measure $ CARD o FDOM o FST o SND o SND’
  >> rpt gen_tac
  >> strip_tac
  >> gvs [finite_mapTheory.FDOM_DOMSUB, FLOOKUP_DEF]
  >> Cases_on ‘CARD (FDOM refs)’
  >- fs[finite_setTheory.fCARD_EQ0]
  >> gvs [] *)
let mb_rel_def = cake_define
  `mb_rel f x2 refs v1 v2 =
        match (x2,v1,v2) with
          ((refs_old:(num,bvlSem_v bvlSem_ref)fmap),(Block tag
            xs:bvlSem_v),(RefPtr b ptr:bvlSem_v)) ->
      (if b \/ ptr IN FRANGE f \/ ptr IN FDOM refs_old then F else
        match FLOOKUP refs ptr with SOME (bvlSem_MutBlock tag' fin'
          left' child' right') ->
            (tag = tag' /\
             fin' = F /\
             (?left child right.
               xs = left ++ [child] ++ right /\
               LIST_REL (v_rel f) left left' /\
               mb_rel f refs_old (refs \\ ptr) child child' /\
               LIST_REL (v_rel f) right right')) | _4 -> F)
        | (_5,v1,v2) -> v_rel f v1 v2`;;

(* Install reads byte/word vectors out of values; these are lists of
   Numbers
   resp. Word64s, which v_rel relates exactly. *)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[IntOp]:
  Cases_on ‘i’
  >~ [‘Const i’] >-
   (gvs [do_app_def, do_app_aux_def, CaseEq "option"]
    >> imp_res_tac LIST_REL_LENGTH
    >> first_assum $ irule_at Any
    >> gvs [v_rel_cases, only_fresh_refl, holes_unchanged_except_refl,
      holes_still_not_finalised_refl, NULL_LENGTH])
  >~ [‘LessConstSmall n’] >-
   (gvs [AllCaseEqs (), v_rel_cases, do_app_def, do_app_aux_def,
     bvlSemTheory.do_app_def]
    >> Cases_on ‘vs’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def]
    >> reverse $ Cases_on ‘t’ >> gvs [v_rel_cases,
      bvlSemTheory.do_int_app_def]
    >- (Cases_on ‘t'’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def,
      bvl_to_bvi_id, bvlSemTheory.Boolv_def])
    >> gvs [bvlSemTheory.Boolv_def, bvl_to_bvi_id]
    >> first_assum $ irule_at Any
    >> gvs [only_fresh_refl, holes_unchanged_except_refl,
      holes_still_not_finalised_refl])
  >> gvs [AllCaseEqs (), v_rel_cases, do_app_def, do_app_aux_def,
    bvlSemTheory.do_app_def]
  >> reverse $ Cases_on ‘vs’ >> gvs [v_rel_cases,
    bvlSemTheory.do_int_app_def]
  >> Cases_on ‘t’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def]
  >> Cases_on ‘t'’ >> gvs [v_rel_cases, bvlSemTheory.do_int_app_def,
    bvl_to_bvi_id, bvlSemTheory.Boolv_def]
  >> first_assum $ irule_at Any
  >> gvs [only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
QED
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[WordOp]:
  gvs [do_app_def, do_app_aux_def, AllCaseEqs (),
    bvlSemTheory.do_app_def]
  >> drule_all do_word_app_v_rel >> strip_tac >> gvs []
  >> qexists ‘f’
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> drule do_word_app_v_rel_refl >> simp []
QED
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[Label]:
  gvs [AllCaseEqs (), v_rel_cases, do_app_def, do_app_aux_def]
  >> first_assum $ irule_at Any
  >> gvs [only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl, state_rel_def, code_rel_def,
    domain_lookup]
  >> Cases_on ‘v’
  >> last_x_assum $ drule
  >> strip_tac
  >> Cases_on ‘compile_exp n n' q r’
  >- gvs []
  >> gvs []
  >> Cases_on ‘x’
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[GlobOp]:
  Cases_on ‘g’
  >~ [‘do_app (GlobOp AllocGlobal)’] >-
   gvs [do_app_def, do_app_aux_def, AllCaseEqs ()]
  >~ [‘do_app (GlobOp GlobalsPtr)’] >-
   (gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
    >> ‘OPTREL (λp p'. FLOOKUP f p = SOME p') s.global s'.global’ by gvs
      [state_rel_def]
    >> gvs [OPTREL_def]
    >> qexists ‘f’ >> gvs [only_fresh_refl, holes_unchanged_except_refl,
      holes_still_not_finalised_refl])
  >~ [‘do_app (GlobOp SetGlobalsPtr)’] >-
   (gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
    >> qexists ‘f’
    >> simp [only_fresh_refl, holes_unchanged_except_refl,
      holes_still_not_finalised_refl]
    >> rpt conj_tac
    >- simp [bvlSemTheory.Unit_def]
    >> gvs [state_rel_def, OPTREL_def])
  >~ [‘do_app (GlobOp (Global _))’] >-
   (gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
    >> ‘OPTREL (λp p'. FLOOKUP f p = SOME p') s.global s'.global’ by gvs
      [state_rel_def]
    >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
    >> gvs [OPTREL_def]
    >> qpat_assum ‘state_ref_rel f s.refs s'.refs’
         (strip_assume_tac o REWRITE_RULE [state_ref_rel_def])
    >> first_x_assum drule >> strip_tac >> gvs [ref_rel_cases]
    >> ‘n < LENGTH ys’ by (imp_res_tac LIST_REL_LENGTH >> gvs [])
    >> ‘v_rel f (EL n xs) (EL n ys)’ by gvs [LIST_REL_EL_EQN]
    >> qexists ‘f’ >> simp [only_fresh_refl,
      holes_unchanged_except_refl, holes_still_not_finalised_refl]
    >> qpat_x_assum ‘v_rel f (EL n xs) _’ mp_tac
    >> simp [Once v_rel_cases])
*)
  (* SetGlobal *)
(* HOL4 ML code, not ported:
  >> gvs [do_app_def, do_app_aux_def, AllCaseEqs (), v_rel_cases]
  >> ‘OPTREL (λp p'. FLOOKUP f p = SOME p') s.global s'.global’ by gvs
    [state_rel_def]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> gvs [OPTREL_def]
  >> qpat_assum ‘state_ref_rel f s.refs s'.refs’
       (strip_assume_tac o REWRITE_RULE [state_ref_rel_def])
  >> first_x_assum drule >> strip_tac >> gvs [ref_rel_cases]
  >> rename1 ‘LIST_REL (v_rel f) xs ws’
  >> ‘n < LENGTH ws’ by (imp_res_tac LIST_REL_LENGTH >> gvs [])
  >> qexists ‘f’ >> simp [only_fresh_refl]
  >> rpt conj_tac
  >> (
    (gvs [state_rel_def] >> irule state_ref_rel_update >> simp
      [ref_rel_cases]
     >> irule EVERY2_LUPDATE_same >> simp [Once v_rel_cases] >> gvs [])
    ORELSE
    (irule holes_unchanged_except_frange_update >> first_assum $
      irule_at Any)
    ORELSE
    (irule holes_still_not_finalised_frange_update >> first_assum $
      irule_at Any)
    ORELSE
    simp [bvlSemTheory.Unit_def])
QED
*)

(* Allocating a fresh reference (Ref, RefByte, RefArray). *)
(* HOL4 ML code, not ported:
val memop_create_tac =
  simp [bvl_to_bvi_refs]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> qmatch_goalsub_abbrev_tac ‘s.refs⟨_ ↦ rv⟩’
  >> qmatch_goalsub_abbrev_tac ‘s'.refs⟨_ ↦ rw⟩’
  >> drule state_rel_alloc
  >> disch_then $ qspecl_then
       [‘LEAST ptr. ptr ∉ FDOM s.refs’, ‘LEAST ptr. ptr ∉ FDOM s'.refs’,
        ‘rv’, ‘rw’] mp_tac
  >> impl_tac
  >- (simp [fresh_ptr_fresh]
      >> conj_tac >- (irule fresh_not_in_range_f >> first_assum $
        irule_at Any)
      >> ‘f ⊑ f⟨(LEAST ptr. ptr ∉ FDOM s.refs) ↦ (LEAST ptr. ptr ∉ FDOM
        s'.refs)⟩’
           by (simp [SUBMAP_FUPDATE_FLOOKUP, FLOOKUP_DEF]
               >> gvs [state_ref_rel_def, fresh_ptr_fresh])
      >> irule ref_rel_submap
      >> first_assum $ irule_at Any
      >> unabbrev_all_tac >> gvs [ref_rel_cases,
        LIST_REL_REPLICATE_same]
      >> rw [] >> gvs [Once v_rel_cases])
  >> strip_tac
  >> qexists ‘f⟨(LEAST ptr. ptr ∉ FDOM s.refs) ↦ (LEAST ptr. ptr ∉ FDOM
    s'.refs)⟩’
  >> gvs [];
*)

(* Reading a reference without changing the state, returning a fresh
   value
   (Length, LengthByte, DerefByte, BoundsCheckArray, BoundsCheckByte).
     *)
(* HOL4 ML code, not ported:
val memop_read_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> drule_all state_ref_rel_lookup >> strip_tac
  >> gvs [ref_rel_cases, bvl_to_bvi_id, only_fresh_refl,
    holes_unchanged_except_refl, holes_still_not_finalised_refl]
  >> imp_res_tac LIST_REL_LENGTH >> gvs []
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def];
*)

(* Reading an element out of a ValueArray reference (El on a RefPtr). *)
(* HOL4 ML code, not ported:
val memop_el_ref_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> drule_all state_ref_rel_lookup >> strip_tac >> gvs [ref_rel_cases]
  >> qmatch_asmsub_rename_tac ‘LIST_REL (v_rel f) xs ws’
  >> imp_res_tac LIST_REL_LENGTH
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> ‘Num i'' < LENGTH xs’ by intLib.ARITH_TAC
  >> ‘v_rel f (EL (Num i'') xs) (EL (Num i'') ws)’ by gvs
    [LIST_REL_EL_EQN]
  >> pop_assum mp_tac >> simp [Once v_rel_cases];
*)

(* Reading an element out of a Block (El on a Block). *)
(* HOL4 ML code, not ported:
val memop_el_block_tac =
  qexists ‘f’
  >> imp_res_tac LIST_REL_LENGTH
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> ‘v_rel f (EL (Num i'') xs'') (EL (Num i'') ys)’ by gvs
    [LIST_REL_EL_EQN]
  >> pop_assum mp_tac >> simp [Once v_rel_cases];
*)

(* Updating a ValueArray reference in place (Update). *)
(* HOL4 ML code, not ported:
val memop_update_val_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> qpat_assum ‘state_ref_rel f s.refs s'.refs’
       (strip_assume_tac o REWRITE_RULE [state_ref_rel_def])
  >> qpat_x_assum ‘FLOOKUP s.refs _ = SOME (ValueArray _)’ assume_tac
  >> first_x_assum drule >> strip_tac >> gvs [ref_rel_cases]
  >> imp_res_tac LIST_REL_LENGTH
  >> simp [bvl_to_bvi_refs, only_fresh_refl, bvlSemTheory.Unit_def]
  >> rpt conj_tac
  >> (intLib.ARITH_TAC
      ORELSE (irule holes_unchanged_except_frange_update >> first_assum
        $ irule_at Any)
      ORELSE (irule holes_still_not_finalised_frange_update >>
        first_assum $ irule_at Any)
      ORELSE (gvs [state_rel_def] >> irule state_ref_rel_update
              >> simp [ref_rel_cases] >> irule EVERY2_LUPDATE_same
              >> simp [Once v_rel_cases] >> gvs []));
*)

(* Updating a ByteArray reference in place (UpdateByte, CopyByte,
   XorByte).
   The byte arrays are equal on both sides, so the operations agree. *)
(* HOL4 ML code, not ported:
val memop_update_byte_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> imp_res_tac state_ref_rel_lookup >> gvs [ref_rel_cases]
  >> simp [bvl_to_bvi_refs, only_fresh_refl, bvlSemTheory.Unit_def]
  >> rpt conj_tac
  >> (intLib.ARITH_TAC
      ORELSE (irule holes_unchanged_except_frange_update >> first_assum
        $ irule_at Any)
      ORELSE (irule holes_still_not_finalised_frange_update >>
        first_assum $ irule_at Any)
      ORELSE (gvs [state_rel_def] >> irule state_ref_rel_update >> simp
        [ref_rel_cases]));
*)

(* Turning a stack of mutable conses into a Block (FinaliseCons). *)
(* HOL4 ML code, not ported:
val memop_finalise_tac =
  qexists ‘f’
  >> simp [only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> gvs [bviSemTheory.finalise_cons_def, AllCaseEqs ()]
  >> imp_res_tac state_ref_rel_lookup
  >> gvs [ref_rel_cases, bviSemTheory.finalise_cons_def]
  >> simp [Once v_rel_cases];
*)

(* Mutating the hole of a MutBlock (UpdateCons) cannot happen:
   state_ref_rel
   never relates a MutBlock. *)
(* HOL4 ML code, not ported:
val memop_mutblock_tac =
  ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> drule_all no_mutblock >> simp [];
*)

(* ConfigGC returns Unit and leaves the state unchanged. *)
(* HOL4 ML code, not ported:
val memop_configgc_tac =
  qexists ‘f’
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
          holes_still_not_finalised_refl, bvlSemTheory.Unit_def];
*)

(* Comparing two ByteArray references without changing the state
   (StringCmp).
   Both byte arrays are equal on the two sides, so the comparison
     agrees. *)
(* HOL4 ML code, not ported:
val memop_strcmp_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> imp_res_tac state_ref_rel_lookup
  >> gvs [ref_rel_cases, bvl_to_bvi_id, only_fresh_refl,
    holes_unchanged_except_refl, holes_still_not_finalised_refl]
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def];
*)

(* HOL4 ML code, not ported:
val memop_finalise_tac =
drule do_app_op_finalise_rel
>> disch_then drule
>> gvs [v_rel_cases]
>> strip_tac
>> rpt $ first_assum $ irule_at Any
>> gvs [v_rel_cases]
*)

(* HOL4 ML code, not ported:
val memop_finalise_block_tac =
drule do_app_op_finalise_rel
>> disch_then drule
>> gvs [v_rel_cases]
>> disch_then $ qspec_then ‘Block n ys’ mp_tac
>> gvs []
>> strip_tac
>> rpt $ first_assum $ irule_at Any
>> gvs [v_rel_cases]
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[MemOp]:
  Cases_on ‘m’
  >> gvs [do_app_def, do_app_aux_def, AllCaseEqs (),
    bvlSemTheory.do_app_def,
          no_mutcons_op_def, v_rel_cases]
  >> FIRST [memop_mutblock_tac >> NO_TAC, memop_finalise_tac >> NO_TAC,
            memop_create_tac >> NO_TAC, memop_update_val_tac >> NO_TAC,
            memop_update_byte_tac >> NO_TAC, memop_el_ref_tac >> NO_TAC,
            memop_el_block_tac >> NO_TAC, memop_read_tac >> NO_TAC,
            memop_configgc_tac >> NO_TAC, memop_strcmp_tac >> NO_TAC,
            memop_finalise_tac >> NO_TAC, memop_finalise_block_tac >>
              NO_TAC]
QED
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[ThunkOp]:
  Cases_on ‘t’
  >> gvs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def,
    AllCaseEqs ()]
  >~ [‘Thunk NotEvaluated’] >-
*)
   (* UpdateThunk *)
(* HOL4 ML code, not ported:
   (qpat_x_assum ‘v_rel f (RefPtr _ _) _’ mp_tac
    >> simp [Once v_rel_cases] >> strip_tac
    >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
    >> ‘fmap_inj f’ by gvs [state_rel_def]
    >> qpat_assum ‘state_ref_rel f s.refs s'.refs’
         (strip_assume_tac o REWRITE_RULE [state_ref_rel_def])
    >> first_x_assum drule >> strip_tac
    >> gvs [ref_rel_cases]
    >> simp [bvl_to_bvi_refs] >> qexists ‘f’
    >> simp [only_fresh_refl, bvlSemTheory.Unit_def]
    >> rpt conj_tac
    >-
     (gvs [bvlSemTheory.bad_thunk_update_def]
      >> rw []
      >> imp_res_tac dest_thunk_not_thunk_rel)
    >- simp [Once v_rel_cases]
    >- (gvs [state_rel_def] >> irule state_ref_rel_update >> simp
      [ref_rel_cases])
    >-
     (gvs [holes_unchanged_except_def, FLOOKUP_SIMP]
      >> rw [] >> gvs [IN_FRANGE_FLOOKUP] >> metis_tac [])
    >> irule holes_still_not_finalised_frange_update
    >> first_assum $ irule_at Any)
*)
  (* AllocThunk *)
(* HOL4 ML code, not ported:
  >> qmatch_goalsub_rename_tac ‘Thunk mode v'’
  >> simp [bvl_to_bvi_refs]
  >> qexists ‘f⟨(LEAST ptr. ptr ∉ FDOM s.refs) ↦ (LEAST ptr. ptr ∉ FDOM
    s'.refs)⟩’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘(LEAST ptr. ptr ∉ FDOM s'.refs) ∉ FRANGE f’
       by (irule fresh_not_in_range_f >> first_assum $ irule_at Any)
  >> drule state_rel_alloc
  >> disch_then $ qspecl_then
       [‘LEAST ptr. ptr ∉ FDOM s.refs’, ‘LEAST ptr. ptr ∉ FDOM s'.refs’,
        ‘Thunk mode v'’, ‘Thunk mode y’] mp_tac
  >> impl_tac
  >- (simp [fresh_ptr_fresh, ref_rel_cases]
      >> irule v_rel_submap >> first_assum $ irule_at Any
      >> simp [SUBMAP_FUPDATE_FLOOKUP, FLOOKUP_DEF]
      >> gvs [state_ref_rel_def, fresh_ptr_fresh])
  >> strip_tac >> simp [Once v_rel_cases]
  >> gvs [bvlSemTheory.bad_thunk_update_def]
      >> rw []
  >> imp_res_tac dest_thunk_not_thunk_rel
QED
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[FFI]:
  gvs [do_app_def, do_app_aux_def, bvlSemTheory.do_app_def, AllCaseEqs
    (), v_rel_cases]
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘s'.ffi = s.ffi’ by gvs [state_rel_def]
  >> fs [state_ref_rel_def]
  >> res_tac
  >> gvs [ref_rel_cases]
  >> qexists ‘f’
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> simp [bvl_to_bvi_def, bvi_to_bvl_def, only_fresh_refl,
    bvlSemTheory.Unit_def]
  >> conj_tac
  >- (‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
      >> gvs [state_rel_def]
      >> irule state_ref_rel_update
      >> simp [ref_rel_cases]
      >> first_assum $ irule_at Any)
  >> gvs [holes_unchanged_except_def, FLOOKUP_SIMP]
  >> conj_tac
  >- (rw [] >> gvs [IN_FRANGE_FLOOKUP] >> metis_tac [])
  >> irule holes_still_not_finalised_frange_update
  >> first_assum $ irule_at Any
QED
*)

(* Structural block operations with a fresh, state-preserving result
   (Cons, TagLenEq, LenEq, TagEq, LengthBlock, BoolTest,
     BoundsCheckBlock,
   EqualConst on a Number/Word64). *)
(* HOL4 ML code, not ported:
val block_simple_tac =
  qexists ‘f’
  >> rpt (qpat_x_assum ‘v_rel f _ _’ (strip_assume_tac o
    ONCE_REWRITE_RULE [v_rel_cases]))
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> imp_res_tac LIST_REL_LENGTH
  >> gvs [bvlSemTheory.Boolv_def]
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def];
*)

(* ElemAt reading an element out of a Block value. *)
(* HOL4 ML code, not ported:
val block_el_block_tac =
  qexists ‘f’
  >> qpat_x_assum ‘v_rel f (Block _ _) _’ (strip_assume_tac o
    ONCE_REWRITE_RULE [v_rel_cases])
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> qmatch_asmsub_rename_tac ‘LIST_REL (v_rel f) aa bb’
  >> imp_res_tac LIST_REL_LENGTH >> gvs []
  >> ‘v_rel f (EL n aa) (EL n bb)’ by gvs [LIST_REL_EL_EQN]
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl];
*)

(* ElemAt reading an element out of a ValueArray reference. *)
(* HOL4 ML code, not ported:
val block_el_ref_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> qpat_x_assum ‘v_rel f (RefPtr _ _) _’ (strip_assume_tac o
    ONCE_REWRITE_RULE [v_rel_cases])
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> drule_all state_ref_rel_lookup >> strip_tac >> gvs [ref_rel_cases]
  >> qmatch_asmsub_rename_tac ‘LIST_REL (v_rel f) aa bb’
  >> imp_res_tac LIST_REL_LENGTH >> gvs []
  >> ‘v_rel f (EL n aa) (EL n bb)’ by gvs [LIST_REL_EL_EQN]
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl];
*)

(* ConsExtend: result is an append of (a prefix of) two related blocks.
   *)
(* HOL4 ML code, not ported:
val block_consextend_tac =
  qexists ‘f’
  >> qpat_x_assum ‘v_rel f (Block _ _) _’ (strip_assume_tac o
    ONCE_REWRITE_RULE [v_rel_cases])
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> rpt (qpat_x_assum ‘v_rel f (Number _) _’ (strip_assume_tac o
    ONCE_REWRITE_RULE [v_rel_cases]))
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> imp_res_tac LIST_REL_LENGTH >> gvs []
  >> simp [Once v_rel_cases]
  >> irule EVERY2_APPEND_suff >> conj_tac
  >> ((irule EVERY2_TAKE >> irule EVERY2_DROP >> gvs []) ORELSE gvs []);
*)

(* FromList: convert a list value to a packed Block. *)
(* HOL4 ML code, not ported:
val block_fromlist_tac =
  qexists ‘f’
  >> qpat_x_assum ‘v_rel f (Number _) _’ (strip_assume_tac o
    ONCE_REWRITE_RULE [v_rel_cases])
  >> drule_all v_to_list_v_rel >> strip_tac
  >> imp_res_tac LIST_REL_LENGTH
  >> gvs [only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> simp [Once v_rel_cases];
*)

(* ListAppend: append two lists. *)
(* HOL4 ML code, not ported:
val block_listappend_tac =
  qexists ‘f’
  >> imp_res_tac v_to_list_v_rel
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> irule list_to_v_v_rel >> irule EVERY2_APPEND_suff >> gvs [];
*)

(* Equal: structural equality preserved by the renaming (uses
   do_eq_v_rel). *)
(* HOL4 ML code, not ported:
val block_equal_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> qspecl_then [‘s.refs’,‘x1'’,‘x2'’,‘s'.refs’,‘y’,‘y'’] mp_tac (cj 1
    do_eq_v_rel)
  >> impl_tac >- gvs []
  >> strip_tac
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def];
*)

(* EqualConst on a string constant (a compare-by-contents byte array).
   *)
(* HOL4 ML code, not ported:
val block_equalconst_ba_tac =
  qexists ‘f’
  >> ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> qpat_x_assum ‘v_rel f (RefPtr _ _) _’ (strip_assume_tac o
    ONCE_REWRITE_RULE [v_rel_cases])
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> drule_all state_ref_rel_lookup >> strip_tac >> gvs [ref_rel_cases]
  >> gvs [bvl_to_bvi_id, only_fresh_refl, holes_unchanged_except_refl,
    holes_still_not_finalised_refl]
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def];
*)

(* Build: evaluate a constant, possibly allocating byte arrays for
   strings. *)
(* HOL4 ML code, not ported:
val block_build_tac =
  ‘state_ref_rel f s.refs s'.refs’ by gvs [state_rel_def]
  >> ‘fmap_inj f’ by gvs [state_rel_def]
  >> Cases_on ‘do_build_const l s.refs’ >> gvs []
  >> drule_all do_build_const_v_rel >> strip_tac
  >> simp [bvl_to_bvi_refs]
  >> qexists ‘f'’ >> simp [bvl_to_bvi_refs]
  >> gvs [state_rel_def]
  >> gvs [OPTREL_def] >> imp_res_tac FLOOKUP_SUBMAP >> gvs [];
*)

(* BoolNot: negates a boolean; the argument value is a Boolv, equal on
   both
   sides, so the negation agrees. *)
(* HOL4 ML code, not ported:
val block_boolnot_tac =
  qexists ‘f’
  >> qpat_x_assum ‘v_rel f _ y’ mp_tac
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def]
  >> strip_tac
  >> gvs [bvlSemTheory.Boolv_def, bvl_to_bvi_id, only_fresh_refl,
    holes_unchanged_except_refl, holes_still_not_finalised_refl]
  >> simp [Once v_rel_cases, bvlSemTheory.Boolv_def];
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[BlockOp]:
  Cases_on ‘b’
  >> gvs [do_app_def, do_app_aux_def, AllCaseEqs (),
    bvlSemTheory.do_app_def,
          no_mutcons_op_def]
  >> FIRST [block_simple_tac >> NO_TAC, block_el_block_tac >> NO_TAC,
            block_el_ref_tac >> NO_TAC, block_consextend_tac >> NO_TAC,
            block_fromlist_tac >> NO_TAC, block_listappend_tac >>
              NO_TAC,
            block_equal_tac >> NO_TAC, block_equalconst_ba_tac >>
              NO_TAC,
            block_build_tac >> NO_TAC, block_boolnot_tac >> NO_TAC]
QED
*)

(* HOL4 ML code, not ported:
Resume do_app_op_rel[Install]:
  gvs [do_app_def, do_install_def, AllCaseEqs (), PULL_EXISTS]
  >> qpat_x_assum `v_rel f (Number (&LENGTH bytes)) _`
       (strip_assume_tac o ONCE_REWRITE_RULE [v_rel_cases])
  >> qpat_x_assum `v_rel f (Number (&LENGTH data)) _`
       (strip_assume_tac o ONCE_REWRITE_RULE [v_rel_cases])
  >> gvs []
  >> drule_all v_to_bytes_v_rel >> strip_tac
  >> drule_all v_to_words_v_rel >> strip_tac
  >> gvs []
  >> `s'.compile_oracle = state_co compile_each s.compile_oracle ∧
      s.compile = state_cc compile_each s'.compile ∧
      state_ref_rel f s.refs s'.refs ∧ s'.clock = s.clock ∧
      OPTREL (λp p'. FLOOKUP f p = SOME p') s.global s'.global ∧
      s'.ffi = s.ffi ∧ code_rel s.code s'.code ∧
      namespace_rel s.code s'.code ∧ fmap_inj f ∧
      (∀n. let ((next,cfg),prog) = s.compile_oracle n in
              input_condition next prog) ∧
      (∀n. n ∈ domain s'.code ∧ in_ns_3 n ⇒ n < FST (FST
        (s.compile_oracle 0)))`
       by fs [state_rel_def]
  >> Cases_on `s.compile_oracle 0` >> PairCases_on `q`
  >> rename1 `s.compile_oracle 0 = ((state0,cfg),progs0)`
  >> gvs [backendPropsTheory.state_co_def,
    backendPropsTheory.state_cc_def,
          miscTheory.shift_seq_def]
  >> Cases_on `compile_each state0 progs0`
  >> rename1 `compile_each state0 progs0 = (state1,progs1)`
  >> gvs [AllCaseEqs ()]
  >> `∃w rest. progs1 = (k,w)::rest` by
       (qpat_x_assum `compile_each state0 ((k,prog)::v7) = _` mp_tac
        >> PairCases_on `prog` >> simp [bvi_tmcTheory.compile_each_def]
        >> rpt (pairarg_tac >> simp []) >> CASE_TAC >> simp [] >> rw []
        >> Cases_on `x` >> gvs [])
  >> gvs []
  >> qexists `f` >> gvs []
  >> `input_condition state0 ((k,prog)::v7)` by
       (qpat_x_assum `∀n. (λ((next,cfg),prog). input_condition next
         prog) _`
          (qspec_then `0` mp_tac) >> simp [])
  >> `in_ns_3 state0 ∧ bvl_num_stubs ≤ state0` by gvs
    [input_condition_def]
  >> `ALL_DISTINCT (MAP FST ((k,w)::rest))` by
       (irule (cj 1 compile_each_ALL_DISTINCT)
        >> first_x_assum (irule_at Any) >> gvs [input_condition_def])
  >> `code_rel (fromAList ((k,prog)::v7)) (fromAList ((k,w)::rest))` by
       (irule compile_each_code_rel
        >> first_x_assum (irule_at Any) >> gvs [input_condition_def])
  >> `namespace_rel (fromAList ((k,prog)::v7)) (fromAList
    ((k,w)::rest))` by
       (irule compile_each_namespace_rel
        >> first_x_assum (irule_at Any) >> gvs [input_condition_def])
  >> `DISJOINT (domain s.code) (set (MAP FST ((k,prog)::v7)))` by
       (simp [] >> gvs [pred_setTheory.IN_DISJOINT] >> metis_tac [])
  >> `∀nm. in_ns_3 nm ∧ bvl_num_stubs ≤ nm ⇒
            ¬MEM nm (MAP FST ((k,prog)::v7))` by
       (rw [] >> CCONTR_TAC >> gvs [MEM_MAP]
        >> gvs [input_condition_def, EVERY_MEM, MEM_FILTER]
        >> qpat_x_assum `∀e. bvl_num_stubs ≤ FST e ∧ _ ⇒ _ MOD _ ≠ 3`
             (qspec_then `(k,prog)` mp_tac) >> gvs [])
  >> `DISJOINT (domain s'.code) (set (MAP FST ((k,w)::rest)))` by
       (qabbrev_tac `qq = (k,prog)::v7` >> qabbrev_tac `pp =
         (k,w)::rest`
        >> fs [pred_setTheory.IN_DISJOINT]
        >> qx_gen_tac `nn` >> spose_not_then strip_assume_tac
        >> Cases_on `in_ns_3 nn ∧ bvl_num_stubs ≤ nn`
        >- (`¬MEM nn (MAP FST qq)` by metis_tac []
            >> drule (GEN_ALL compile_each_MEM) >> disch_then drule >>
              simp []
            >> CCONTR_TAC >> fs [] >> res_tac >> fs [])
        >> qpat_x_assum `namespace_rel s.code s'.code` mp_tac
        >> simp [namespace_rel_def] >> spose_not_then strip_assume_tac
        >> `nn ∈ domain s.code` by metis_tac [NOT_LESS]
        >> drule (GEN_ALL compile_each_MEM) >> disch_then drule
        >> strip_tac >- metis_tac []
        >> fs [backend_commonTheory.bvl_to_bvi_namespaces_def]
        >> res_tac >> fs [])
  >> rpt conj_tac
  >- (qpat_x_assum `DISJOINT (domain s'.code) (set (MAP FST
    ((k,w)::rest)))`
        mp_tac >> simp [] >> rw [])
  >- (qpat_x_assum `DISJOINT (domain s'.code) (set (MAP FST
    ((k,w)::rest)))`
        mp_tac >> simp [] >> rw [])
  >- (qpat_x_assum `ALL_DISTINCT (MAP FST ((k,w)::rest))` mp_tac >> simp
    [] >> rw [])
  >- (qpat_x_assum `ALL_DISTINCT (MAP FST ((k,w)::rest))` mp_tac >> simp
    [])
  >- (Cases_on `s.compile_oracle 1` >> PairCases_on `q`
      >> gvs [] >> pairarg_tac >> gvs [])
  >- simp [Once v_rel_cases]
  >- (simp [state_rel_def]
      >> rpt conj_tac
      >- simp [FUN_EQ_THM, backendPropsTheory.state_co_def]
      >- (simp [FUN_EQ_THM, backendPropsTheory.state_cc_def,
        FORALL_PROD]
          >> rpt (pairarg_tac >> gvs []) >> rw []
          >> rpt (pairarg_tac >> gvs []) >> rw [])
      >- (rewrite_tac [GSYM (cj 2 sptreeTheory.fromAList_def)]
          >> irule code_rel_union >> simp [domain_fromAList]
          >> qpat_x_assum
               `DISJOINT (domain s'.code) (set (MAP FST ((k,w)::rest)))`
                 mp_tac
          >> qpat_x_assum `code_rel (fromAList ((k,prog)::v7)) _` mp_tac
          >> qpat_x_assum `code_rel s.code s'.code` mp_tac
          >> simp [pred_setTheory.DISJOINT_SYM])
      >- (rewrite_tac [GSYM (cj 2 sptreeTheory.fromAList_def)]
          >> irule namespace_rel_union >> simp [domain_fromAList]
          >> qpat_x_assum
               `DISJOINT (domain s'.code) (set (MAP FST ((k,w)::rest)))`
                 mp_tac
          >> qpat_x_assum `namespace_rel (fromAList ((k,prog)::v7)) _`
            mp_tac
          >> qpat_x_assum `namespace_rel s.code s'.code` mp_tac
          >> simp [pred_setTheory.DISJOINT_SYM])
      >> qpat_x_assum `(state1,cfg1) = FST (s.compile_oracle 1)`
           (assume_tac o SYM)
      >> simp [domain_fromAList]
      >> imp_res_tac compile_each_next_mono
      >> rw []
      >- (res_tac >> simp [])
      >- (`k < bvl_num_stubs` by
            (CCONTR_TAC >> fs [NOT_LESS]
             >> qpat_x_assum
                  `∀nm. in_ns_3 nm ∧ bvl_num_stubs ≤ nm ⇒ nm ≠ k ∧ _`
                  (qspec_then `k` mp_tac) >> simp [])
          >> decide_tac)
      >> `MEM n (MAP FST ((k,w)::rest))` by simp []
      >> drule (GEN_ALL compile_each_MEM) >> disch_then drule >>
        strip_tac
      >- (Cases_on `bvl_num_stubs ≤ n`
          >- (qpat_x_assum `∀nm. in_ns_3 nm ∧ bvl_num_stubs ≤ nm ⇒ ¬MEM
            _ _`
                (qspec_then `n` mp_tac) >> simp [])
          >> fs [NOT_LESS_EQUAL] >> decide_tac)
      >> qpat_x_assum `n < state0 + bvl_to_bvi_namespaces * k'`
           (mp_tac o ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM])
      >> simp [])
  >- simp [only_fresh_refl]
  >> simp [holes_unchanged_except_refl, holes_still_not_finalised_refl]
QED
*)

(* HOL4 ML code, not ported:
Finalise do_app_op_rel;
*)

let is_block_op_cons_def = cake_define
  `is_block_op_cons op <=>
     (?block_tag.
       op = closLang_BlockOp (Cons block_tag))`;;

let optimised_code_def = cake_define
  `optimised_code loc loc_opt c1 c2 <=>
     (?arity body body_wrap body_work.
       sptree_lookup loc c1 = SOME (arity,body) /\
       sptree_lookup loc c2 = SOME (arity,body_wrap) /\
       sptree_lookup loc_opt c2 = SOME (arity + 2,body_work) /\
       rewrite_wrapper loc loc_opt arity body = SOME body_wrap /\
       rewrite_worker loc loc_opt arity (arity + 1) arity body =
         body_work)`;;

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[op_non_opt]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (rs,u)’]
  >> first_assum $ qspecl_then [‘xs’, ‘s’, ‘env’] mp_tac
  >> impl_tac >- gvs []
  >> disch_then drule
  >> drule_all env_rel_relax_opt
  >> strip_tac
  >> rpt $ disch_then drule
  >> impl_tac >- gvs [CaseEq "prod", CaseEq "result"]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac
  >> gvs [GSYM PULL_FORALL]
  >> rename [‘evaluate (xs,env2,s') = (rs',u')’]
  >> reverse $ Cases_on ‘rs’ >> gvs []
  >- (* Error evaluating args *)
   (rename [‘evaluate (xs,env2,s') = (Rerr e',t')’]
    >> qexists‘f''’
    >> gvs []
    >> strip_tac >> gvs []
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> gvs [evaluate_def, fill_hole_def, opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rename [‘LIST_REL (v_rel f'') vs vs'’]
  >> reverse $ Cases_on ‘do_app op (REVERSE vs) u’ >> gvs []
  >- (* FFI *)
   (qrefinel [‘_’, ‘f''’, ‘_’]
    >> drule do_app_err
    >> strip_tac >> gvs []
    >> rename [‘do_app (FFI i) (REVERSE vs) u = Rerr (Rabort (Rffi_error
      e))’]
    >> drule do_app_op_err_rel
    >> disch_then $ qspecl_then [‘REVERSE vs'’, ‘u'’, ‘f''’] mp_tac
    >> disch_then drule
    >> drule $ iffLR list_rel_reverse
    >> gvs []
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def, evaluate_def, fill_hole_def,
      opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rename [‘do_app _ (REVERSE vs) u = Rval v’]
  >> gvs [CaseEq "prod"]
  >> rename [‘do_app op _ _ = Rval (v,r)’]
  >> drule $ iffLR list_rel_reverse
  >> strip_tac
  >> drule_all do_app_op_rel
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> gvs []
  >> conj_asm1_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_asm1_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_asm1_tac
  >- imp_res_tac holes_unchanged_except_trans
  >> conj_asm1_tac
  >- imp_res_tac holes_still_not_finalised_trans
  >> rw []
  >- gvs [rewrite_wrapper_def]
  >> gvs [rewrite_worker_def]
  >> ho_match_mp_tac evaluate_fill_hole_val
  >> rpt $ first_assum $ irule_at Any
  >> gvs [evaluate_def]
QED
*)

let hypothesis_def = cake_define
  `hypothesis xs' (s'':(num#'gc,'ffi)bviSem_state) clock <=> clock
   s'' < clock ==>
   (!env1' r' t' opt' f' s'³' env2' loc'.
             evaluate (xs',env1',s'') = (r',t') /\
             bvi_tmcProof_env_rel opt' f' env1' env2' /\ EVERY (\x.
               no_mutcons x) xs' /\
             bvi_tmcProof_state_rel f' s'' s'³' /\
             (opt' ==> LENGTH xs' = 1) /\ ~(
             r' = Rerr (Rabort Rtype_error)) ==>
             (?t'' f'' r''.
               evaluate (xs',env2',s'³') = (r'',t'') /\
               result_rel (LIST_REL (v_rel f'')) (eor_rel f'') r' r''
                 /\
               bvi_tmcProof_state_rel f'' t' t'' /\ f' SUBMAP f'' /\
                 only_fresh f' f'' (refs s'³') /\
               holes_unchanged_except f' (refs s'³') (refs t'') {} /\
               holes_still_not_finalised f' (refs s'³') (refs t'') /\
               (!loc_opt.
                 optimised_code loc' loc_opt (code s'') (code s'³')
                   ==>
                 (!wrap.
                    LENGTH xs' = 1 /\
                    rewrite_wrapper loc' loc_opt (LENGTH env1') (HD
                      xs') = SOME wrap ==>
                    (?t_wrap f_wrap r_wrap.
                      evaluate ([wrap],env2',s'³') = (r_wrap,t_wrap)
                        /\
                      result_rel (LIST_REL (v_rel f_wrap)) (eor_rel
                        f_wrap) r'
                        r_wrap /\ bvi_tmcProof_state_rel f_wrap t'
                          t_wrap /\ f' SUBMAP f_wrap /\
                      only_fresh f' f_wrap (refs s'³') /\
                      holes_unchanged_except f' (refs s'³') (refs
                        t_wrap) {} /\
                      holes_still_not_finalised f' (refs s'³') (refs
                        t_wrap))) /\
                 (opt' ==>
                  (!hole_ptr.
                    (?c. hole_has_val f' env1' env2' (refs s'³') c)
                      /\
                    hole_not_finalised (refs s'³') hole_ptr /\ EL
                      (LENGTH env1')
                    env2' = RefPtr F hole_ptr ==>
                    (?r_work f_work t_work.
                      evaluate
                        ([rewrite_worker loc' loc_opt (LENGTH env1')
                            (LENGTH env1' + 1) (LENGTH env1') (HD
                              xs')],env2',s'³') =
                      (r_work,t_work) /\ opt_res_rel f_work r' r_work
                        /\
                      bvi_tmcProof_state_rel f_work t' t_work /\ f'
                        SUBMAP f_work /\
                      only_fresh f' f_work (refs s'³') /\
                      holes_unchanged_except f' (refs s'³') (refs
                        t_work) {hole_ptr} /\
                      holes_still_not_finalised f' (refs s'³') (refs
                        t_work) /\
                      (!res_v.
                        r' = Rval [res_v] ==>
                        (?res_v'.
                          mb_rel f_work (refs s'³') (refs t_work \\
                            hole_ptr) res_v res_v' /\
                          hole_has_val f' env1' env2' (refs
                            t_work) res_v'))))))))`;;

let alloc_hole_has_val_def = cake_define
  `alloc_hole_has_val f refs extras i_ptr c_idx c <=>
     (?hole_ptr tag left right.
       i_ptr < LENGTH extras /\ EL i_ptr
       extras = RefPtr F hole_ptr /\
       c_idx = LENGTH left /\
       small_enough_int (&(LENGTH left)) /\ ~(
       hole_ptr IN FRANGE f) /\
       FLOOKUP refs hole_ptr = SOME (bvlSem_MutBlock tag F left c
         right))`;;

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[call_block]:
*)
  (* Phase 1 theorem in s *)
(* HOL4 ML code, not ported:
  drule_then drule evaluate_bvi_to_cb
  >> impl_tac >- gvs []
  >> simp [Once evaluate_def]
  >> strip_tac
  >> gvs [CaseEq "prod"]
  >> rename [‘evaluate (bs,env,s) = (as,u)’]
*)
  (* Hypothesis on bs *)
(* HOL4 ML code, not ported:
  >> first_assum $ qspecl_then [‘bs’, ‘s’] mp_tac
  >> impl_tac
  >- (imp_res_tac bvi_to_cb_size >> gvs [])
  >> imp_res_tac env_rel_relax_opt
  >> imp_res_tac bvi_to_cb_no_mutcons
  >> rpt $ disch_then drule
  >> impl_tac
  >- (gvs [] >> spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac
  >> pop_assum kall_tac
  >> rename [‘evaluate (bs,env2,s') = (as',u')’]
  >> rename [‘f ⊑ f'’]
*)
  (* Phase 1 theorem in s' *)
(* HOL4 ML code, not ported:
  >> Cases_on ‘evaluate ([x],env2,s')’
  >> rename [‘evaluate ([x],env2,s') = (r',t')’]
  >> drule_then drule evaluate_bvi_to_cb
  >> impl_tac >- (imp_res_tac env_rel_length >> gvs [])
  >> simp [Once evaluate_def]
  >> strip_tac
  >> reverse $ gvs [CaseEq "result"]
  >- (* bs fails *)
   (rename [‘exc_rel (eor_rel f') e e'’]
    >> rpt $ first_assum $ irule_at Any
    >> rpt gen_tac
    >> strip_tac
    >> gvs [optimised_code_def]
    >> rw []
    >-
     (reverse $ imp_res_tac bvi_to_cb_cases
      >- gvs [rewrite_wrapper_def, bvi_to_cb_def]
      >> gvs [rewrite_wrapper_def, evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> reverse $ imp_res_tac bvi_to_cb_cases
    >-
     (gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def]
      >> rpt $ first_assum $ irule_at Any
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
*)
  (* Phase 2 theorem *)
(* HOL4 ML code, not ported:
  >> rename [‘LIST_REL (v_rel f') vs vs'’]
  >> qpat_x_assum ‘env_rel _ _ _ _’ kall_tac
  >> drule evaluate_cb
  >> drule_all env_rel_submap
  >> strip_tac
  >> drule_all env_rel_append
  >> strip_tac
  >> ntac 2 $ disch_then $ drule_at Any
  >> disch_then $ qspec_then ‘s.clock’ mp_tac
  >> impl_tac
  >-
   (irule_at Any wf_cb_expand
    >> imp_res_tac bvi_to_cb_wf
    >> first_assum $ irule_at Any
    >> imp_res_tac evaluate_IMP_LENGTH
    >> imp_res_tac evaluate_clock
    >> gvs [LENGTH_APPEND]
    >> gvs [hypothesis_def, LENGTH_APPEND])
  >> strip_tac
  >> gvs []
  >> rpt $ first_assum $ irule_at Any
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_tac
  >- imp_res_tac holes_unchanged_except_trans
  >> conj_tac
  >- imp_res_tac holes_still_not_finalised_trans
  >> gen_tac
  >> strip_tac
  >> drule_all evaluate_pres_opt_code
  >> strip_tac
  >> first_x_assum $ drule
  >> gvs []
  >> rw []
  >-
   (reverse $ imp_res_tac bvi_to_cb_cases
    >- gvs [rewrite_wrapper_def]
    >> rename [‘CallBlock _ left _ right’]
    >> gvs [rewrite_wrapper_def, evaluate_def]
    >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> conj_tac
    >- imp_res_tac holes_unchanged_except_trans
    >> imp_res_tac holes_still_not_finalised_trans)
  >> reverse $ imp_res_tac bvi_to_cb_cases
  >-
   (gvs [rewrite_worker_def, evaluate_def]
    >> imp_res_tac evaluate_IMP_LENGTH
    >> gvs []
    >> first_x_assum $ qspec_then ‘hole_ptr’ mp_tac
    >> impl_tac
    >-
     (conj_tac
      >-
       (irule_at Any hole_has_val_append
        >> imp_res_tac env_rel_strip_extras
        >> gvs []
        >> irule_at Any unchanged_hole_has_val
        >> rpt $ first_assum $ irule_at Any
        >> gvs [])
      >> conj_tac
      >-
       (imp_res_tac holes_still_not_finalised_def
        >> gvs [hole_has_val_def])
      >> gvs [EL_APPEND_EQN])
    >> strip_tac
    >> gvs []
    >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> rpt $ first_assum $ irule_at Any
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> conj_tac
    >- imp_res_tac holes_still_not_finalised_trans
    >> rw []
    >> irule_at Any mb_rel_refs_old_subset
    >> first_assum $ irule_at Any
    >> conj_tac
    >- imp_res_tac evaluate_refs_SUBSET
    >> irule hole_has_val_submap
    >> drule_all hole_has_val_unappend
    >> strip_tac
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [rewrite_worker_def, evaluate_def]
  >> imp_res_tac evaluate_IMP_LENGTH
  >> gvs []
  >> first_x_assum $ qspec_then ‘hole_ptr’ mp_tac
  >> impl_tac
  >-
   (conj_tac
    >-
     (irule_at Any hole_has_val_append
      >> imp_res_tac env_rel_strip_extras
      >> gvs []
      >> irule_at Any unchanged_hole_has_val
      >> rpt $ first_assum $ irule_at Any
      >> gvs [])
    >> conj_tac
    >-
     (imp_res_tac holes_still_not_finalised_def
      >> gvs [hole_has_val_def])
    >> gvs [EL_APPEND_EQN])
  >> strip_tac
  >> gvs []
  >> rpt $ first_assum $ irule_at Any
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> conj_tac
  >- imp_res_tac holes_still_not_finalised_trans
  >> rw []
  >> irule_at Any mb_rel_refs_old_subset
  >> first_assum $ irule_at Any
  >> conj_tac
  >- imp_res_tac evaluate_refs_SUBSET
  >> irule hole_has_val_submap
  >> drule_all hole_has_val_unappend
  >> strip_tac
  >> first_assum $ irule_at Any
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[list]:
  gvs [evaluate_def]
*)
  (* First inductive hypothesis *)
(* HOL4 ML code, not ported:
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename[‘evaluate ([x],env,s) = (rx,u)’]
  >> first_assum $ qspecl_then [‘[x]’, ‘s’, ‘env’] mp_tac
  >> impl_tac
  >- gvs []
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> fs [])
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> gvs []
  >> pop_assum kall_tac
  >> rename [‘evaluate ([x],env2,s') = (rx',u')’]
  >> reverse $ Cases_on ‘rx’ >> gvs []
  >- (first_x_assum $ irule_at Any >> fs [])
*)
  (* Second inductive hypothesis *)
(* HOL4 ML code, not ported:
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> qpat_x_assum ‘_ = _’ mp_tac
  >> rename [‘evaluate (y::xs,env,u) = (ry,w)’]
  >> strip_tac
  >> rename [‘LIST_REL (v_rel f'') vx vx'’]
  >> first_x_assum $ qspecl_then [‘y::xs’, ‘u’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [])
  >> imp_res_tac env_rel_submap
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> impl_tac
  >- gvs [CaseEq "result"]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac >> fs []
  >> rename [‘evaluate (y::xs,env2,u') = (ry',w')’]
  >> Cases_on ‘ry’ >> gvs []
  >-
   (rename [‘state_rel f3 t t'’]
    >> rename [‘LIST_REL (v_rel f3) vy vy'’]
    >> qexists ‘f3’ >> fs []
    >> imp_res_tac evaluate_SING_IMP >> gvs []
    >> rename [‘v_rel f'' vx vx'’]
    >> drule_all v_rel_submap >> rw []
    >- imp_res_tac SUBMAP_TRANS
    >-
     (irule only_fresh_trans
      >> rpt $ goal_assum $ drule_at Any
      >> irule evaluate_refs_SUBSET
      >> goal_assum $ drule_at Any)
    >-
     (irule holes_unchanged_except_trans
      >> rpt $ goal_assum $ drule_at Any)
    >> imp_res_tac holes_still_not_finalised_trans)
  >> rename [‘state_rel f3 t t'’]
  >> qexists ‘f3’ >> fs []
  >> rw []
  >- imp_res_tac SUBMAP_TRANS
  >-
   (irule only_fresh_trans
    >> rpt $ goal_assum $ drule_at Any
    >> irule evaluate_refs_SUBSET
    >> goal_assum $ drule_at Any)
  >-
   (irule holes_unchanged_except_trans
    >> rpt $ goal_assum $ drule_at Any)
  >> imp_res_tac holes_still_not_finalised_trans
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[var]:
  gvs [evaluate_def]
  >> Cases_on ‘n < LENGTH env1’ >> gvs []
  >> ‘n < LENGTH env2’ by (drule_all env_rel_length >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> drule_all env_rel_el_v_rel
  >> strip_tac
  >> first_assum $ irule_at Any
  >> gvs []
  >> conj_asm1_tac
  >- irule only_fresh_refl
  >> conj_asm1_tac
  >- irule holes_unchanged_except_refl
  >> conj_asm1_tac
  >- irule holes_still_not_finalised_refl
  >> strip_tac
  >> gvs [rewrite_wrapper_def]
  >> rw []
  >> gvs [rewrite_worker_def]
  >> ho_match_mp_tac evaluate_fill_hole_val
  >> gvs [evaluate_def]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[if]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x1],env,s) = (r1,u)’]
*)
  (* First inductive hypothesis *)
(* HOL4 ML code, not ported:
  >> first_assum $ qspecl_then [‘[x1]’, ‘s’] mp_tac
  >> impl_tac >- gvs []
  >> imp_res_tac env_rel_relax_opt
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> impl_tac >- gvs [CaseEq "result"]
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> pop_assum kall_tac
  >> gvs []
  >> Cases_on ‘r1’ >> gvs []
  >-
   (imp_res_tac evaluate_SING_IMP
    >> gvs []
    >> rename [‘state_rel f' u u'’]
    >> rename [‘v_rel f' v1 v1'’]
    >> Cases_on ‘v1 = Boolv T’ >> gvs []
    >- (* Then inductive hypothesis *)
     (‘v1' = Boolv T’ by (drule $ iffLR v_rel_cases >> gvs
       [bvlSemTheory.Boolv_def])
      >> gvs []
      >> first_x_assum $ qspecl_then [‘[x2]’, ‘u’] mp_tac
      >> impl_tac >- (imp_res_tac evaluate_clock >> gvs [])
      >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
      >> imp_res_tac env_rel_submap
      >> asm_simp_tac std_ss [EVERY_DEF]
      >> rpt $ disch_then drule
      >> disch_then $ qspec_then ‘loc’ mp_tac
      >> impl_tac >- gvs []
      >> strip_tac
      >> qexistsl [‘t''’, ‘f''’, ‘r''’]
      >> gvs [GSYM PULL_FORALL]
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> goal_assum $ drule_at $ Pos $ el 2
        >> goal_assum $ drule_at Any
        >> irule evaluate_refs_SUBSET
        >> qexistsl [‘env2’, ‘Rval [Boolv T]’, ‘[x1]’]
        >> gvs [])
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs [])
      >> conj_tac
      >- imp_res_tac holes_still_not_finalised_trans
      >> gen_tac
      >> strip_tac
      >> gvs []
      >> drule_all evaluate_pres_opt_code
      >> strip_tac
      >> first_x_assum drule
      >> strip_tac
      >> gvs []
      >> rw []
      >-
       (drule wrapper_strip_if_then
        >> strip_tac
        >-
         (gvs [evaluate_def]
          >> rpt $ first_assum $ irule_at Any
          >> conj_tac
          >- imp_res_tac SUBMAP_TRANS
          >> conj_tac
          >-
           (irule only_fresh_trans
            >> rpt $ first_assum $ irule_at Any
            >> imp_res_tac evaluate_refs_SUBSET)
          >> conj_tac
          >- imp_res_tac holes_unchanged_except_trans
          >> imp_res_tac holes_still_not_finalised_trans)
        >> gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at Any
          >> imp_res_tac evaluate_refs_SUBSET)
        >> conj_tac
        >- imp_res_tac holes_unchanged_except_trans
        >> imp_res_tac holes_still_not_finalised_trans)
      >> gvs []
      >> first_x_assum $ qspecl_then [‘c’] mp_tac
      >> impl_tac
      >-
       (drule env_rel_strip_extras
        >> strip_tac
        >> gvs []
        >> conj_tac
        >-
         (irule unchanged_hole_has_val
          >> qexists ‘EMPTY’
          >> gvs []
          >> first_assum $ irule_at $ Pos hd
          >> gvs [])
        >> ntac 2 $ imp_res_tac holes_still_not_finalised_def
        >> gvs [hole_has_val_def])
      >> strip_tac
      >> gvs [rewrite_worker_def, evaluate_def]
      >> imp_res_tac env_rel_length_opt
      >> gvs [EL_APPEND_EQN]
      >> first_assum $ irule_at Any
      >> gvs []
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs []
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> conj_tac
      >- imp_res_tac holes_still_not_finalised_trans
      >> rw []
      >> irule_at Any mb_rel_refs_old_subset
      >> first_assum $ irule_at Any
      >> conj_tac
      >- imp_res_tac evaluate_refs_SUBSET
      >> irule hole_has_val_submap
      >> first_assum $ irule_at Any
      >> gvs [])
*)
    (* Else inductive hypothesis *)
(* HOL4 ML code, not ported:
    >> Cases_on ‘v1 = Boolv F’ >> gvs []
    >> ‘v1' = Boolv F’ by (drule $ iffLR v_rel_cases >> gvs
      [bvlSemTheory.Boolv_def])
    >> gvs []
    >> first_x_assum $ qspecl_then [‘[x3]’, ‘u’] mp_tac
    >> impl_tac >- (imp_res_tac evaluate_clock >> gvs [])
    >> qpat_x_assum ‘env_rel F _ _ _’ kall_tac
    >> imp_res_tac env_rel_submap
    >> asm_simp_tac std_ss [EVERY_DEF]
    >> rpt $ disch_then drule
    >> disch_then $ qspec_then ‘loc’ mp_tac
    >> impl_tac >- gvs []
    >> strip_tac
    >> qexistsl [‘t''’, ‘f''’, ‘r''’]
    >> gvs [GSYM PULL_FORALL]
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> goal_assum $ drule_at $ Pos $ el 2
      >> goal_assum $ drule_at Any
      >> irule evaluate_refs_SUBSET
      >> qexistsl [‘env2’, ‘Rval [Boolv F]’, ‘[x1]’]
      >> gvs [])
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at Any
      >> gvs [])
    >> conj_tac
    >- imp_res_tac holes_still_not_finalised_trans
    >> gen_tac
    >> strip_tac
    >> gvs []
    >> drule_all evaluate_pres_opt_code
    >> strip_tac
    >> first_x_assum drule
    >> strip_tac
    >> gvs []
    >> rw []
    >-
     (drule wrapper_strip_if_else
      >> strip_tac
      >-
       (gvs [evaluate_def]
        >> rpt $ first_assum $ irule_at Any
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at Any
          >> imp_res_tac evaluate_refs_SUBSET)
        >> conj_tac
        >- imp_res_tac holes_unchanged_except_trans
        >> imp_res_tac holes_still_not_finalised_trans)
      >> gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
      >> conj_tac
      >- imp_res_tac holes_unchanged_except_trans
      >> imp_res_tac holes_still_not_finalised_trans)
    >> gvs []
    >> first_x_assum $ qspecl_then [‘c’] mp_tac
    >> impl_tac
    >-
     (drule env_rel_strip_extras
      >> strip_tac
      >> gvs []
      >> conj_tac
      >-
       (irule unchanged_hole_has_val
        >> qexists ‘EMPTY’
        >> gvs []
        >> first_assum $ irule_at $ Pos hd
        >> gvs [])
      >> ntac 2 $ imp_res_tac holes_still_not_finalised_def
      >> gvs [hole_has_val_def])
    >> strip_tac
    >> gvs [rewrite_worker_def, evaluate_def]
    >> imp_res_tac env_rel_length_opt
    >> gvs [EL_APPEND_EQN]
    >> first_assum $ irule_at Any
    >> gvs []
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >> conj_tac
    >-
     (irule holes_unchanged_except_trans
      >> first_assum $ irule_at Any
      >> gvs []
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
    >> conj_tac
    >- imp_res_tac holes_still_not_finalised_trans
    >> rw []
    >> irule_at Any mb_rel_refs_old_subset
    >> first_assum $ irule_at Any
    >> conj_tac
    >- imp_res_tac evaluate_refs_SUBSET
    >> irule hole_has_val_submap
    >> first_assum $ irule_at Any
    >> gvs [])
*)
  (* Error case *)
(* HOL4 ML code, not ported:
  >> gvs []
  >> ‘e' ≠ Rabort Rtype_error’ by (spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
  >> rw []
  >-
   (drule wrapper_strip_if_then
    >> strip_tac
    >-
     (gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> gvs [evaluate_def]
    >> rpt $ first_assum $ irule_at Any)
  >> gvs [rewrite_worker_def, evaluate_def]
  >> first_assum $ irule_at Any
  >> conj_tac
  >- gvs [opt_res_rel_def]
  >> gvs []
  >> irule holes_unchanged_except_subset
  >> first_assum $ irule_at Any
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[lett]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (rs,u)’]
*)
  (* First inductive hypothesis *)
(* HOL4 ML code, not ported:
  >> first_assum $ qspecl_then [‘xs’, ‘s’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [])
  >> imp_res_tac env_rel_relax_opt
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> impl_tac
  >- gvs [CaseEq "result"]
  >> pop_assum kall_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> pop_assum kall_tac
  >> reverse $ gvs [CaseEq "result"]
  >-
   (gvs [GSYM PULL_FORALL]
    >> first_assum $ irule_at Any
    >> gvs []
    >> rw []
    >-
     (drule wrapper_strip_let
      >> strip_tac
      >> gvs [evaluate_def]
      >> rpt $ first_assum $ irule_at Any)
    >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def]
    >> rpt $ first_assum $ irule_at Any
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rename [‘evaluate (_,_,_) = (Rval vs',u')’, ‘LIST_REL (v_rel f') _
    _’]
  >> gvs []
*)
  (* Second inductive hypothesis *)
(* HOL4 ML code, not ported:
  >> first_x_assum $ qspecl_then [‘[x2]’, ‘u’] mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [])
  >> imp_res_tac env_rel_submap
  >> imp_res_tac env_rel_append
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> impl_tac
  >- gvs [LENGTH_APPEND]
  >> strip_tac
  >> rename [‘evaluate (_,_,_) = (r',t')’]
  >> gvs [GSYM PULL_FORALL]
  >> first_assum $ irule_at Any
  >> gvs []
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET
    >> gvs [])
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> first_assum $ irule_at Any
    >> gvs [])
  >> conj_tac
  >- imp_res_tac holes_still_not_finalised_trans
  >> gen_tac
  >> strip_tac
  >> first_x_assum $ qspec_then ‘loc_opt’ mp_tac
  >> impl_tac
  >- imp_res_tac evaluate_pres_opt_code
  >> strip_tac
  >> rw []
  >-
   (imp_res_tac evaluate_IMP_LENGTH
    >> gvs [rewrite_wrapper_def, CaseEq "option"]
    >> gvs [evaluate_def]
    >> first_assum $ irule_at Any
    >> gvs []
    >> conj_tac
    >- imp_res_tac SUBMAP_TRANS
    >> conj_tac
    >-
     (irule only_fresh_trans
      >> first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET
      >> gvs [])
    >> conj_tac
    >- imp_res_tac holes_unchanged_except_trans
    >> imp_res_tac holes_still_not_finalised_trans)
  >> gvs []
  >> first_x_assum $ qspecl_then [‘hole_ptr’, ‘c’] mp_tac
  >> impl_tac
  >-
   (conj_tac
    >-
     (irule hole_has_val_append
      >> gvs []
      >> imp_res_tac env_rel_strip_extras
      >> gvs []
      >> irule unchanged_hole_has_val
      >> rpt $ first_assum $ irule_at Any
      >> gvs [])
    >> conj_tac
    >-
     (gvs [holes_still_not_finalised_def]
      >> first_x_assum $ irule
      >> gvs [hole_has_val_def])
    >> imp_res_tac env_rel_length_opt
    >> gvs [EL_APPEND_EQN])
  >> strip_tac
  >> gvs [rewrite_worker_def, evaluate_def]
  >> rpt $ first_assum $ irule_at Any
  >> imp_res_tac evaluate_IMP_LENGTH
  >> gvs []
  >> conj_tac
  >- imp_res_tac SUBMAP_TRANS
  >> conj_tac
  >-
   (irule only_fresh_trans
    >> rpt $ first_assum $ irule_at Any
    >> imp_res_tac evaluate_refs_SUBSET)
  >> conj_tac
  >-
   (irule holes_unchanged_except_trans
    >> first_assum $ irule_at Any
    >> gvs []
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> conj_tac
  >- imp_res_tac holes_still_not_finalised_trans
  >> rw []
  >> irule_at Any mb_rel_refs_old_subset
  >> first_assum $ irule_at Any
  >> conj_tac
  >- imp_res_tac evaluate_refs_SUBSET
  >> irule hole_has_val_submap
  >> imp_res_tac hole_has_val_unappend
  >> first_assum $ irule_at Any
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[raise]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate ([x],env,s) = (v,u)’]
  >> first_x_assum $ qspecl_then [‘[x]’, ‘s’, ‘env’] mp_tac
  >> impl_tac
  >- gvs []
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs []
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> gvs [PULL_EXISTS, GSYM PULL_FORALL]
  >> rpt $ first_assum $ irule_at Any
  >> reverse $ gvs [CaseEq "result"]
  >-
   (rw []
    >- gvs [evaluate_def, rewrite_wrapper_def]
    >> gvs [evaluate_def, rewrite_worker_def, opt_res_rel_def]
    >> first_assum $ irule_at Any
    >> gvs []
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> imp_res_tac evaluate_SING_IMP
  >> gvs []
  >> rw []
  >- gvs [evaluate_def, rewrite_wrapper_def]
  >> gvs [evaluate_def, rewrite_worker_def, opt_res_rel_def]
  >> first_assum $ irule_at Any
  >> gvs []
  >> irule holes_unchanged_except_subset
  >> first_assum $ irule_at Any
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[tick]:
  gvs [evaluate_def]
  >> ‘s'.clock = s.clock’ by gvs [state_rel_def]
  >> gvs []
  >> Cases_on ‘s.clock’
  >-
   (gvs [GSYM PULL_FORALL]
    >> rpt $ first_assum $ irule_at Any
    >> gvs []
    >> gvs [only_fresh_refl, holes_unchanged_except_refl,
      holes_still_not_finalised_refl]
    >> rw []
    >-
     (gvs [rewrite_wrapper_def, evaluate_def]
      >> rpt $ first_assum $ irule_at Any
      >> gvs [only_fresh_refl, holes_unchanged_except_refl,
        holes_still_not_finalised_refl])
    >> first_assum $ irule_at Any
    >> gvs [rewrite_worker_def, evaluate_def, opt_res_rel_def,
      holes_unchanged_except_refl, only_fresh_refl,
      holes_still_not_finalised_refl])
  >> gvs [GSYM PULL_FORALL]
  >> first_x_assum $ qspecl_then [‘[x]’, ‘dec_clock 1 s’] mp_tac
  >> impl_tac >- gvs [dec_clock_def]
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> drule state_rel_dec
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘1’ mp_tac
  >> impl_tac >- gvs []
  >> strip_tac
  >> disch_then drule
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> impl_tac >- gvs []
  >> strip_tac
  >> rename [‘evaluate ([x],env2,dec_clock 1 s') = (r',t')’]
  >> rpt $ first_assum $ irule_at Any
  >> gvs []
  >> gen_tac
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> rw []
  >-
   (gvs [rewrite_wrapper_def, evaluate_def]
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [rewrite_worker_def, evaluate_def, PULL_EXISTS]
  >> first_x_assum drule
  >> strip_tac
  >> gvs []
  >> first_assum $ irule_at Any
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[call_non_opt]:
  gvs [evaluate_def]
  >> IF_CASES_TAC >> gvs []
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (xs,env,s) = (v_xs,u)’]
*)
  (* xs inductive hypothesis *)
(* HOL4 ML code, not ported:
  >> first_assum $ qspecl_then [‘xs’, ‘s’] mp_tac
  >> impl_tac
  >- gvs []
  >> imp_res_tac env_rel_relax_opt
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> pop_assum kall_tac
  >> impl_tac
  >- (CCONTR_TAC >> gvs [])
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> pop_assum kall_tac
  >> rename [‘state_rel f' u u'’, ‘result_rel _ _ _ v_xs'’]
  >> reverse $ gvs [CaseEq "result"]
*)
  (* Error case *)
(* HOL4 ML code, not ported:
  >-
   (rename [‘evaluate (xs,env2,s') = (Rerr e',t')’, ‘exc_rel (eor_rel
     f') e _’]
    >> gvs [GSYM PULL_FORALL]
    >> rpt $ first_assum $ irule_at Any
    >> gen_tac
    >> strip_tac
    >> rw []
    >- gvs [evaluate_def, rewrite_wrapper_def]
    >> gvs [evaluate_def, rewrite_worker_def, fill_hole_def]
    >> IF_CASES_TAC
    >- gvs []
    >> gvs []
    >> rpt $ first_assum $ irule_at Any
    >> conj_tac
    >- gvs [opt_res_rel_def]
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [GSYM PULL_FORALL, CaseEq "option", CaseEq "prod"]
  >> drule_all find_code_rel
  >> strip_tac
  >> gvs []
  >> ‘u.clock = u'.clock’ by gvs [state_rel_def]
  >> IF_CASES_TAC
  >-
   (qexistsl [‘u' with clock := 0’, ‘f'’, ‘Rerr (Rabort
     Rtimeout_error)’]
    >> gvs [state_rel_with_clock]
    >> rw []
    >- gvs [rewrite_wrapper_def]
    >> gvs [rewrite_worker_def]
    >> gvs [evaluate_def, fill_hole_def]
    >> IF_CASES_TAC
    >- gvs []
    >> gvs []
    >> first_assum $ irule_at Any
    >> gvs [opt_res_rel_def, state_rel_with_clock]
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> gvs [CaseEq "prod"]
  >> first_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ticks + 1) u’]
    mp_tac
  >> impl_tac
  >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
  >> rpt $ disch_then drule
  >> drule state_rel_dec
  >> Cases_on ‘u.clock’
  >- gvs []
  >> gvs []
  >> disch_then $ qspec_then ‘ticks + 1’ mp_tac
  >> impl_tac
  >- gvs []
  >> strip_tac
  >> disch_then drule
  >> disch_then $ qspec_then ‘loc'’ mp_tac
  >> impl_tac
  >- gvs [CaseEq "result", CaseEq "error_result"]
  >> strip_tac
  >> Cases_on ‘exp = body'’
  >-
   (gvs []
    >> pop_assum kall_tac
    >> qmatch_asmsub_rename_tac ‘result_rel _ _ cres _’
    >> reverse $ Cases_on ‘∃v_raise h. cres = Rerr (Rraise (Exn
      v_raise)) ∧ handler = SOME h’
    >-
     (gvs []
      >> qexistsl [‘t''’, ‘f''’, ‘r''’]
      >> ‘(cres,s'') = (r,t) ∧ ∀vs. r ≠ Rerr (Rraise (Ret vs))’ by
        (Cases_on ‘cres’ >> gvs []
         >> every_case_tac >> gvs [])
      >> gvs []
      >> conj_tac
      >- (Cases_on ‘r''’ >> gvs [] >> every_case_tac >> gvs [])
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET)
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs []
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> conj_tac
      >- imp_res_tac holes_still_not_finalised_trans
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >-
       (gvs [rewrite_worker_def]
        >> ho_match_mp_tac evaluate_fill_hole
        >> rpt $ first_assum $ irule_at Any
        >> gvs [evaluate_def]
        >> IF_CASES_TAC
        >- gvs []
        >> gvs []
        >> conj_tac
        >-
         (Cases_on ‘cres’ >> gvs []
          >> every_case_tac >> gvs [])
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule holes_unchanged_except_trans
          >> first_assum $ irule_at Any
          >> gvs []
          >> irule holes_unchanged_except_subset
          >> first_assum $ irule_at Any
          >> gvs [])
        >> conj_tac
        >- imp_res_tac holes_still_not_finalised_trans
        >> irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any
        >> imp_res_tac evaluate_refs_SUBSET))
    >-
     (gvs []
      >> qmatch_asmsub_rename_tac ‘eor_rel _ (Exn v_raise) tv’
      >> Cases_on ‘tv’ >> gvs []
      >> rename [‘state_rel _ k k'’, ‘v_rel _ _ v_raise'’, ‘LIST_REL _
        vs vs'’]
      >> ‘env_rel opt f'' (v_raise::env) (v_raise'::env2)’ by
        (imp_res_tac env_rel_submap
         >> imp_res_tac env_rel_cons)
      >> Cases_on ‘evaluate ([h],v_raise::env,k)’ >> gvs []
      >> ‘q ≠ Rerr (Rabort Rtype_error) ∧ ∀vs. q ≠ Rerr (Rraise (Ret
        vs))’ by
        (Cases_on ‘q’ >> gvs [] >> every_case_tac >> gvs [])
      >> first_x_assum $ qspecl_then [‘[h]’, ‘k’] mp_tac
      >> impl_tac
      >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
      >> disch_then drule
      >> asm_simp_tac std_ss [EVERY_DEF]
      >> rpt $ disch_then drule
      >> impl_tac
      >- gvs []
      >> disch_then $ qspec_then ‘loc’ mp_tac
      >> strip_tac
      >> gvs []
      >> ‘(q,r') = (r,t)’ by (Cases_on ‘q’ >> gvs [] >> every_case_tac
        >> gvs [])
      >> gvs []
      >> qexistsl [‘t''’, ‘f'³'’, ‘r''’]
      >> conj_tac
      >- (Cases_on ‘r''’ >> gvs [] >> every_case_tac >> gvs [])
      >> rpt $ first_assum $ irule_at Any
      >> conj_asm1_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_asm1_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at $ Pos last
        >> imp_res_tac evaluate_refs_SUBSET
        >> gvs []
        >> conj_tac
        >- imp_res_tac SUBSET_TRANS
        >> irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any)
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at $ Pos last
        >> gvs []
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at $ Pos last
          >> imp_res_tac evaluate_refs_SUBSET)
        >> irule holes_unchanged_except_trans
        >> rpt $ first_assum $ irule_at $ Pos last)
      >> conj_tac
      >- imp_res_tac holes_still_not_finalised_trans
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole
      >> rpt $ first_assum $ irule_at Any
      >> gvs [evaluate_def]
      >> conj_tac
      >- (Cases_on ‘r''’ >> gvs [] >> every_case_tac >> gvs [])
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> rpt $ first_assum $ irule_at $ Pos last
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at $ Pos last
          >> imp_res_tac evaluate_refs_SUBSET)
        >> irule holes_unchanged_except_trans
        >> first_assum $ irule_at $ Pos last
        >> gvs [])
      >> imp_res_tac holes_still_not_finalised_trans))
  >-
   (gvs []
    >> first_x_assum drule
    >> disch_then drule
    >> strip_tac
    >> gvs []
    >> qmatch_asmsub_rename_tac ‘result_rel _ _ cres _’
    >> reverse $ Cases_on ‘∃v_raise h. cres = Rerr (Rraise (Exn
      v_raise)) ∧ handler = SOME h’
    >-
     (gvs []
      >> qexistsl [‘t_wrap’, ‘f_wrap’, ‘r_wrap’]
      >> ‘(cres,s'') = (r,t) ∧ ∀vs. r ≠ Rerr (Rraise (Ret vs))’ by
        (Cases_on ‘cres’ >> gvs [] >> every_case_tac >> gvs [])
      >> gvs []
      >> conj_tac
      >- (Cases_on ‘r_wrap’ >> gvs [] >> every_case_tac >> gvs [])
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at $ Pos last
        >> imp_res_tac evaluate_refs_SUBSET)
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at $ Pos last
        >> gvs [])
      >> conj_tac
      >- imp_res_tac holes_still_not_finalised_trans
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole
      >> rpt $ first_assum $ irule_at Any
      >> gvs [evaluate_def]
      >> IF_CASES_TAC
      >- gvs []
      >> gvs []
      >> conj_tac
      >- (Cases_on ‘r_wrap’ >> gvs [] >> every_case_tac >> gvs [])
      >> conj_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at Any
        >> gvs []
        >> irule holes_unchanged_except_subset
        >> first_assum $ irule_at Any
        >> gvs [])
      >> conj_tac
      >- imp_res_tac holes_still_not_finalised_trans
      >> irule only_fresh_trans
      >> rpt $ first_assum $ irule_at Any
      >> imp_res_tac evaluate_refs_SUBSET)
    >-
     (gvs []
      >> qmatch_asmsub_rename_tac ‘eor_rel _ (Exn v_raise) tv’
      >> Cases_on ‘tv’ >> gvs []
      >> rename [‘state_rel _ k k'’, ‘v_rel _ _ v_raise'’, ‘LIST_REL _
        vs vs'’]
      >> ‘env_rel opt f_wrap (v_raise::env) (v_raise'::env2)’ by
        (imp_res_tac env_rel_submap
         >> imp_res_tac env_rel_cons)
      >> Cases_on ‘evaluate ([h],v_raise::env,k)’ >> gvs []
      >> ‘q ≠ Rerr (Rabort Rtype_error) ∧ ∀vs. q ≠ Rerr (Rraise (Ret
        vs))’ by
        (Cases_on ‘q’ >> gvs [] >> every_case_tac >> gvs [])
      >> first_x_assum $ qspecl_then [‘[h]’, ‘k’] mp_tac
      >> impl_tac
      >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
      >> disch_then drule
      >> asm_simp_tac std_ss [EVERY_DEF]
      >> rpt $ disch_then drule
      >> impl_tac
      >- gvs []
      >> disch_then $ qspec_then ‘loc’ mp_tac
      >> strip_tac
      >> gvs []
      >> ‘(q,r') = (r,t)’ by (Cases_on ‘q’ >> gvs [] >> every_case_tac
        >> gvs [])
      >> gvs []
      >> qexistsl [‘t'³'’, ‘f'³'’, ‘r''’]
      >> conj_tac
      >- (Cases_on ‘r''’ >> gvs [] >> every_case_tac >> gvs [])
      >> rpt $ first_assum $ irule_at Any
      >> conj_asm1_tac
      >- imp_res_tac SUBMAP_TRANS
      >> conj_asm1_tac
      >-
       (irule only_fresh_trans
        >> rpt $ first_assum $ irule_at $ Pos last
        >> imp_res_tac evaluate_refs_SUBSET
        >> gvs []
        >> conj_tac
        >- imp_res_tac SUBSET_TRANS
        >> irule only_fresh_trans
        >> rpt $ first_assum $ irule_at Any)
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> first_assum $ irule_at $ Pos last
        >> gvs []
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at $ Pos last
          >> imp_res_tac evaluate_refs_SUBSET)
        >> irule holes_unchanged_except_trans
        >> rpt $ first_assum $ irule_at $ Pos last)
      >> conj_tac
      >- imp_res_tac holes_still_not_finalised_trans
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole
      >> rpt $ first_assum $ irule_at Any
      >> gvs [evaluate_def]
      >> conj_tac
      >- (Cases_on ‘r''’ >> gvs [] >> every_case_tac >> gvs [])
      >> conj_tac
      >-
       (irule holes_unchanged_except_trans
        >> rpt $ first_assum $ irule_at $ Pos last
        >> conj_tac
        >- imp_res_tac SUBMAP_TRANS
        >> conj_tac
        >-
         (irule only_fresh_trans
          >> rpt $ first_assum $ irule_at $ Pos last
          >> imp_res_tac evaluate_refs_SUBSET)
        >> irule holes_unchanged_except_trans
        >> first_assum $ irule_at $ Pos last
        >> gvs [])
      >> imp_res_tac holes_still_not_finalised_trans))
QED
*)

let dest_thunk_ret_rel_def = cake_define
  `dest_thunk_ret_rel f t1 t2 <=>
     ((t1 = BadRef /\ t2 = BadRef) \/
      (t1 = NotThunk /\ t2 = NotThunk) \/
      (?tm1 tm2 v1 v2.
        t1 = IsThunk tm1 v1 /\ t2 = IsThunk tm2 v2 /\
        tm1 = tm2 /\
        v_rel f v1 v2))`;;

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[force]:
  gvs [evaluate_def]
  >> imp_res_tac env_rel_length
  >> Cases_on ‘¬(n < LENGTH env1)’
  >- gvs []
  >> gvs [GSYM PULL_FORALL]
  >> imp_res_tac dest_thunk_rel
  >> gvs [dest_thunk_ret_rel_def, CaseEq "thunk_mode"]
  >- (first_assum $ irule_at Any
      >> gvs [only_fresh_refl, holes_unchanged_except_refl,
        holes_still_not_finalised_refl]
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> ho_match_mp_tac evaluate_fill_hole_val
      >> rpt $ first_assum $ irule_at Any
      >> gvs [evaluate_def, holes_unchanged_except_refl,
        only_fresh_refl, holes_still_not_finalised_refl])
  >> gvs [CaseEq "option", CaseEq "prod"]
  >> drule find_code_rel
  >> ‘LIST_REL (v_rel f) [EL n env1; v1] [EL n env2; v2]’ by
    (irule $ iffRL LIST_REL_EL_EQN
     >> gvs []
     >> rw []
     >> Cases_on ‘n'’
     >- (imp_res_tac env_rel_el >> gvs [])
     >> Cases_on ‘n''’
     >- gvs []
     >> gvs [])
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> strip_tac
  >> gvs []
  >> ‘s.clock = s'.clock’ by gvs [state_rel_def]
  >> IF_CASES_TAC
  >- (gvs []
      >> qexists ‘f’
      >> conj_tac
      >- gvs [state_rel_def]
      >> gvs [only_fresh_refl, holes_unchanged_except_refl,
        holes_still_not_finalised_refl]
      >> rw []
      >- gvs [rewrite_wrapper_def]
      >> gvs [rewrite_worker_def]
      >> gvs [evaluate_def, fill_hole_def]
      >> qexists ‘f’
      >> gvs [opt_res_rel_def, state_rel_def,
        holes_unchanged_except_refl, only_fresh_refl,
        holes_still_not_finalised_refl])
  >> gvs []
  >- (‘∃q u. evaluate ([exp],args,dec_clock 1 s) = (q,u)’ by
        (Cases_on ‘evaluate ([exp],args,dec_clock 1 s)’ >> gvs [])
      >> ‘(q,u) = (r,t) ∧ ∀vs. r ≠ Rerr (Rraise (Ret vs))’ by
        (Cases_on ‘q’ >> gvs [] >> every_case_tac >> gvs [])
      >> gvs []
      >> first_x_assum $ qspecl_then [‘[exp]’, ‘dec_clock 1 s’] mp_tac
      >> impl_tac >- gvs [dec_clock_def]
      >> asm_simp_tac std_ss [EVERY_DEF]
      >> rpt $ disch_then drule
      >> disch_then $ qspec_then ‘dec_clock 1 s'’ mp_tac
      >> impl_tac >- gvs [dec_clock_def, state_rel_def]
      >> disch_then $ qspec_then ‘loc'’ mp_tac
      >> strip_tac
      >> rename [‘state_rel f' t t'’, ‘result_rel _ _ _ r'’]
      >> Cases_on ‘exp = body'’
      >- (gvs []
          >> ‘(case r' of
                 Rval v6 => (Rval v6,t')
               | Rerr (Rraise (Exn v14)) => (Rerr (Rraise (Exn v14)),t')
               | Rerr (Rraise (Ret v15)) => (Rerr (Rabort
                 Rtype_error),t')
               | Rerr (Rabort v11) => (Rerr (Rabort v11),t')) = (r',t')’
                 by
             (Cases_on ‘q’ >> gvs [] >> every_case_tac >> gvs [])
          >> gvs []
          >> qexists ‘f'’
          >> gvs []
          >> rw []
          >- gvs [rewrite_wrapper_def]
          >> gvs [rewrite_worker_def]
          >> ho_match_mp_tac evaluate_fill_hole
          >> rpt $ first_assum $ irule_at Any
          >> gvs [evaluate_def])
      >- (gvs []
          >> first_x_assum drule
          >> disch_then drule
          >> strip_tac
          >> gvs []
          >> rename [‘evaluate ([body'],args',dec_clock 1 s') =
            (rb,tb)’,
                     ‘result_rel (LIST_REL (v_rel fb)) _ q rb’]
          >> ‘(case rb of
                 Rval v6 => (Rval v6,tb)
               | Rerr (Rraise (Exn v14)) => (Rerr (Rraise (Exn v14)),tb)
               | Rerr (Rraise (Ret v15)) => (Rerr (Rabort
                 Rtype_error),tb)
               | Rerr (Rabort v11) => (Rerr (Rabort v11),tb)) = (rb,tb)’
                 by
              (Cases_on ‘q’ >> gvs [] >> every_case_tac >> gvs [])
          >> gvs []
          >> qexists ‘fb’
          >> gvs []
          >> rw []
          >- gvs [rewrite_wrapper_def]
          >> gvs [rewrite_worker_def]
          >> ho_match_mp_tac evaluate_fill_hole
          >> rpt $ first_assum $ irule_at Any
          >> gvs [evaluate_def]))
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[letcall]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (args,env1,s) = (v_args,u)’]
*)
  (* args inductive hypothesis *)
(* HOL4 ML code, not ported:
  >> first_assum $ qspecl_then [‘args’, ‘s’] mp_tac
  >> impl_tac
  >- gvs []
  >> imp_res_tac env_rel_relax_opt
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> pop_assum kall_tac
  >> impl_tac
  >- (CCONTR_TAC >> gvs [])
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> gvs [GSYM PULL_FORALL]
  >> strip_tac
  >> pop_assum kall_tac
  >> rename [‘state_rel f' u u'’, ‘result_rel _ _ _ v_args'’]
  >> reverse $ gvs [CaseEq "result"]
  >- (gvs [GSYM PULL_FORALL]
      >> rpt $ first_assum $ irule_at Any
      >> gen_tac
      >> strip_tac
      >> rw []
      >- gvs [evaluate_def, rewrite_wrapper_def]
      >> gvs [evaluate_def, rewrite_worker_def, fill_hole_def]
      >> qexists ‘f'’
      >> gvs [opt_res_rel_def]
      >> irule holes_unchanged_except_subset
      >> first_assum $ irule_at Any
      >> gvs [])
  >- (gvs [GSYM PULL_FORALL, CaseEq "option", CaseEq "prod"]
      >> drule_all find_code_rel
      >> strip_tac
      >> gvs []
      >> ‘u.clock = u'.clock’ by gvs [state_rel_def]
      >> IF_CASES_TAC
      >- (qexistsl [‘u' with clock := 0’, ‘f'’, ‘Rerr (Rabort
        Rtimeout_error)’]
          >> gvs [state_rel_with_clock]
          >> rw []
          >- gvs [rewrite_wrapper_def]
          >> gvs [rewrite_worker_def]
          >> gvs [evaluate_def, fill_hole_def]
          >> qexists ‘f'’
          >> gvs [opt_res_rel_def, state_rel_with_clock]
          >> irule holes_unchanged_except_subset
          >> first_assum $ irule_at Any
          >> gvs [])
      >> gvs [CaseEq "prod"]
*)
      (* callee inductive hypothesis (smaller clock) *)
(* HOL4 ML code, not ported:
      >> first_assum $ qspecl_then [‘[exp]’, ‘dec_clock (ticks + 1) u’]
        mp_tac
      >> impl_tac
      >- (imp_res_tac evaluate_clock >> gvs [dec_clock_def])
      >> rpt $ disch_then drule
      >> drule state_rel_dec
      >> Cases_on ‘u.clock’
      >- gvs []
      >> gvs []
      >> disch_then $ qspec_then ‘ticks + 1’ mp_tac
      >> impl_tac
      >- gvs []
      >> strip_tac
      >> disch_then drule
      >> disch_then $ qspec_then ‘loc'’ mp_tac
      >> impl_tac
      >- gvs [CaseEq "result", CaseEq "error_result"]
      >> strip_tac
      >> Cases_on ‘exp = body'’
      >- (gvs []
          >> qmatch_asmsub_rename_tac ‘evaluate ([body'],args',dec_clock
            (ticks + 1) u) = (cres,cs)’
          >> qmatch_asmsub_rename_tac ‘result_rel _ _ cres tres’
          >> Cases_on ‘cres’ >> gvs []
          >> rename [‘exc_rel _ err terr’]
          >> Cases_on ‘err’ >> gvs []
          >- (Cases_on ‘a’ >> gvs []
              >- (Cases_on ‘v''’ >> gvs []
                  >> qexists ‘f''’
                  >> gvs []
                  >> conj_asm1_tac >- imp_res_tac SUBMAP_TRANS
                  >> conj_asm1_tac
                  >- (irule only_fresh_trans
                      >> rpt $ first_assum $ irule_at Any
                      >> imp_res_tac evaluate_refs_SUBSET)
                  >> conj_asm1_tac >- imp_res_tac
                    holes_unchanged_except_trans
                  >> conj_asm1_tac >- imp_res_tac
                    holes_still_not_finalised_trans
                  >> rw []
                  >- gvs [rewrite_wrapper_def]
                  >> gvs [rewrite_worker_def, evaluate_def,
                    fill_hole_def]
                  >> qexists ‘f''’
                  >> gvs [opt_res_rel_def]
                  >> irule holes_unchanged_except_subset
                  >> first_assum $ irule_at Any
                  >> gvs [])
              >- (Cases_on ‘v''’ >> gvs []
                  >> IF_CASES_TAC >> gvs []
                  >- (imp_res_tac LIST_REL_LENGTH
                      >> gvs []
                      >> ‘env_rel F f'' (l ++ env1) (l' ++ env2)’ by
                         (irule env_rel_append
                          >> gvs []
                          >> metis_tac [env_rel_relax_opt,
                            env_rel_submap, SUBMAP_TRANS])
                      >> first_x_assum $ qspecl_then [‘[x]’, ‘cs’]
                        mp_tac
                      >> impl_tac >- (imp_res_tac evaluate_clock >> gvs
                        [dec_clock_def])
                      >> asm_simp_tac std_ss [EVERY_DEF]
                      >> rpt $ disch_then drule
                      >> impl_tac >- gvs []
                      >> disch_then $ qspec_then ‘loc’ mp_tac
                      >> strip_tac
                      >> rename [‘evaluate ([x],l' ++ env2,t'') =
                        (rc,tc)’,
                                 ‘result_rel (LIST_REL (v_rel fc)) _ r
                                   rc’]
                      >> qexistsl [‘tc’, ‘fc’, ‘rc’]
                      >> gvs []
                      >> imp_res_tac evaluate_refs_SUBSET
                      >> conj_asm1_tac >- metis_tac [SUBMAP_TRANS]
                      >> conj_asm1_tac >- (fs [dec_clock_def] >>
                        metis_tac [only_fresh_trans, SUBSET_TRANS])
                      >> conj_asm1_tac
                      >- (fs [dec_clock_def]
                          >> metis_tac [holes_unchanged_except_trans,
                            only_fresh_trans, SUBMAP_TRANS,
                            SUBSET_TRANS])
                      >> conj_asm1_tac >- imp_res_tac
                        holes_still_not_finalised_trans
                      >> rw []
                      >- gvs [rewrite_wrapper_def]
                      >> gvs [rewrite_worker_def]
                      >> ho_match_mp_tac evaluate_fill_hole
                      >> rpt $ first_assum $ irule_at Any
                      >> gvs [evaluate_def])
                  >> imp_res_tac LIST_REL_LENGTH >> gvs []))
          >- (qexists ‘f''’
              >> gvs []
              >> conj_asm1_tac >- imp_res_tac SUBMAP_TRANS
              >> conj_asm1_tac
              >- (irule only_fresh_trans
                  >> rpt $ first_assum $ irule_at Any
                  >> imp_res_tac evaluate_refs_SUBSET)
              >> conj_asm1_tac >- imp_res_tac
                holes_unchanged_except_trans
              >> conj_asm1_tac >- imp_res_tac
                holes_still_not_finalised_trans
              >> rw []
              >- gvs [rewrite_wrapper_def]
              >> gvs [rewrite_worker_def, evaluate_def, fill_hole_def]
              >> qexists ‘f''’
              >> gvs [opt_res_rel_def]
              >> irule holes_unchanged_except_subset
              >> first_assum $ irule_at Any
              >> gvs []))
      >- (gvs []
          >> first_x_assum drule
          >> disch_then drule
          >> strip_tac
          >> gvs []
*)
          (* the wrapper-IH gives the target callee result for body';
             rename to
             controlled names and discard the spurious direct-IH result
               for exp *)
(* HOL4 ML code, not ported:
          >> qmatch_asmsub_rename_tac
               ‘evaluate ([body'],args'',dec_clock (ticks + 1) u') =
                 (wres,wcs)’
          >> qpat_x_assum ‘evaluate ([exp],args'',_) = _’ kall_tac
          >> qpat_x_assum ‘result_rel _ _ v2 wres’ mp_tac
          >> rpt (qpat_x_assum ‘result_rel _ _ v2 _’ kall_tac)
          >> strip_tac
          >> Cases_on ‘v2’ >> gvs []
          >> Cases_on ‘e’ >> gvs []
          >-
           (Cases_on ‘a’ >> gvs []
            >-
             (Cases_on ‘v''’ >> gvs []
              >> qexists ‘f_wrap’
              >> gvs []
              >> conj_asm1_tac >- metis_tac [SUBMAP_TRANS]
              >> conj_asm1_tac
              >- (irule only_fresh_trans
                  >> rpt $ first_assum $ irule_at Any
                  >> imp_res_tac evaluate_refs_SUBSET)
              >> conj_asm1_tac >- metis_tac
                [holes_unchanged_except_trans]
              >> conj_asm1_tac >- imp_res_tac
                holes_still_not_finalised_trans
              >> rw []
              >- gvs [rewrite_wrapper_def]
              >> gvs [rewrite_worker_def, evaluate_def, fill_hole_def]
              >> qexists ‘f_wrap’
              >> gvs [opt_res_rel_def]
              >> irule holes_unchanged_except_subset
              >> first_assum $ irule_at Any
              >> gvs [])
            >> Cases_on ‘v''’ >> gvs []
            >> IF_CASES_TAC >> gvs []
            >-
             (imp_res_tac LIST_REL_LENGTH
              >> gvs []
              >> ‘env_rel F f_wrap (l ++ env1) (l' ++ env2)’ by
                 (irule env_rel_append
                  >> gvs []
                  >> metis_tac [env_rel_relax_opt, env_rel_submap,
                    SUBMAP_TRANS])
              >> first_x_assum $ qspecl_then [‘[x]’, ‘s''’] mp_tac
              >> impl_tac >- (imp_res_tac evaluate_clock >> gvs
                [dec_clock_def])
              >> asm_simp_tac std_ss [EVERY_DEF]
              >> rpt $ disch_then drule
              >> impl_tac >- gvs []
              >> disch_then $ qspec_then ‘loc’ mp_tac
              >> strip_tac
              >> rename [‘evaluate ([x],l' ++ env2,wcs) = (rc,tc)’,
                         ‘result_rel (LIST_REL (v_rel fc)) _ r rc’]
              >> qexistsl [‘tc’, ‘fc’, ‘rc’]
              >> gvs []
              >> imp_res_tac evaluate_refs_SUBSET
              >> conj_asm1_tac >- metis_tac [SUBMAP_TRANS]
              >> conj_asm1_tac >- (fs [dec_clock_def] >> metis_tac
                [only_fresh_trans, SUBSET_TRANS])
              >> conj_asm1_tac
              >- (fs [dec_clock_def]
                  >> metis_tac [holes_unchanged_except_trans,
                    only_fresh_trans, SUBMAP_TRANS, SUBSET_TRANS])
              >> conj_asm1_tac
              >- imp_res_tac holes_still_not_finalised_trans
              >> rw []
              >- gvs [rewrite_wrapper_def]
              >> gvs [rewrite_worker_def]
              >> ho_match_mp_tac evaluate_fill_hole
              >> rpt $ first_assum $ irule_at Any
              >> gvs [evaluate_def])
            >> imp_res_tac LIST_REL_LENGTH >> gvs [])
          >> qexists ‘f_wrap’
          >> gvs []
          >> conj_asm1_tac >- metis_tac [SUBMAP_TRANS]
          >> conj_asm1_tac
          >- (irule only_fresh_trans
              >> rpt $ first_assum $ irule_at Any
              >> imp_res_tac evaluate_refs_SUBSET)
          >> conj_asm1_tac >- metis_tac [holes_unchanged_except_trans]
          >> conj_tac >- imp_res_tac holes_still_not_finalised_trans
          >> rw []
          >- gvs [rewrite_wrapper_def]
          >> gvs [rewrite_worker_def, evaluate_def, fill_hole_def]
          >> qexists ‘f_wrap’
          >> gvs [opt_res_rel_def]
          >> conj_tac
          >-
           (irule holes_unchanged_except_subset
            >> first_assum $ irule_at Any
            >> gvs [])
          >> imp_res_tac holes_still_not_finalised_trans))
QED
*)

(* HOL4 ML code, not ported:
Resume evaluate_rewrite_tmc[return]:
  gvs [evaluate_def]
  >> gvs [CaseEq "prod", PULL_EXISTS]
  >> rename [‘evaluate (es,env1,s) = (v,u)’]
  >> first_x_assum $ qspecl_then [‘es’, ‘s’, ‘env1’, ‘v’, ‘u’, ‘F’]
    mp_tac
  >> impl_tac
  >- gvs []
  >> asm_simp_tac std_ss [EVERY_DEF]
  >> rpt $ disch_then drule
  >> ‘env_rel F f env1 env2’ by (irule env_rel_relax_opt >> first_assum
    $ irule_at Any)
  >> disch_then drule
  >> disch_then drule
  >> impl_tac
  >- (spose_not_then assume_tac >> gvs [])
  >> disch_then $ qspec_then ‘loc’ mp_tac
  >> strip_tac
  >> gvs [PULL_EXISTS, GSYM PULL_FORALL]
  >> rpt $ first_assum $ irule_at Any
  >> reverse $ gvs [CaseEq "result"]
  >-
   (rw []
    >- gvs [evaluate_def, rewrite_wrapper_def]
    >> gvs [evaluate_def, rewrite_worker_def, fill_hole_def,
      opt_res_rel_def]
    >> first_assum $ irule_at Any
    >> gvs []
    >> irule holes_unchanged_except_subset
    >> first_assum $ irule_at Any
    >> gvs [])
  >> rw []
  >- gvs [evaluate_def, rewrite_wrapper_def]
  >> gvs [evaluate_def, rewrite_worker_def, fill_hole_def,
    opt_res_rel_def]
  >> first_assum $ irule_at Any
  >> gvs []
  >> irule holes_unchanged_except_subset
  >> first_assum $ irule_at Any
  >> gvs []
QED
*)

(* HOL4 ML code, not ported:
Finalise evaluate_rewrite_tmc;
*)

(* ---------------------------------------------------------------------
   ----
   Code labels: the pass only introduces calls to the fresh worker names
     it
   allocates, so every label of the output is a label of the input or
     one of
   the names strictly below the final next-name.
   ---------------------------------------------------------------------
     ---- *)
