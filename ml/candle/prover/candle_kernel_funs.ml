(* ======================================================== *)
(*  candle_kernel_funs: ported from HOL4's
    candle/prover/candle_kernel_funsScript.sml
    A definition theory, with no definitions and 21 theorems.
    Needed by candle_prover_evaluate.ml and
    candle_prover_semantics.ml.  *)
(* ======================================================== *)

(*
  Prove that kernel functions maintain Candle prover's invariants
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_kernel_perms.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/candle_prover_inv.ml";;
needs "candle/prover/compute/computeProof.ml";;
needs "candle/prover/perms.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/ml_monad_translator.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_kernel_funs"
  ["ast_extras"; "candle_kernelProg"; "candle_kernel_perms";
   "candle_kernel_vals"; "candle_prover_inv"; "computeProof"; "evaluate";
   "evaluateProps"; "holKernelProof"; "misc"; "ml_hol_kernel_funsProg";
   "ml_prog"; "namespaceProps"; "perms"; "semanticPrimitives";
   "semanticPrimitivesProps"];;

let _ = do_list hide_constant ["C"; "abort"; "fv"];;


(* Arrow1 *)
let arrow1 = prove
 (`(A (Arrow) B) f fv /\
   semanticPrimitives_do_opapp [fv; av] = SOME (env,exp) /\
   evaluate (s:'ffi semanticPrimitives_state) env [exp] = (s',res) /\
   A a av /\
   perms_ok {} av /\
   perms_ok {} fv ==> semanticPrimitives_state_ffi
     s = semanticPrimitives_state_ffi s' /\
     ((res = Rerr (Rabort Rtimeout_error)) \/
      (res = Rerr (Rabort Rtype_error)) \/ semanticPrimitives_state_refs
      s = semanticPrimitives_state_refs s'
        /\ semanticPrimitives_state_eval_state
      s = semanticPrimitives_state_eval_state s'
        /\ semanticPrimitives_state_next_type_stamp
      s = semanticPrimitives_state_next_type_stamp s' /\
      (?rv. res = Rval [rv] /\
           B (f a) rv))`,
  CHEAT_TAC);;

(* Arrow2 *)
let arrow2 = prove
 (`(A (Arrow) B (Arrow) C) f fv /\
   do_partial_app fv av = SOME gv /\
   semanticPrimitives_do_opapp [gv; bv] = SOME (env,exp) /\
   evaluate (s:'ffi semanticPrimitives_state) env [exp] = (s',res) /\
   A a av /\ B b bv /\
   perms_ok {} av /\
   perms_ok {} bv /\
   perms_ok {} fv ==> semanticPrimitives_state_ffi
     s = semanticPrimitives_state_ffi s' /\
     ((res = Rerr (Rabort Rtimeout_error)) \/
      (res = Rerr (Rabort Rtype_error)) \/ semanticPrimitives_state_refs
      s = semanticPrimitives_state_refs s'
        /\ semanticPrimitives_state_eval_state
      s = semanticPrimitives_state_eval_state s'
        /\ semanticPrimitives_state_next_type_stamp
      s = semanticPrimitives_state_next_type_stamp s' /\
      (?rv. res = Rval [rv] /\
           C (f a b) rv))`,
  CHEAT_TAC);;

(* [local] *)
let GC_T = prove
 (`GC s = T`,
  CHEAT_TAC);;

let MEM_st2heap = prove
 (`// TODO: move
   cfHeapsBase_Mem l x IN st2heap p s <=>
   l < LENGTH (semanticPrimitives_state_refs s) /\ x = EL l
     (semanticPrimitives_state_refs s)`,
  CHEAT_TAC);;

let HOL_STORE_not_kernel_locs = prove
 (`(!loc. loc IN kernel_locs ==> kernel_loc_ok refs loc
  (semanticPrimitives_state_refs s)) /\
   l < LENGTH (semanticPrimitives_state_refs s) /\ ~(l IN kernel_locs) ==>
   (HOL_STORE refs * set_sep_one (cfHeapsBase_Mem l (EL l
     (semanticPrimitives_state_refs s))) * GC) (st2heap p s)`,
  CHEAT_TAC);;

let REFS_PRED_HOL_STORE = prove
 (`(!loc. loc IN kernel_locs ==> kernel_loc_ok refs loc
  (semanticPrimitives_state_refs s)) ==>
   REFS_PRED (HOL_STORE,p) refs s`,
  CHEAT_TAC);;

let HOL_STORE_kernel_loc_ok = prove
 (`(HOL_STORE r * frame) (st2heap p s) /\ loc IN kernel_locs ==>
   kernel_loc_ok r loc (semanticPrimitives_state_refs s)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_perms_ok_lemma = prove
 (`(LIST_TYPE (PAIR_TYPE STRING_TYPE NUM) x1 v ==> perms_ok ps v) /\
   (LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE) x2 v ==> perms_ok ps v) /\
   (LIST_TYPE THM_TYPE x3 v ==> perms_ok ps v) /\
   (LIST_TYPE UPDATE_TYPE x4 v ==> perms_ok ps v)`,
  CHEAT_TAC);;

(* HOL4 candle_kernel_funsScript.sml:217-218: the ML values that the
   definitions below antiquote *)

let ArrowM1 = prove
 (`ArrowP F (HOL_STORE,(p:('a->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) (PURE A) (MONAD B D) f fv /\
   semanticPrimitives_do_opapp [fv; av] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) /\
   A a av /\ STATE ctxt refs /\
   (!loc. loc IN kernel_locs ==> kernel_loc_ok refs loc
     (semanticPrimitives_state_refs s)) /\
   (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l)
     (semanticPrimitives_state_refs s) loc = SOME r ==>
     candle_prover_inv_ref_ok ctxt r) /\
   perms_ok kernel_perms av /\
   perms_ok kernel_perms fv ==> semanticPrimitives_state_ffi
     s = semanticPrimitives_state_ffi s' /\
     ((res = Rerr (Rabort Rtimeout_error)) \/
      (res = Rerr (Rabort Rtype_error)) \/
        semanticPrimitives_state_next_type_stamp
      s = semanticPrimitives_state_next_type_stamp s'
        /\ semanticPrimitives_state_eval_state
      s = semanticPrimitives_state_eval_state s' /\
      (?r refs2.
        f a refs = (r,refs2) /\
        (!loc. loc IN kernel_locs ==> kernel_loc_ok refs2 loc
          (semanticPrimitives_state_refs s')) /\
        (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l)
          (semanticPrimitives_state_refs s') loc = SOME r ==>
          candle_prover_inv_ref_ok ctxt r) /\
        (!x. r = M_success x ==> (?rv. res = Rval [rv] /\ B x rv)) /\
        (!x. r = M_failure x ==> (?rv. res = Rerr (Rraise rv) /\ D x
          rv))))`,
  CHEAT_TAC);;

let ArrowM2 = prove
 (`ArrowP F (HOL_STORE,(p:('a->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) (PURE A1) (ArrowM F (HOL_STORE,p) (PURE A2) (MONAD B D)) f fv
  /\
   do_partial_app fv a1v = SOME gv /\
   semanticPrimitives_do_opapp [gv; a2v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) /\
   A1 a1 a1v /\ A2 a2 a2v /\ STATE ctxt refs /\
   (!loc. loc IN kernel_locs ==> kernel_loc_ok refs loc
     (semanticPrimitives_state_refs s)) /\
   (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l)
     (semanticPrimitives_state_refs s) loc = SOME r ==>
     candle_prover_inv_ref_ok ctxt r) /\
   perms_ok kernel_perms a1v /\
   perms_ok kernel_perms a2v /\
   perms_ok kernel_perms fv ==> semanticPrimitives_state_ffi
     s = semanticPrimitives_state_ffi s' /\
     ((res = Rerr (Rabort Rtimeout_error)) \/
      (res = Rerr (Rabort Rtype_error)) \/
        semanticPrimitives_state_next_type_stamp
      s = semanticPrimitives_state_next_type_stamp s'
        /\ semanticPrimitives_state_eval_state
      s = semanticPrimitives_state_eval_state s' /\
      (?r refs2.
        f a1 a2 refs = (r,refs2) /\
        (!loc. loc IN kernel_locs ==> kernel_loc_ok refs2 loc
          (semanticPrimitives_state_refs s')) /\
        (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l)
          (semanticPrimitives_state_refs s') loc = SOME r ==>
          candle_prover_inv_ref_ok ctxt r) /\
        (!x. r = M_success x ==> (?rv. res = Rval [rv] /\ B x rv)) /\
        (!x. r = M_failure x ==> (?rv. res = Rerr (Rraise rv) /\ D x
          rv))))`,
  CHEAT_TAC);;

let state_ok_with_clock = prove
 (`candle_prover_inv_state_ok ctxt (semanticPrimitives_state_clock_fupd (K k)
  s) <=> candle_prover_inv_state_ok ctxt s`,
  CHEAT_TAC);;
add_simp state_ok_with_clock;;

let EqualityType_11 = prove
 (`!abs' x v v'. EqualityType abs' /\ abs' x v /\ abs' x v' ==> v = v'`,
  CHEAT_TAC);;

let IMP_EVERY_v_ok = prove
 (`(!loc. if loc IN kernel_locs then kernel_loc_ok refs loc
  (semanticPrimitives_state_refs s')
          else (\l n. oEL n l) (semanticPrimitives_state_refs s') loc = (\l
            n. oEL n l) (semanticPrimitives_state_refs s) loc) /\
   (!loc. loc IN kernel_locs ==> kernel_loc_ok refs loc
     (semanticPrimitives_state_refs s)) /\
   ALL (candle_prover_inv_ref_ok ctxt) (semanticPrimitives_state_refs s)
     /\ STATE ctxt refs ==>
   ALL (candle_prover_inv_ref_ok ctxt) (semanticPrimitives_state_refs s')`,
  CHEAT_TAC);;

let HOL_EXN_TYPE_Fail_v_ok = prove
 (`HOL_EXN_TYPE (holKernel_Failure m) v ==> candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let inferred_APPEND = prove
 (`!c v. inferred c v ==>
     (!x s. STATE (APPEND x c) s /\ (!th. THM c th ==> THM (APPEND x c) th)
       ==>
           inferred (APPEND x c) v)`,
  CHEAT_TAC);;

let v_ok_APPEND = prove
 (`(!c v. kernel_vals c v ==>
     (!x s.
     STATE (APPEND x c) s /\ (!th. THM c th ==> THM (APPEND x c) th) ==>
       kernel_vals (APPEND x c) v)) /\
   (!c v. candle_prover_inv_v_ok c v ==> (!x s.
     !x s.
      STATE (APPEND x c) s /\ (!th. THM c th ==> THM (APPEND x c) th) ==>
        candle_prover_inv_v_ok (APPEND x c) v)) /\
   (!c e. candle_prover_inv_env_ok c e ==> (!x s.
     !x s.
   STATE (APPEND x c) s /\ (!th. THM c th ==> THM (APPEND x c) th) ==>
     candle_prover_inv_env_ok (APPEND x c) e))`,
  CHEAT_TAC);;

let ref_ok_APPEND = prove
 (`!c v. candle_prover_inv_ref_ok c v ==> (!x s.
     !x s.
      STATE (APPEND x c) s /\ (!th. THM c th ==> THM (APPEND x c) th) ==>
        candle_prover_inv_ref_ok (APPEND x c) v)`,
  CHEAT_TAC);;

let inferred_ok = prove
 (`inferred ctxt f /\
   candle_prover_inv_state_ok ctxt s /\
   candle_prover_inv_v_ok ctxt v /\
   semanticPrimitives_do_opapp [f; v] = SOME (env,exp) /\
   evaluate (s:'ffi semanticPrimitives_state) env [exp] = (s',res) ==>
     (?abort. semanticPrimitives_state_ffi s' = semanticPrimitives_state_ffi
       s /\ res = Rerr (Rabort abort)) \/
     (?ctxt'.
       candle_prover_inv_state_ok ctxt' s' /\
       (!v. candle_prover_inv_v_ok ctxt v ==> candle_prover_inv_v_ok ctxt'
         v) /\
       (!v. kernel_vals ctxt v ==> kernel_vals ctxt' v) /\
       (!vs. res = Rval vs ==> ALL (candle_prover_inv_v_ok ctxt') vs) /\
       (!v. res = Rerr (Rraise v) ==> candle_prover_inv_v_ok ctxt' v))`,
  CHEAT_TAC);;

let kernel_vals_twice_partial_app = prove
 (`!ctxt f. kernel_vals ctxt f ==>
            (!v g w. do_partial_app f v = SOME g ==>
                    do_partial_app g w = NONE)`,
  CHEAT_TAC);;

let kernel_vals_max_app = prove
 (`kernel_vals ctxt f /\
   do_partial_app f v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) ==>
     f IN kernel_funs`,
  CHEAT_TAC);;

let kernel_vals_ok = prove
 (`!ctxt f.
     kernel_vals ctxt f ==>
       (!s v env exp s' res.
         semanticPrimitives_do_opapp [f; v] = SOME (env,exp) /\
         candle_prover_inv_state_ok ctxt s /\
         candle_prover_inv_v_ok ctxt v /\
         evaluate (s:'ffi semanticPrimitives_state) env [exp] = (s',res) ==>
           (?abort. semanticPrimitives_state_ffi s' =
             semanticPrimitives_state_ffi s /\ res = Rerr (Rabort abort)) \/
           (?ctxt'.
             candle_prover_inv_state_ok ctxt' s' /\
             (!v. candle_prover_inv_v_ok ctxt v ==> candle_prover_inv_v_ok
               ctxt' v) /\
             (!v. kernel_vals ctxt v ==> kernel_vals ctxt' v) /\
             (!vs. res = Rval vs ==> ALL (candle_prover_inv_v_ok ctxt') vs)
               /\
             (!v. res = Rerr (Rraise v) ==> candle_prover_inv_v_ok ctxt'
               v)))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C";
   "abort";
   "fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
