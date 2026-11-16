(* ======================================================== *)
(*  computeProof: ported from HOL4's
    candle/prover/compute/computeProofScript.sml
    A proof theory about compute.ml, with no definitions and 14
    theorems.  Needed by candle_kernel_funs.ml.  *)
(* ======================================================== *)

(*
  Proof of correctness for the compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/compute/compute.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/prover/compute/compute_evalProof.ml";;
needs "candle/prover/compute/compute_exec.ml";;
needs "candle/prover/compute/compute_execProof.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/prover/compute/compute_syntaxProof.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "computeProof"
  ["compute"; "compute_eval"; "compute_evalProof"; "compute_execProof";
   "compute_syntax"; "compute_syntaxProof"; "holKernel"; "holKernelProof";
   "holSyntax"; "holSyntaxExtra"; "ml_monadBase"];;

let compute_init_thy_ok = prove
 (`compute_init ths /\
   STATE ctxt s /\
   ALL (THM ctxt) ths ==>
     compute_thy_ok ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) ctxt)`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * compute_add
 * ------------------------------------------------------------------------- *)

let compute_add_thm = prove
 (`STATE ctxt s /\
   ALL (THM ctxt) ths /\
   TERM ctxt tm ==>
   compute_add ths tm s = (res,s') ==>
     s' = s /\
     (!th. res = M_success th ==> THM ctxt th) /\
     (!tm. ~(res = M_failure (holKernel_Clash tm)))`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * compute
 * ------------------------------------------------------------------------- *)

(* [local] *)
let const_list_ok = prove
 (`!vs. set_of_list ((\ctxt. FLAT (MAP consts_of_upd ctxt)) vs) = cexp_consts
  vs`,
  CHEAT_TAC);;

(* [local] *)
let var_list_ok = prove
 (`!vs. set_of_list (compute_var_list vs) = cexp_vars vs`,
  CHEAT_TAC);;

let check_cexp_closed_correct = prove
 (`!bvs v. check_cexp_closed bvs v ==> cexp_vars v DIFF set_of_list bvs = {}`,
  CHEAT_TAC);;

let map_check_var_thm = prove
 (`!tms s res s'.
     STATE ctxt s /\
     ALL (TERM ctxt) tms /\
     compute_eval_map check_var tms s = (res,s') ==>
       s = s' /\
       (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
       (!ns.
         res = M_success ns ==>
         ALL2 (\tm n. tm = holSyntax_Var n (holSyntax_Tyapp (implode
           "cval") [])) tms ns)`,
  CHEAT_TAC);;

let check_eqn_thm = prove
 (`compute_thy_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
  list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
  (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt) /\
   STATE ctxt s /\
   THM ctxt th /\
   check_eqn th s = (res,s') ==>
     s = s' /\
     (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
     (!f vs r.
       res = M_success (f,vs,cv) ==>
       (?l r. ALL_DISTINCT vs /\
             th = holKernel_Sequent [] ((===) l r) /\
             list_dest_comb [] l = CONS (holSyntax_Const f (app_type (LENGTH
               vs)))
                              (MAP (\s. holSyntax_Var s (holSyntax_Tyapp
                                (implode "cval") [])) vs) /\
             dest_cexp r = SOME cv /\
             (!v. v IN cexp_vars cv ==> MEM v vs)))`,
  CHEAT_TAC);;

let map_check_eqn_thm = prove
 (`compute_thy_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
  list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
  (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt) ==>
   (!ceqs s res s'.
     STATE ctxt s /\
     ALL (THM ctxt) ceqs /\
     compute_eval_map check_eqn ceqs s = (res,s') ==>
       s = s' /\
       (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
       (!eqs. res = M_success eqs ==>
         (!n. n < LENGTH eqs ==>
             (?f vs cv l r.
               ALL_DISTINCT vs /\
               EL n eqs = (f,vs,cv) /\
               EL n ceqs = holKernel_Sequent [] ((===) l r) /\
               list_dest_comb [] l = CONS (holSyntax_Const f (app_type
                 (LENGTH vs)))
                              (MAP (\s. holSyntax_Var s (holSyntax_Tyapp
                                (implode "cval") [])) vs) /\
               dest_cexp r = SOME cv /\
               (!v. v IN cexp_vars cv ==> MEM v vs)))))`,
  CHEAT_TAC);;

let check_consts_thm = prove
 (`STATE ctxt s /\
   check_consts ars f r s = (res,s') ==>
     s = s' /\
     (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
     (!u. res = M_success u ==> ALL (\(c,n). MEM (c,n) ars) ((\ctxt. FLAT
       (MAP consts_of_upd ctxt)) r))`,
  CHEAT_TAC);;

let map_check_consts_thm = prove
 (`!ceqs s res s'.
     STATE ctxt s /\
     compute_eval_map (\(f,(n,r)). check_consts ars f r) ceqs s = (res,s')
       ==>
       s = s' /\
       (!tm. ~(res = M_failure (holKernel_Clash tm))) /\
       (!u. res = M_success u ==>
         (!f vs cv.
           MEM (f,vs,cv) ceqs ==>
           ALL (\(c,n). MEM (c,n) ars) ((\ctxt. FLAT (MAP consts_of_upd
             ctxt)) cv)))`,
  CHEAT_TAC);;

let check_consts_ok = prove
 (`!eqs cexp s u s'.
     check_consts (MAP (\(f,vs,x). (f,LENGTH vs)) eqs) fn cexp s =
       (M_success u,s') ==>
       cexp_consts_ok eqs cexp`,
  CHEAT_TAC);;

let cexp2term_from_cv = prove
 (`!v. cexp2term (from_cv v) = cv2term v`,
  CHEAT_TAC);;

let const_list_imp_cexp_consts_ok = prove
 (`!eqs cv.
     ALL (\(p1,p2). MEM (p1,p2) (MAP (\(f,n,r). (f,LENGTH n)) eqs)) ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) cv) ==>
     cexp_consts_ok eqs cv`,
  CHEAT_TAC);;

(* The type check can cause all sorts of failures, but the 'compute_eval'
 * (and its implementation called exec) function always succeeds or raises
 * a «timeout» exception. (Unfortunately, this is shadowed by the failures
 * raised by the 'compute' function.)
 *)

let compute_thm = prove
 (`STATE ctxt s /\
   ALL (THM ctxt) ths /\
   ALL (THM ctxt) ceqs /\
   TERM ctxt tm ==>
   compute (ths,ceqs) tm s = (res,s') ==>
     s' = s /\
     (!th. res = M_success th ==> THM ctxt th) /\
     (!tm. ~(res = M_failure (holKernel_Clash tm)))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
