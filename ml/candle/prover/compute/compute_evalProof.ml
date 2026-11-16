(* ======================================================== *)
(*  compute_evalProof: ported from HOL4's
    candle/prover/compute/compute_evalProofScript.sml
    A proof theory about compute_eval.ml, with 1 definition and 40
    theorems.  Needed by computeProof.ml and compute_execProof.ml.  *)
(* ======================================================== *)

(*
   Proofs about the interpreter function for the Candle compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/prover/compute/compute_syntaxProof.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compute_evalProof"
  ["compute_eval"; "compute_syntax"; "compute_syntaxProof"; "holKernel";
   "holKernelProof"; "holSyntax"; "holSyntaxExtra"; "holSyntaxLib";
   "ml_monadBase"];;

(* HOL4 compute_evalProofScript.sml:14-15: ML code, not ported *)

let do_fst_thm = prove
 (`do_fst p s = (res,s') ==>
     s = s' /\
     (?q. res = M_success q /\ cexp_consts q SUBSET cexp_consts p)`,
  CHEAT_TAC);;

let do_snd_thm = prove
 (`do_snd p s = (res,s') ==>
     s = s' /\
     (?q. res = M_success q /\ cexp_consts q SUBSET cexp_consts p)`,
  CHEAT_TAC);;

let do_ispair_thm = prove
 (`do_ispair p s = (res,s') ==>
     s = s' /\
     (?q. res = M_success q /\ cexp_consts q SUBSET cexp_consts p)`,
  CHEAT_TAC);;

let term_ok_FOLDL_Comb = prove
 (`!tms tm.
     holSyntax_term_ok sig (FOLDL holSyntax_Comb tm tms) ==>
       holSyntax_term_ok sig tm /\
       ALL (holSyntax_term_ok sig) tms`,
  CHEAT_TAC);;

let subst_term_ok = prove
 (`!env cv.
     holSyntax_term_ok ctxt (cexp2term cv) /\
     ALL (holSyntax_term_ok ctxt o cexp2term) (MAP SND env) ==>
       holSyntax_term_ok ctxt (cexp2term (compute_eval_subst env cv))`,
  CHEAT_TAC);;

let do_arith_value = prove
 (`!opn x y s z s'.
     compute_eval_do_arith opn x y s = (M_success z,s') ==> cexp_value z`,
  CHEAT_TAC);;

let do_reln_value = prove
 (`!opn x y s z s'.
     do_reln opn x y s = (M_success z,s') ==> cexp_value z`,
  CHEAT_TAC);;

let do_eq_value = prove
 (`compute_eval_do_eq (x:compute_exp) y (s:'a) = (M_success z,s') ==>
  cexp_value z`,
  CHEAT_TAC);;

let do_binop_value = prove
 (`!bop x y z s s'.
     do_binop bop x y s = (M_success z,s') ==> cexp_value z`,
  CHEAT_TAC);;

let compute_eval_value = prove
 (`(!ck ceqs cv s x s'.
     compute_eval ck ceqs cv s = (M_success x,s') ==> cexp_value x) /\
   (!ck ceqs cvs s xs s'.
     compute_eval_list ck ceqs cvs s = (M_success xs,s') ==> ALL
       cexp_value xs)`,
  CHEAT_TAC);;

let dest_binary_thm = prove
 (`STATE ctxt s /\
   TERM ctxt tm /\
   TERM ctxt tm' ==>
   dest_binary tm' tm s = (res,s') ==>
     s' = s /\
     (!l r. res = M_success (l,r) ==>
           TERM ctxt l /\ TERM ctxt r /\
           tm = holSyntax_Comb (holSyntax_Comb tm' l) r)`,
  CHEAT_TAC);;

let dest_numeral_thm = prove
 (`STATE ctxt s /\
   TERM ctxt tm ==>
   dest_numeral tm s = (res,s') ==>
     s' = s /\
     (!n. res = M_success n ==>
         (numeral_thy_ok ((\(ctxt:holSyntax_update list).
           ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt.
           FLAT (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap
           ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt.
           set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd)
           (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt) ==> typeof tm =
           (holSyntax_Tyapp (implode "num") [])) /\
         (?tm'. tm = (\tm. holSyntax_Comb (holSyntax_Const (implode
           "NUMERAL") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
           (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp (implode
           "num") []))) tm) tm' /\ compute_eval_dest_num tm' = SOME n))`,
  CHEAT_TAC);;

let num2bit_thm = prove
 (`numeral_thy_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
  list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt)) ctxt))
  ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt)) ctxt))
  ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
  (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt)) ctxt) ==>
     TERM ctxt (num2bit x)`,
  CHEAT_TAC);;

let dest_num_num2bit = prove
 (`numeral_thy_ok thy ==>
   (!x y.
     compute_eval_dest_num x = SOME y ==> (|-) (thy,[]) ((===) (num2bit y)
       x))`,
  CHEAT_TAC);;

let num2bit_dest_numeral = prove
 (`dest_numeral ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s
  t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (holSyntax_Tyapp (implode "num") []))) tm) x) s = (M_success y,s') /\
   numeral_thy_ok ((\(ctxt:holSyntax_update list). ((\(ctxt:holSyntax_update
     list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP types_of_upd ctxt))
     ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt. FLAT (MAP consts_of_upd ctxt))
     ctxt)) ctxt)) ctxt,(\ctxt. set_of_list ((\ctxt. FLAT (MAP (\upd. APPEND
     (axexts_of_upd upd) (conexts_of_upd upd)) ctxt)) ctxt)) ctxt))
     (hol_refs_the_context s)) ==>
     s = s' /\ (|-) ((\(ctxt:holSyntax_update list).
       ((\(ctxt:holSyntax_update list). ((\ctxt. alist_to_fmap ((\ctxt. FLAT
       (MAP types_of_upd ctxt)) ctxt)) ctxt,(\ctxt. alist_to_fmap ((\ctxt.
       FLAT (MAP consts_of_upd ctxt)) ctxt)) ctxt)) ctxt,(\ctxt. set_of_list
       ((\ctxt. FLAT (MAP (\upd. APPEND (axexts_of_upd upd) (conexts_of_upd
       upd)) ctxt)) ctxt)) ctxt)) (hol_refs_the_context s),[]) ((===)
       (num2bit y) x)`,
  CHEAT_TAC);;

let cexp2term_dest_numeral_opt = prove
 (`dest_numeral_opt x = SOME y /\
   compute_thy_ok thy ==> (|-) (thy,[]) ((===) (cexp2term
     ((holSyntax_Tyapp (implode "num") []) y)) ((\tm. holSyntax_Comb
     (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
     "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
     (implode "cval") []))) tm) x))`,
  CHEAT_TAC);;

let dest_cexp_thm = prove
 (`compute_thy_ok thy ==>
     (!tm cv.
       dest_cexp tm = SOME cv ==>
       holSyntax_term_ok (FST thy) tm ==> (|-) (thy,[]) ((===) (cexp2term cv)
         tm) /\
         typeof tm = (holSyntax_Tyapp (implode "cval") []))`,
  CHEAT_TAC);;

(* ALOOKUP_MAP_3[local] *)
let compute_evalProof_ALOOKUP_MAP_3 = prove
 (`!xs n.
     (!x y. f x = f y ==> x = y) ==>
       ALOOKUP (MAP (\(k,v). (f k,g v)) xs) (f n) =
       ALOOKUP (MAP (\(k,v). (k,g v)) xs) n`,
  CHEAT_TAC);;

let cexp_value_closed = prove
 (`!v. cexp_value v ==> cexp_vars v = {}`,
  CHEAT_TAC);;

let closed_subst = prove
 (`!env v.
     ALL cexp_value (MAP SND env) ==>
       cexp_vars (compute_eval_subst env v) = cexp_vars v DIFF set_of_list
         (MAP FST env)`,
  CHEAT_TAC);;

let closed_subst' = prove
 (`ALL cexp_value (MAP SND env) /\
   cexp_vars v SUBSET set_of_list (MAP FST env) ==>
     cexp_vars (compute_eval_subst env v) = {}`,
  CHEAT_TAC);;

let VSUBST_FOLDL_Comb_push = prove
 (`!tms t.
     FOLDL holSyntax_Comb (VSUBST is t) (MAP (VSUBST is) tms) =
     VSUBST is (FOLDL (holSyntax_Comb:holSyntax_term) t tms)`,
  CHEAT_TAC);;

let VSUBST_bop2term = prove
 (`VSUBST is (bop2term bop x y) = bop2term bop (VSUBST is x) (VSUBST is y)`,
  CHEAT_TAC);;
add_simp VSUBST_bop2term;;

let VSUBST_uop2term = prove
 (`VSUBST is (uop2term uop x) = uop2term uop (VSUBST is x)`,
  CHEAT_TAC);;
add_simp VSUBST_uop2term;;


let VFREE_IN_FOLDL = prove
 (`!ts v t.
     VFREE_IN v (FOLDL holSyntax_Comb t ts) <=> EX (VFREE_IN v) ts \/
       VFREE_IN v t`,
  CHEAT_TAC);;

let VFREE_IN_cexp_vars = prove
 (`!v. cexp_vars v = {n | VFREE_IN (holSyntax_Var n (holSyntax_Tyapp (implode
  "cval") [])) (cexp2term v)}`,
  CHEAT_TAC);;

let subst_VSUBST = prove
 (`!env x.
     ALL (\v. cexp_vars v = {}) (MAP SND env) ==>
       cexp2term (compute_eval_subst env x) =
       VSUBST (MAP (\(s,v). (cexp2term v,holSyntax_Var s (holSyntax_Tyapp
         (implode "cval") []))) env) (cexp2term x)`,
  CHEAT_TAC);;

(* [local] *)
let MAP_subst_MAP_Var = prove
 (`!xs ys.
     ALL_DISTINCT xs /\
     LENGTH xs = LENGTH ys ==>
       MAP (compute_eval_subst (ZIP xs ys)) (MAP holSyntax_Var xs) = ys`,
  CHEAT_TAC);;

(* TODO Move *)
let SAFEDIV_0 = prove
 (`SAFEDIV 0 n = 0`,
  CHEAT_TAC);;
add_simp SAFEDIV_0;;

(* [local] *)
let NUMERAL_ONE = prove
 (`numeral_thy_ok thy ==> (|-) (thy,[]) ((===) ((\tm. holSyntax_Comb
  (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
  (implode "num") []))) tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode
  "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
  (implode "num") []) (holSyntax_Tyapp (implode "num") []))) tm)
  (holSyntax_Const (implode "_0") (holSyntax_Tyapp (implode "num") []))))
  ((\tm. holSyntax_Comb (holSyntax_Const (implode "SUC") ((\s t.
  holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode "num")
  []) (holSyntax_Tyapp (implode "num") []))) tm) ((\tm. holSyntax_Comb
  (holSyntax_Const (implode "NUMERAL") ((\s t. holSyntax_Tyapp (implode
  "fun") [s; t]) (holSyntax_Tyapp (implode "num") []) (holSyntax_Tyapp
  (implode "num") []))) tm) (holSyntax_Const (implode "_0") (holSyntax_Tyapp
  (implode "num") [])))))`,
  CHEAT_TAC);;

let do_binop_thm = prove
 (`compute_thy_ok thy ==>
     holSyntax_term_ok (FST thy)
       (cexp2term p) /\
     holSyntax_term_ok (FST thy)
       (cexp2term q) /\ (|-) (thy,[]) ((===) (cexp2term p) (cexp2term x))
       /\ cexp_value x /\ (|-) (thy,[]) ((===) (cexp2term q) (cexp2term y))
       /\ cexp_value y /\
     do_binop bop x y s = (res,s') ==>
       s' = s /\
       (?cv. res = M_success cv /\ (|-) (thy,[]) ((===) (bop2term bop
         (cexp2term p) (cexp2term q)) (cexp2term cv)))`,
  CHEAT_TAC);;

let do_uop_thm = prove
 (`compute_thy_ok thy ==>
     holSyntax_term_ok (FST thy)
       (cexp2term p) /\ (|-) (thy,[]) ((===) (cexp2term p) (cexp2term x))
       /\ cexp_value x /\
     do_uop uop x s = (res,s') ==>
       s' = s /\
       (?cv. res = M_success cv /\ (|-) (thy,[]) ((===) (uop2term uop
         (cexp2term p)) (cexp2term cv)))`,
  CHEAT_TAC);;

let term_ok_bop2term = prove
 (`holSyntax_term_ok sig (bop2term bop tm1 tm2) ==>
     holSyntax_term_ok sig tm1 /\ holSyntax_term_ok sig tm2`,
  CHEAT_TAC);;

let term_ok_uop2term = prove
 (`holSyntax_term_ok sig (uop2term uop tm) ==>
     holSyntax_term_ok sig tm`,
  CHEAT_TAC);;

let compute_eval_list_map = prove
 (`!cvs s. compute_eval_list ck eqs cvs s = compute_eval_map (compute_eval ck
  eqs) cvs s`,
  CHEAT_TAC);;

let compute_thy_ok_is_std_sig = prove
 (`compute_thy_ok thy ==> is_std_sig (FST thy)`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE (compute_exp_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let cexp_consts_ok_def,cexp_consts_ok_ind = define_guess
  `(cexp_consts_ok eqs (compute_syntax_Var s) = T) /\
   (cexp_consts_ok eqs (compute_syntax_Num n) = T) /\
   (cexp_consts_ok eqs (compute_syntax_Pair p q) =
      (cexp_consts_ok eqs p /\ cexp_consts_ok eqs q)) /\
   (cexp_consts_ok eqs (compute_syntax_If p q r) =
      (cexp_consts_ok eqs p /\ cexp_consts_ok eqs q /\ cexp_consts_ok
          eqs r)) /\
   (cexp_consts_ok eqs (compute_syntax_Uop uop p) = cexp_consts_ok eqs p) /\
   (cexp_consts_ok eqs (compute_syntax_Binop bop p q) =
      (cexp_consts_ok eqs p /\ cexp_consts_ok eqs q)) /\
   (cexp_consts_ok eqs (compute_syntax_Let s p q) =
      (cexp_consts_ok eqs p /\ cexp_consts_ok eqs q)) /\
   (cexp_consts_ok eqs (compute_syntax_App f cs) =
      (MEM (f,LENGTH cs) (MAP (\(f,n,x). (f,LENGTH n)) eqs) /\
       ALL (cexp_consts_ok eqs) cs))`;;

let cexp_consts_ok_value = prove
 (`!eqs cv.
     cexp_value cv ==>
     cexp_consts_ok eqs cv`,
  CHEAT_TAC);;

let cexp_consts_ok_subst = prove
 (`!xs x.
     cexp_consts_ok eqs x /\
     ALL (cexp_consts_ok eqs) (MAP SND xs) ==>
       cexp_consts_ok eqs (compute_eval_subst xs x)`,
  CHEAT_TAC);;

(* N.B. This can be cleaned up a bit. There's a derivation of general beta
 *      conversion hidden in here that could be pulled out into a lemma if its
 *      ever needed.
 *)

let LET_VSUBST = prove
 (`compute_thy_ok thy /\
   holSyntax_term_ok (FST thy)
     q /\ holSyntax_term_ok (FST thy)
     p /\ holSyntax_term_ok (FST thy)
     r /\ (|-) (thy,[]) ((===) p r) /\ has_type p (holSyntax_Tyapp (implode
     "cval") []) /\ has_type q (holSyntax_Tyapp (implode "cval") []) ==> (|-)
     (thy,[]) ((===) ((\t1 t2. holSyntax_Comb (holSyntax_Comb
     (holSyntax_Const (implode "LET") ((\s t. holSyntax_Tyapp (implode "fun")
     [s; t]) ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
     (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])) (ast_Fun
     (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
     [])))) t1) t2) (holSyntax_Abs (holSyntax_Var s (holSyntax_Tyapp (implode
     "cval") [])) q) p) (VSUBST [(r,holSyntax_Var s (holSyntax_Tyapp (implode
     "cval") []))] q))`,
  CHEAT_TAC);;

let compute_eval_thm = prove
 (`compute_thy_ok thy ==>
     ((!ck eqs cv s res s' tm.
       compute_eval ck eqs cv s = (res,s') /\
       holSyntax_term_ok (FST thy) (cexp2term cv) /\
       cexp_vars cv = {} /\
       cexp_consts_ok eqs cv /\
       ALL_DISTINCT (MAP FST eqs) /\
       ALL (\(f,vs,cv).
         ALL_DISTINCT vs /\
         cexp_consts_ok eqs cv /\
         (?r. (|-) (thy,[]) ((===) (cexp2term (ast_App f (MAP ast_Var vs)))
           r) /\
             dest_cexp r = SOME cv /\
             cexp_vars cv SUBSET set_of_list vs)) eqs ==>
         s' = s /\
         (!err. res = M_failure err ==> err = holKernel_Failure (implode
           "timeout")) /\
         (!cv'. res = M_success cv' ==> (|-) (thy,[]) ((===) (cexp2term cv)
           (cexp2term cv')))) /\
     (!ck eqs cvs s res s' tm.
       compute_eval_list ck eqs cvs s = (res,s') /\
       ALL (holSyntax_term_ok (FST thy)) (MAP cexp2term cvs) /\
       ALL (\cv. cexp_vars cv = {}) cvs /\
       ALL (cexp_consts_ok eqs) cvs /\
       ALL_DISTINCT (MAP FST eqs) /\
       ALL (\(f,vs,cv).
         ALL_DISTINCT vs /\
         cexp_consts_ok eqs cv /\
         (?r. (|-) (thy,[]) ((===) (cexp2term (ast_App f (MAP ast_Var vs)))
           r) /\
             dest_cexp r = SOME cv /\
             cexp_vars cv SUBSET set_of_list vs)) eqs ==>
         s' = s /\
         (!err. res = M_failure err ==> err = holKernel_Failure (implode
           "timeout")) /\
         (!cvs'. res = M_success cvs' ==>
           ALL2 (\cv cv'. (|-) (thy,[]) ((===) (cexp2term cv) (cexp2term
             cv')))
                     cvs cvs')))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
