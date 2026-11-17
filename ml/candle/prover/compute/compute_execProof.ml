(* ======================================================== *)
(*  compute_execProof: ported from HOL4's
    candle/prover/compute/compute_execProofScript.sml
    A proof theory about compute_exec.ml, with 4 definitions and 20
    theorems.  Needed by computeProof.ml.  *)
(* ======================================================== *)

(*
   Verification of fast interpreter for the Candle compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/prover/compute/compute_evalProof.ml";;
needs "candle/prover/compute/compute_exec.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/prover/compute/compute_syntaxProof.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compute_execProof"
  ["compute_eval"; "compute_evalProof"; "compute_exec"; "compute_syntax";
   "holKernel"; "holKernelProof"; "holSyntax"; "holSyntaxExtra";
   "holSyntaxLib"; "ml_monadBase"; "mlvector"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["vars","vars"];;


(* verification *)

let from_cv_def,from_cv_ind = define_guess
  `(from_cv (((holSyntax_Tyapp (implode "num") []) n):cv) =
    ((holSyntax_Tyapp (implode "num") []) n:compute_exp)) /\
   (from_cv (compute_exec_Pair x y) = ((compute_exec_Pair (from_cv x)
    (from_cv y)):compute_exp))`;;
add_simp from_cv_def;;

let from_res_def = define_cases
  `(from_res f (M_success v) = M_success (f v)) /\
   (from_res f (M_failure e) = M_failure e)`;;
add_simp from_res_def;;

let code_rel = cake_inductive
  `(!eqs v1 n v2.
      ~(MEM n v1) ==>
      compute_execProof_code_rel eqs (APPEND (APPEND v1 [n]) v2)
        ((compute_exec_Var n):compute_exp) ((compute_exec_Var (LENGTH v1)):ce))
        /\
   (!eqs vars' n.
      compute_execProof_code_rel eqs vars' ((holSyntax_Tyapp (implode "num")
        []) n) (compute_exec_Const n)) /\
   (!eqs vars' x y x1 y1.
      compute_execProof_code_rel eqs vars' x x1 /\
      compute_execProof_code_rel eqs vars' y y1 ==>
      compute_execProof_code_rel eqs vars' (compute_exec_Pair x y)
        (compute_exec_Binop compute_exec_Pair x1 y1)) /\
   (!eqs vars' x y z x1 y1 z1.
      compute_execProof_code_rel eqs vars' x x1 /\
      compute_execProof_code_rel eqs vars' y y1 /\
      compute_execProof_code_rel eqs vars' z z1 ==>
      compute_execProof_code_rel eqs vars' (compute_exec_If x y z)
        (compute_exec_If x1 y1 z1)) /\
   (!eqs vars' s x y x1 y1.
      compute_execProof_code_rel eqs vars' x x1 /\
      compute_execProof_code_rel eqs (CONS s vars') y y1 ==>
      compute_execProof_code_rel eqs vars' (compute_syntax_Let s x y)
        (compute_exec_Let x1 y1)) /\
   (!eqs vars' xs xs1 f l body n.
      ALL2 (compute_execProof_code_rel eqs vars') xs xs1 /\
      n < LENGTH eqs /\ EL n eqs = (f,l,body) /\
      LENGTH l = LENGTH xs /\
      (!k. k < n ==> ~(FST (EL k eqs) = f)) ==>
      compute_execProof_code_rel eqs vars' (compute_exec_App f xs)
        (compute_exec_App n xs1)) /\
   (!eqs vars' x x1 m.
      compute_execProof_code_rel eqs vars' x x1 ==>
      compute_execProof_code_rel eqs vars' (compute_syntax_Uop m x)
        (compute_exec_Monop (monop m) x1)) /\
   (!eqs vars' x y x1 y1 b.
      compute_execProof_code_rel eqs vars' x x1 /\
      compute_execProof_code_rel eqs vars' y y1 ==>
      compute_execProof_code_rel eqs vars' (compute_exec_Binop b x y)
        (compute_exec_Binop (compute_exec_binop b) x1 y1))`;;

let option_ALOOKUP = prove
 (`!eqs n f l body s.
     n < LENGTH eqs /\
     EL n eqs = (f,l,body) /\
     (!k. k < n ==> ~(FST (EL k eqs) = f)) ==>
     compute_eval_option (ALOOKUP eqs) f s = (M_success (l,body),s)`,
  CHEAT_TAC);;

let LESS_LENGTH_env_lookup = prove
 (`!xs n. n < LENGTH xs ==> env_lookup n xs = EL n xs`,
  CHEAT_TAC);;

let compute_eval_from_cv = prove
 (`!x s ck eqs. compute_eval ck eqs (from_cv x) s = (M_success (from_cv x),s)`,
  CHEAT_TAC);;

let compile_eval_list_length = prove
 (`!cvs xs ck ceqs s s'.
     compute_eval_list ck ceqs cvs s = (M_success xs,s') ==> LENGTH xs =
       LENGTH cvs`,
  CHEAT_TAC);;

let cexp_value_from_cv = prove
 (`!y. cexp_value (from_cv y)`,
  CHEAT_TAC);;

(* [local] *)
let compute_execProof_cexp_vars_def = cexp_vars_def;;
add_simp compute_execProof_cexp_vars_def;;

(* HOL4 compute_execProofScript.sml:110-115: the definition *)

let do_uop_from_cv = prove
 (`do_uop uop (from_cv a) s = (M_success (from_cv (monop uop a)),s)`,
  CHEAT_TAC);;

let from_cv_11 = prove
 (`!x y. from_cv x = from_cv y <=> x = y`,
  CHEAT_TAC);;

let do_binop_from_cv = prove
 (`do_binop bop (from_cv a) (from_cv b) s = (M_success (from_cv
  (compute_exec_binop bop a b)),s)`,
  CHEAT_TAC);;

let env_lookup_lemma = prove
 (`!v1 env s v2.
     MAP FST env = APPEND (APPEND v1 [s]) v2 /\ ~(MEM s v1) ==>
     (?z.
       ALOOKUP (MAP (\(x,y). (x,from_cv y)) env) s = SOME (from_cv z) /\
       env_lookup (LENGTH v1) (MAP SND env) = z)`,
  CHEAT_TAC);;

let subst_from_cv = prove
 (`!v xs. compute_eval_subst xs (from_cv v) = from_cv v`,
  CHEAT_TAC);;

let subst_subst = prove
 (`!e xs ys.
     ALL (\x. ?v. SND x = from_cv v) ys ==>
     compute_eval_subst xs (compute_eval_subst ys e) = compute_eval_subst
       (APPEND ys xs) e`,
  CHEAT_TAC);;

let alookup_subst = prove
 (`!e xs ys.
     ALOOKUP xs = ALOOKUP ys ==>
     compute_eval_subst xs e = compute_eval_subst ys e`,
  CHEAT_TAC);;

let subst_cons_lemma = prove
 (`compute_eval_subst [s,from_cv a] (compute_eval_subst
        (FILTER (\(n,x). ~(n = s)) (MAP (\(x,y). (x,from_cv y)) env)) e2) =
   compute_eval_subst (MAP (\(x,y). (x,from_cv y)) (CONS (s,a) env)) e2`,
  CHEAT_TAC);;

let subst_eq_subst_lemma = prove
 (`!s xs ys.
     ALL_DISTINCT (MAP FST xs) /\ xs = REVERSE ys ==>
     compute_eval_subst xs s = compute_eval_subst ys s`,
  CHEAT_TAC);;

let exec_thm = prove
 (`(!ck eqs e res env e1 s s1.
     compute_eval ck eqs (compute_eval_subst (MAP (\(x,y). (x,from_cv y))
       env) e) s = (res,s1) /\
     cexp_vars e SUBSET set_of_list (MAP FST env) /\ eqs_ok eqs /\
     compute_execProof_code_rel eqs (MAP FST env) e e1 ==>
     (?res1.
       exec (build_funs eqs) (MAP SND env) ck e1 s = (res1,s1) /\
       res = from_res from_cv res1)) /\
   (!ck eqs e res env e1 s s1 acc.
     compute_eval_list ck eqs (MAP (compute_eval_subst (MAP (\(x,y).
       (x,from_cv y)) env)) e) s = (res,s1) /\
     ALL (\e. cexp_vars e SUBSET set_of_list (MAP FST env)) e /\ eqs_ok eqs
       /\
     ALL2 (compute_execProof_code_rel eqs (MAP FST env)) e e1 ==>
     (?res1.
       exec_list (build_funs eqs) (MAP SND env) ck e1 acc s = (res1,s1) /\
       from_res (\xs. APPEND (REVERSE xs) (MAP from_cv acc)) res =
         from_res (MAP from_cv) res1))`,
  CHEAT_TAC);;

(* HOL4 compute_execProofScript.sml:367-371: a theorem that HOL4 states as
   the value of an ML expression: exec_lemma *)

(* [local] *)
let LIST_REL_MAP_lemma = prove
 (`!xs. ALL2 R xs (MAP f xs) = ALL (\x. R x (f x)) xs`,
  CHEAT_TAC);;

let code_rel_to_ce = prove
 (`!e vars' eqs.
     cexp_vars e SUBSET set_of_list vars' /\ cexp_consts_ok eqs e /\
     ALL (\(n,args,body). cexp_vars body SUBSET set_of_list args
       /\ cexp_consts_ok eqs body) eqs /\
     ALL_DISTINCT (MAP FST eqs) ==>
     compute_execProof_code_rel eqs vars' e (to_ce eqs vars' e)`,
  CHEAT_TAC);;

let compute_eval_eq_exec = prove
 (`cexp_vars e = {} /\
   cexp_consts_ok eqs e /\
   ALL_DISTINCT (MAP FST eqs) /\
   ALL (\(n,args,body).
     ALL_DISTINCT args /\
     cexp_vars body SUBSET set_of_list args /\
     cexp_consts_ok eqs body) eqs ==>
   compute_eval ck eqs e s =
     (let (r,s1) = exec (build_funs eqs) [] ck (to_ce eqs [] e) s in
       (from_res from_cv r,s1))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
