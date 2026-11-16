(* ======================================================== *)
(*  compute_exec: ported from HOL4's
    candle/prover/compute/compute_execScript.sml
    A definition theory, with 22 definitions, 2 datatypes and no
    theorems.  Needed by compute.ml, computeProof.ml,
    compute_execProof.ml and fmap_cv.ml.  *)
(* ======================================================== *)

(*
   Fast interpreter function for the Candle compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "lib/regexp_compiler.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compute_exec"
  ["compute_eval"; "compute_syntax"; "holKernel"; "holKernelProof";
   "holSyntax"; "holSyntaxExtra"; "holSyntaxLib"; "ml_monadBase"; "mlvector"];;


(* -------------------------------------------------------------------------
 * st_ex_monad setup
 * ------------------------------------------------------------------------- *)

(* HOL4 compute_execScript.sml:16-23: ML code, not ported *)

(* HOL4 compute_execScript.sml:29: the overload return, which the port
   expands *)
(* HOL4 compute_execScript.sml:30: the overload failwith, which the port
   expands *)
(* HOL4 compute_execScript.sml:31: the overload handle, which the port
   expands *)
(* HOL4 compute_execScript.sml:32: the overload error, which the port
   expands *)
(* HOL4 compute_execScript.sml:33: the overload timeout, which the port
   expands *)

(* -------------------------------------------------------------------------
 * execute engine
 * ------------------------------------------------------------------------- *)

let cv_INDUCT,cv_RECURSION = define_datatype
  "cv =
     compute_exec_Num num
   | compute_exec_Pair cv cv";;

let ce_INDUCT,ce_RECURSION = define_datatype
  "ce =
     compute_exec_Const num
   | compute_exec_Var num
   | compute_exec_Monop (cv->cv) ce
   | compute_exec_Binop (cv->cv->cv) ce ce
   | compute_exec_App num (ce list)
   | compute_exec_If ce ce ce
   | compute_exec_Let ce ce";;

let env_lookup_def,env_lookup_ind = define_guess
  `(env_lookup n [] = compute_exec_Num 0) /\
   (env_lookup n (CONS x xs) =
      if n = 0 then x else env_lookup (n - 1) xs)`;;

let get_code_def = new_definition
  `get_code f funs =
     if f < length funs then
       st_ex_return (regexp_compiler_sub funs f)
     else (raise_Failure (implode "timeout"))`;;

(* the termination relation that HOL4 gives is
     inv_image ((<) LEX (<))
                      (\x. match x with INL (_,_,ck,cv) -> (ck,ce_size cv)
                                  | INR (_,_,ck,cv,_) -> (ck,list_size ce_size
                                    cv))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 compute_execScript.sml:110-115: the tactic that proves the
   termination *)
let exec_def,exec_ind = define_guess
  `(exec funs env ck (compute_exec_Const n) =
      st_ex_return (compute_exec_Num n)) /\
   (exec funs env ck (compute_exec_Var n) =
      st_ex_return (env_lookup n env)) /\
   (exec funs env ck (compute_exec_Monop m x) =
      st_ex_bind (exec funs env ck x) (\v.
        st_ex_return (m v))) /\
   (exec funs env ck (compute_exec_Binop b x y) =
      st_ex_bind (exec funs env ck x) (\v. st_ex_bind (exec funs env ck y)
          (\w.
        st_ex_return (b v w)))) /\
   (exec funs env ck (compute_exec_App f xs) =
      (if ck = 0 then (raise_Failure (implode "timeout")) else st_ex_bind
          (exec_list funs env ck xs []) (\vs. st_ex_bind (get_code f funs) (\c.
        exec funs vs (ck - 1) c)))) /\
   (exec funs env ck (compute_exec_Let x y) =
      (if ck = 0 then (raise_Failure (implode "timeout")) else st_ex_bind
          (exec funs env ck x) (\v.
        exec funs (CONS v env) (ck - 1) y))) /\
   (exec funs env ck (compute_exec_If x y z) =
      st_ex_bind (exec funs env ck x) (\v.
        exec funs env ck (match v with compute_exec_Num n -> if n = 0 then
            z else y
                          | compute_exec_Pair _ _ -> z))) /\
   (exec_list funs env ck [] acc =
      st_ex_return acc) /\
   (exec_list funs env ck (CONS x xs) acc =
      st_ex_bind (exec funs env ck x) (\v.
        exec_list funs env ck xs (CONS v acc)))`;;

let monop_fst_def = new_definition
  `monop_fst = (\x. match x with compute_exec_Pair y z -> y | _ ->
  compute_exec_Num 0)`;;

let monop_snd_def = new_definition
  `monop_snd = (\x. match x with compute_exec_Pair y z -> z | _ ->
  compute_exec_Num 0)`;;

let monop_ispair_def = new_definition
  `monop_ispair = (\x. match x with compute_exec_Pair y z ->
  compute_exec_Num 1 | _ -> compute_exec_Num 0)`;;

let monop_def = new_definition
  `monop IsPair =
   match IsPair with
     Fst -> monop_fst
   | Snd -> monop_snd
   | IsPair -> monop_ispair`;;

let to_num_def = define_cases
  `(to_num (compute_exec_Pair _ _) = 0) /\
   (to_num ((compute_exec_Num n):cv) = n)`;;
add_simp to_num_def;;

let cv_T_def = new_definition
  `cv_T = (compute_exec_Num 1:cv)`;;

let cv_F_def = new_definition
  `cv_F = (compute_exec_Num 0:cv)`;;

let binop_add_def = new_definition
  `binop_add = (\x y. compute_exec_Num (to_num x + to_num y))`;;

let binop_sub_def = new_definition
  `binop_sub = (\x y. compute_exec_Num (to_num x - to_num y))`;;

let binop_mul_def = new_definition
  `binop_mul = (\x y. compute_exec_Num (to_num x * to_num y))`;;

let binop_div_def = new_definition
  `binop_div = (\x y. compute_exec_Num (let k = to_num y in if k = 0 then 0
  else to_num x DIV k))`;;

let binop_mod_def = new_definition
  `binop_mod =
     (\x y. compute_exec_Num (let k = to_num y in if k = 0 then to_num x
       else to_num x MOD k))`;;

let binop_eq_def = new_definition
  `binop_eq = (\x y. if x = y then cv_T else cv_F)`;;

let binop_less_def = new_definition
  `binop_less =
     (\x y. match x with compute_exec_Pair _ _ -> cv_F
           | compute_exec_Num n -> (match y with compute_exec_Pair _ _ ->
             cv_F
                         | compute_exec_Num m -> if n < m then cv_T else
                           cv_F))`;;

let binop_def = new_definition
  `compute_exec_binop op =
     match op with compute_syntax_Add -> binop_add
     | compute_syntax_Sub -> binop_sub
     | compute_syntax_Mul -> binop_mul
     | compute_syntax_Div -> binop_div
     | compute_syntax_Mod -> binop_mod
     | compute_syntax_Eq -> binop_eq
     | compute_syntax_Less -> binop_less`;;

(* the termination relation that HOL4 gives is
     MEASURE (\(eqs,args,e). compute_exp_size e)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let to_ce_def,to_ce_ind = define_guess
  `(to_ce (eqs:(mlstring#mlstring list#compute_exp) list)
      args ((compute_syntax_Var v):compute_exp) = compute_syntax_Var
          (mlvector_findi v args)) /\
   (to_ce (eqs:(mlstring#mlstring list#compute_exp) list) args
    (compute_syntax_Num n) = compute_exec_Const n) /\
   (to_ce (eqs:(mlstring#mlstring list#compute_exp) list) args
    (compute_syntax_Pair x y) =
      compute_syntax_Binop compute_syntax_Pair (to_ce eqs args x)
          (to_ce eqs args y)) /\
   (to_ce (eqs:(mlstring#mlstring list#compute_exp) list) args
    (compute_syntax_If x y z) =
      compute_syntax_If (to_ce eqs args x) (to_ce eqs args y) (to_ce
          eqs args z)) /\
   (to_ce (eqs:(mlstring#mlstring list#compute_exp) list) args
    (compute_syntax_Let s x y) =
      compute_exec_Let (to_ce eqs args x) (to_ce eqs (CONS s args) y)) /\
   (to_ce (eqs:(mlstring#mlstring list#compute_exp) list) args
    (compute_syntax_Uop m x) =
      compute_exec_Monop (monop m) (to_ce eqs args x)) /\
   (to_ce (eqs:(mlstring#mlstring list#compute_exp) list) args
    (compute_syntax_Binop b x y) =
      compute_syntax_Binop (compute_exec_binop b) (to_ce eqs args x)
          (to_ce eqs args y)) /\
   (to_ce (eqs:(mlstring#mlstring list#compute_exp) list) args
    (compute_syntax_App f xs) =
      compute_syntax_App (mlvector_findi f (MAP FST eqs)) (MAP (to_ce
          eqs args) xs))`;;

let compile_to_ce_def = new_definition
  `compile_to_ce eqs (n,args,body) = to_ce eqs (REVERSE args) body`;;

let build_funs_def = new_definition
  `build_funs eqs = Vector ((MAP (compile_to_ce eqs) eqs):ce list)`;;

let cv2term_def,cv2term_ind = define_guess
  `(cv2term ((compute_exec_Num n):cv) = (\tm. holSyntax_Comb
    (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) compute_exec_Num (holSyntax_Tyapp (implode "cval") [])))
    tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL") ((\s t.
    holSyntax_Tyapp (implode "fun") [s; t]) compute_exec_Num
    compute_exec_Num)) tm) (num2bit n))) /\
   (cv2term (compute_exec_Pair p q) = (\t1 t2. holSyntax_Comb
    (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s t.
    holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
    "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
    (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (cv2term p) (cv2term
    q))`;;

(* and the interface *)
let _ = unhide_overloads ();;
