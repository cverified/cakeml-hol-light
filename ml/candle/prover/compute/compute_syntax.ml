(* ======================================================== *)
(*  compute_syntax: ported from HOL4's
    candle/prover/compute/compute_syntaxScript.sml
    A definition theory, with 10 definitions, 3 datatypes and 1
    theorem.  Needed by 8 files of the port.  *)
(* ======================================================== *)

(*
   Definitions of 'compute expressions' for the Candle compute primitive.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "candle/standard/syntax/holSyntaxExtra.ml";;
needs "candle/syntax-lib/holSyntaxLib.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compute_syntax"
  ["holKernel"; "holKernelProof"; "holSyntax"; "holSyntaxExtra";
   "holSyntaxLib"];;

(* Numbers, bools *)

(* HOL4 compute_syntaxScript.sml:15: the overload Num, which the port
   expands *)

(* HOL4 compute_syntaxScript.sml:17: the overload _X, which the port expands *)
(* HOL4 compute_syntaxScript.sml:18: the overload _Y, which the port expands *)
(* HOL4 compute_syntaxScript.sml:19: the overload _TRUE, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:20: the overload _FALSE, which the port
   expands *)
(* COND on numbers: *)
(* HOL4 compute_syntaxScript.sml:22-23: the overload _COND_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:24: the overload _COND, which the port
   expands *)
(* COND on booleans: *)
(* HOL4 compute_syntaxScript.sml:26-27: the overload _IF_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:28: the overload _IF, which the port
   expands *)

(* HOL4 compute_syntaxScript.sml:30: the overload _0, which the port expands *)
(* HOL4 compute_syntaxScript.sml:31: the overload _SUC_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:32: the overload _SUC, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:33: the overload _BIT0_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:34: the overload _BIT0, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:35: the overload _BIT1_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:36: the overload _BIT1, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:37: the overload _N, which the port expands *)
(* HOL4 compute_syntaxScript.sml:38: the overload _M, which the port expands *)
(* HOL4 compute_syntaxScript.sml:39: the overload _ADD_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:40: the overload _ADD, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:41: the overload _SUB_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:42: the overload _SUB, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:43: the overload _MUL_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:44: the overload _MUL, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:45: the overload _MOD_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:46: the overload _MOD, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:47: the overload _DIV_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:48: the overload _DIV, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:49: the overload _LESS_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:50: the overload _LESS, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:51: the overload _NUMERAL_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:52: the overload _NUMERAL, which the port
   expands *)

(* Compute expressions *)

(* HOL4 compute_syntaxScript.sml:56: the overload Cexp, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:57: the overload Cexp_list, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:58: the overload _P1, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:59: the overload _P2, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:60: the overload _Q1, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:61: the overload _Q2, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:62: the overload _CS, which the port
   expands *)
(*
Overload "_CEXP_NIL_TM" = “Const «[]» Cexp_list”;
Overload "_CEXP_CONS_TM" =
  “Const «::» (Fun Cexp (Fun Cexp_list Cexp_list))”;
Overload "_CEXP_CONS" = “λt1 t2. Comb (Comb _CEXP_CONS_TM t1) t2”;
 *)
(* HOL4 compute_syntaxScript.sml:69: the overload _CEXP_NUM_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:70: the overload _CEXP_NUM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:71: the overload _CEXP_PAIR_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:72: the overload _CEXP_PAIR, which the port
   expands *)

(* HOL4 compute_syntaxScript.sml:74: the overload _CEXP_VAR_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:75: the overload _CEXP_VAR, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:76-77: the overload _CEXP_ADD_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:78: the overload _CEXP_ADD, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:79-80: the overload _CEXP_SUB_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:81: the overload _CEXP_SUB, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:82-83: the overload _CEXP_MUL_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:84: the overload _CEXP_MUL, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:85-86: the overload _CEXP_MOD_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:87: the overload _CEXP_MOD, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:88-89: the overload _CEXP_DIV_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:90: the overload _CEXP_DIV, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:91-92: the overload _CEXP_LESS_TM, which
   the port expands *)
(* HOL4 compute_syntaxScript.sml:93: the overload _CEXP_LESS, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:94-95: the overload _CEXP_APP_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:96: the overload _CEXP_APP, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:97-98: the overload _CEXP_IF_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:99: the overload _CEXP_IF, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:100: the overload _CEXP_FST_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:101: the overload _CEXP_FST, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:102: the overload _CEXP_SND_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:103: the overload _CEXP_SND, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:104: the overload _CEXP_ISPAIR_TM, which
   the port expands *)
(* HOL4 compute_syntaxScript.sml:105: the overload _CEXP_ISPAIR, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:106: the overload _CEXP_EQ_TM, which the
   port expands *)
(* HOL4 compute_syntaxScript.sml:107: the overload _CEXP_EQ, which the port
   expands *)

(* Lets, “let a = b in x”: *)

(* HOL4 compute_syntaxScript.sml:111: the overload _F, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:112: the overload _LET_TM, which the port
   expands *)
(* HOL4 compute_syntaxScript.sml:113: the overload _LET, which the port
   expands *)

(* -------------------------------------------------------------------------
 * Bools
 * ------------------------------------------------------------------------- *)

let bool2term_def = define_cases
  `(bool2term F = (holSyntax_Const (implode "F") (holSyntax_Tyapp (implode
    "bool") []))) /\
   (bool2term T = (holSyntax_Const (implode "T") (holSyntax_Tyapp (implode
    "bool") [])))`;;

(* -------------------------------------------------------------------------
 * Natural numbers
 * ------------------------------------------------------------------------- *)

let num2term_def,num2term_ind = define_guess
  `(num2term 0 = (holSyntax_Const (implode "_0") compute_syntax_Num)) /\
   (num2term (SUC n) = (\tm. holSyntax_Comb (holSyntax_Const (implode
    "SUC") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
    compute_syntax_Num compute_syntax_Num)) tm) (num2term n))`;;

(* the termination relation that HOL4 gives is
     (<)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 compute_syntaxScript.sml:137-139: the tactic that proves the
   termination *)
let num2bit_def,num2bit_ind = define_guess
  `num2bit n =
     if n = 0 then (holSyntax_Const (implode "_0") compute_syntax_Num)
       else holSyntax_Comb (if n MOD 2 = 0 then (holSyntax_Const (implode
       "BIT0") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
       compute_syntax_Num compute_syntax_Num)) else (holSyntax_Const
       (implode "BIT1") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
       compute_syntax_Num compute_syntax_Num))) (num2bit (n DIV 2))`;;

(* -------------------------------------------------------------------------
 * Compute expressions
 * ------------------------------------------------------------------------- *)

let compute_syntax_binop_INDUCT,compute_syntax_binop_RECURSION =
  define_datatype
  "compute_syntax_binop =
     compute_syntax_Add
   | compute_syntax_Sub
   | compute_syntax_Mul
   | compute_syntax_Div
   | compute_syntax_Mod
   | compute_syntax_Less
   | compute_syntax_Eq";;

let uop_INDUCT,uop_RECURSION = define_datatype
  "uop =
     Fst
   | Snd
   | Ispair";;

let compute_exp_INDUCT,compute_exp_RECURSION = define_datatype
  "compute_exp =
     compute_syntax_Pair compute_exp compute_exp
   | compute_syntax_Num num
   | compute_syntax_Var mlstring
   | compute_syntax_App mlstring (compute_exp list)
   | compute_syntax_If compute_exp compute_exp compute_exp
   | compute_syntax_Let mlstring compute_exp compute_exp
   | compute_syntax_Uop uop compute_exp
   | compute_syntax_Binop compute_syntax_binop compute_exp compute_exp";;

let cexp_value_def,cexp_value_ind = define_guess
  `cexp_value x1 =
   match x1 with
     compute_syntax_Num n -> T
   | compute_syntax_Pair p q -> (cexp_value p /\ cexp_value q)
   | _ -> F`;;
add_simp cexp_value_def;;

let app_type_def = new_definition
  `app_type arity = ITER arity ((\s t. holSyntax_Tyapp (implode "fun") [s;
  t]) (holSyntax_Tyapp (implode "cval") [])) (holSyntax_Tyapp (implode
  "cval") [])`;;

let app_type = prove
 (`app_type 0 = (holSyntax_Tyapp (implode "cval") []) /\
   app_type (SUC n) = (\s t. holSyntax_Tyapp (implode "fun") [s; t])
     (holSyntax_Tyapp (implode "cval") []) (app_type n)`,
  CHEAT_TAC);;

let bop2term_def = define_cases
  `(bop2term compute_syntax_Add = (\t1 t2. holSyntax_Comb (holSyntax_Comb
    (holSyntax_Const (implode "Cexp_add") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    [])))) t1) t2)) /\
   (bop2term compute_syntax_Sub = (\t1 t2. holSyntax_Comb (holSyntax_Comb
    (holSyntax_Const (implode "Cexp_sub") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    [])))) t1) t2)) /\
   (bop2term compute_syntax_Mul = (\t1 t2. holSyntax_Comb (holSyntax_Comb
    (holSyntax_Const (implode "Cexp_mul") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    [])))) t1) t2)) /\
   (bop2term compute_syntax_Div = (\t1 t2. holSyntax_Comb (holSyntax_Comb
    (holSyntax_Const (implode "Cexp_div") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    [])))) t1) t2)) /\
   (bop2term compute_syntax_Mod = (\t1 t2. holSyntax_Comb (holSyntax_Comb
    (holSyntax_Const (implode "Cexp_mod") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    [])))) t1) t2)) /\
   (bop2term compute_syntax_Less = (\t1 t2. holSyntax_Comb (holSyntax_Comb
    (holSyntax_Const (implode "Cexp_less") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    [])))) t1) t2)) /\
   (bop2term compute_syntax_Eq = (\t1 t2. holSyntax_Comb (holSyntax_Comb
    (holSyntax_Const (implode "Cexp_eq") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) (holSyntax_Tyapp (implode "cval") []) (ast_Fun
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode
    "cval") [])))) t1) t2))`;;

let uop2term_def = define_cases
  `(uop2term Fst = (\tm. holSyntax_Comb (holSyntax_Const (implode
    "Cexp_fst") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    []))) tm)) /\
   (uop2term Snd = (\tm. holSyntax_Comb (holSyntax_Const (implode
    "Cexp_snd") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode "cval")
    []))) tm)) /\
   (uop2term Ispair = (\tm. holSyntax_Comb (holSyntax_Const (implode
    "Cexp_ispair") ((\s t. holSyntax_Tyapp (implode "fun") [s; t])
    (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp (implode
    "cval") []))) tm))`;;

(* the termination relation that HOL4 gives is
     MEASURE compute_exp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let cexp2term_def,cexp2term_ind = define_guess
  `(cexp2term (compute_syntax_Num n) = (\tm. holSyntax_Comb
    (holSyntax_Const (implode "Cexp_num") ((\s t. holSyntax_Tyapp (implode
    "fun") [s; t]) compute_syntax_Num (holSyntax_Tyapp (implode "cval")
    []))) tm) ((\tm. holSyntax_Comb (holSyntax_Const (implode "NUMERAL")
    ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) compute_syntax_Num
    compute_syntax_Num)) tm) (num2bit n))) /\
   (cexp2term (compute_syntax_Pair p q) = (\t1 t2. holSyntax_Comb
    (holSyntax_Comb (holSyntax_Const (implode "Cexp_pair") ((\s t.
    holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp (implode
    "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
    (holSyntax_Tyapp (implode "cval") [])))) t1) t2) (cexp2term p)
    (cexp2term q)) /\
   (cexp2term (compute_syntax_Uop uop p) = uop2term uop (cexp2term p)) /\
   (cexp2term (compute_syntax_Binop bop p q) = bop2term bop (cexp2term p)
    (cexp2term q)) /\
   (cexp2term (compute_syntax_If p q r) = (\t1 t2 t3. holSyntax_Comb
    (holSyntax_Comb (holSyntax_Comb (holSyntax_Const (implode "Cexp_if")
    ((\s t. holSyntax_Tyapp (implode "fun") [s; t]) (holSyntax_Tyapp
    (implode "cval") []) (ast_Fun (holSyntax_Tyapp (implode "cval") [])
    (ast_Fun (holSyntax_Tyapp (implode "cval") []) (holSyntax_Tyapp
    (implode "cval") []))))) t1) t2) t3) (cexp2term p) (cexp2term q)
    (cexp2term r)) /\
   (cexp2term (compute_syntax_Let s x y) = (\t1 t2. holSyntax_Comb
    (holSyntax_Comb (holSyntax_Const (implode "LET") ((\s t.
    holSyntax_Tyapp (implode "fun") [s; t]) ((\s t. holSyntax_Tyapp
    (implode "fun") [s; t]) (holSyntax_Tyapp (implode "cval") [])
    (holSyntax_Tyapp (implode "cval") [])) (ast_Fun (holSyntax_Tyapp
    (implode "cval") []) (holSyntax_Tyapp (implode "cval") [])))) t1) t2)
    (holSyntax_Abs (holSyntax_Var s (holSyntax_Tyapp (implode "cval") []))
    (cexp2term y)) (cexp2term x)) /\
   (cexp2term (compute_syntax_Var s) = holSyntax_Var s (holSyntax_Tyapp
    (implode "cval") [])) /\
   (cexp2term (compute_syntax_App s cs) =
      FOLDL holSyntax_Comb (holSyntax_Const s (app_type (LENGTH cs)))
          (MAP cexp2term cs))`;;

(* DIV and MOD definitions that are defined for zero (and as in HOL Light). *)

let SAFEDIV_def = new_definition
  `SAFEDIV m n = if n = 0 then 0 else m DIV n`;;

let SAFEMOD_def = new_definition
  `SAFEMOD m n = if n = 0 then m else m MOD n`;;

(* and the interface *)
let _ = unhide_overloads ();;
