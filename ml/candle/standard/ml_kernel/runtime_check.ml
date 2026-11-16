(* ======================================================== *)
(*  runtime_check: ported from HOL4's
    candle/standard/ml_kernel/runtime_checkScript.sml
    A definition theory, with 5 definitions and 1 theorem.  Needed
    by candle_kernelProg.ml, candle_kernel_vals.ml and
    ml_hol_kernel_funsProg.ml.  *)
(* ======================================================== *)

(*
  Theorems and definitions to support adding runtime type checking annotations.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "runtime_check"
  ["holKernel"; "ml_translator"; "mlstring"];;


let pure_seq_intro = prove
 (`x = y ==> (!z. x = pure_seq z y)`,
  CHEAT_TAC);;

(* It's annoying but these few functions need to appear here and in checkLib *)

(* HOL4 runtime_checkScript.sml:19-20: ML code, not ported *)

(* HOL4 runtime_checkScript.sml:22-23: ML code, not ported *)

(* HOL4 runtime_checkScript.sml:25-26: ML code, not ported *)

(* HOL4 runtime_checkScript.sml:28-32: the ML values that the definitions
   below antiquote *)

let check_ty_def,check_ty_ind = define_guess
  `(check_ty [] = one) /\
   (check_ty (CONS t1 l) = pure_seq (t1:type) (check_ty l))`;;

let check_tm_def,check_tm_ind = define_guess
  `(check_tm [] = one) /\
   (check_tm (CONS tm l) = pure_seq (tm:holSyntax_term) (check_tm l))`;;

let check_thm_def,check_thm_ind = define_guess
  `(check_thm [] = one) /\
   (check_thm (CONS th l) = pure_seq (th:thm) (check_thm l))`;;

let check_ty_ty_def,check_ty_ty_ind = define_guess
  `(check_ty_ty [] = one) /\
   (check_ty_ty (CONS (t1,t2) l) = pure_seq (t1:type) (pure_seq (t2:type)
    (check_ty_ty l)))`;;

let check_tm_tm_def,check_tm_tm_ind = define_guess
  `(check_tm_tm [] = one) /\
   (check_tm_tm (CONS (tm,tm') l) = pure_seq (tm:holSyntax_term) (pure_seq
    (tm':holSyntax_term) (check_tm_tm l)))`;;

(* and the interface *)
let _ = unhide_overloads ();;
