(* ======================================================== *)
(*  candle_kernelProg: ported from HOL4's
    candle/prover/candle_kernelProgScript.sml
    A definition theory, with no definitions and 7 theorems.  Needed
    by 8 files of the port.  *)
(* ======================================================== *)

(*
  Adds Candle specific functions to the kernel module from ml_hol_kernel_funsProg
*)

needs "candle/prover/compute/compute.ml";;
needs "candle/prover/compute/compute_eval.ml";;
needs "candle/prover/compute/compute_syntax.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/standard/ml_kernel/runtime_check.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_kernelProg"
  ["compute"; "compute_eval"; "compute_syntax"; "ml_hol_kernel_funsProg";
   "ml_monad_translator"; "ml_prog"; "ml_translator"; "runtime_check"];;
(* HOL4 ancestors outside the port: print_thm compute_pmatch *)
(* compute: *)

(* HOL4 candle_kernelProgScript.sml:13: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:15: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:17: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:19-23: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:25: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:27-36: ML code, not ported *)
(* compute primitive *)

(* HOL4 candle_kernelProgScript.sml:39: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:41-47: ML code, not ported *)

(* [local] *)
let dest_cexp_side = prove
 (`!x. dest_cexp_side x`,
  CHEAT_TAC);;

(* HOL4 candle_kernelProgScript.sml:56: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:58-63: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:65: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:67: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:69: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:71: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:73-74: ML code, not ported *)

(* [local] *)
let check_cexp_closed_ind = prove
 (`check_cexp_closed_ind`,
  CHEAT_TAC);;

(* HOL4 candle_kernelProgScript.sml:89-90: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:92: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:94-95: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:97-100: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:102-122: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:124-125: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:127: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:129-133: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:135-136: ML code, not ported *)

(* extract the interesting theorem *)

(* HOL4 candle_kernelProgScript.sml:142-144: ML code, not ported *)

(* HOL4 candle_kernelProgScript.sml:146-153: a theorem that HOL4 states as
   the value of an ML expression: candle_prog_thm *)

(* extract some other other theorems *)

(* HOL4 candle_kernelProgScript.sml:157: a theorem that HOL4 states as the
   value of an ML expression: EqualityType_TYPE_TYPE *)

(* HOL4 candle_kernelProgScript.sml:159: a theorem that HOL4 states as the
   value of an ML expression: EqualityType_TERM_TYPE *)

(* HOL4 candle_kernelProgScript.sml:161: a theorem that HOL4 states as the
   value of an ML expression: EqualityType_THM_TYPE *)

(* HOL4 candle_kernelProgScript.sml:163: a theorem that HOL4 states as the
   value of an ML expression: EqualityType_UPDATE_TYPE *)

(* HOL4 candle_kernelProgScript.sml:165: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
