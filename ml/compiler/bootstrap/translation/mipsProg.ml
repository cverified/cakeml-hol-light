(* ======================================================== *)
(*  mipsProg: ported from HOL4's
    compiler/bootstrap/translation/mipsProgScript.sml
    A definition theory, with 1 definition and 2 theorems.  Needed
    by compiler64Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the MIPS instruction encoder and MIPS-specific config.
*)

needs "compiler/bootstrap/translation/riscvProg.ml";;
needs "semantics/evaluate.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mipsProg"
  ["evaluate"; "ml_translator"; "riscvProg"];;
(* HOL4 ancestors outside the port: mips_target mips *)

(* HOL4 mipsProgScript.sml:10-15: ML code, not ported *)

(* HOL4 mipsProgScript.sml:19-20: ML code, not ported *)

(* HOL4 mipsProgScript.sml:22: ML code, not ported *)

(* HOL4 mipsProgScript.sml:24-25: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let mipsProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 mipsProgScript.sml:33: ML code, not ported *)

(* HOL4 mipsProgScript.sml:35-49: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 mipsProgScript.sml:53-54: ML code, not ported *)

(* HOL4 mipsProgScript.sml:56: ML code, not ported *)

(* HOL4 mipsProgScript.sml:58: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:60-65: ML code, not ported *)

(* HOL4 mipsProgScript.sml:67-77: ML code, not ported *)

(* HOL4 mipsProgScript.sml:79-82: ML code, not ported *)

(* HOL4 mipsProgScript.sml:84-88: ML code, not ported *)

(* HOL4 mipsProgScript.sml:90: ML code, not ported *)

(* HOL4 mipsProgScript.sml:92-95: ML code, not ported *)

(* HOL4 mipsProgScript.sml:97-99: ML code, not ported *)

(* HOL4 mipsProgScript.sml:101-103: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:105-108: ML code, not ported *)

(* HOL4 mipsProgScript.sml:110: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:112: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:114-117: ML code, not ported *)

(* HOL4 mipsProgScript.sml:119-126: ML code, not ported *)

(* HOL4 mipsProgScript.sml:128-129: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:131-138: ML code, not ported *)

(* HOL4 mipsProgScript.sml:140-141: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:143-144: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:146-148: ML code, not ported *)

(* HOL4 mipsProgScript.sml:150-151: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:153-156: ML code, not ported *)

(* HOL4 mipsProgScript.sml:158-160: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:162-164: ML code, not ported *)

(* HOL4 mipsProgScript.sml:166-167: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:169-170: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:172-174: ML code, not ported *)

(* HOL4 mipsProgScript.sml:176-182: ML code, not ported *)

(* HOL4 mipsProgScript.sml:184-185: ML code, not ported *)

(* HOL4 mipsProgScript.sml:187-190: ML code, not ported *)

(* HOL4 mipsProgScript.sml:192-195: ML code, not ported *)

(* HOL4 mipsProgScript.sml:197-199: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:201-203: ML code, not ported *)

(* HOL4 mipsProgScript.sml:205-206: ML code, not ported *)

(* HOL4 mipsProgScript.sml:208-210: ML code, not ported *)

(* HOL4 mipsProgScript.sml:212-213: the ML values that the definitions below
   antiquote *)

(* HOL4 mipsProgScript.sml:215-225: ML code, not ported *)

let mips_enc_Const_def = new_definition
  `mips_enc_Const n c = mips_enc (word_Inst (asm_Const n c))`;;

(* HOL4 mipsProgScript.sml:344-385: ML code, not ported *)

(* HOL4 mipsProgScript.sml:387-425: ML code, not ported *)

(* HOL4 mipsProgScript.sml:427: ML code, not ported *)

(* HOL4 mipsProgScript.sml:429: ML code, not ported *)

(* HOL4 mipsProgScript.sml:431: ML code, not ported *)

(* HOL4 mipsProgScript.sml:433-434: a theorem that HOL4 states as the value
   of an ML expression: mips_config_v_thm *)


(* HOL4 mipsProgScript.sml:437: ML code, not ported *)

(* HOL4 mipsProgScript.sml:439: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
