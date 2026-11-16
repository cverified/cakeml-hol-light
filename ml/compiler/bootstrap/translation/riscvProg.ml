(* ======================================================== *)
(*  riscvProg: ported from HOL4's
    compiler/bootstrap/translation/riscvProgScript.sml
    A definition theory, with 1 definition and 5 theorems.  Needed
    by mipsProg.ml.  *)
(* ======================================================== *)

(*
  Translate the RISC-V instruction encoder and RISC-V-specific config.
*)

needs "compiler/bootstrap/translation/arm8Prog.ml";;
needs "lib/bitstring.ml";;
needs "semantics/evaluate.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "riscvProg"
  ["arm8Prog"; "evaluate"; "ml_translator"];;
(* HOL4 ancestors outside the port: riscv_target riscv *)

(* HOL4 riscvProgScript.sml:10-15: ML code, not ported *)

(* HOL4 riscvProgScript.sml:19-20: ML code, not ported *)

(* HOL4 riscvProgScript.sml:22: ML code, not ported *)

(* HOL4 riscvProgScript.sml:24-25: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let riscvProg_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 riscvProgScript.sml:33: ML code, not ported *)

(* HOL4 riscvProgScript.sml:35-49: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 riscvProgScript.sml:53-54: ML code, not ported *)

(* HOL4 riscvProgScript.sml:56: ML code, not ported *)

(* HOL4 riscvProgScript.sml:58: ML code, not ported *)

(* HOL4 riscvProgScript.sml:60-61: the ML values that the definitions below
   antiquote *)

(* v2w_rw[local] *)
let riscvProg_v2w_rw = prove
 (`v2w [P] = if P then (n2w 1) else (n2w 0)`,
  CHEAT_TAC);;

(* HOL4 riscvProgScript.sml:69-72: ML code, not ported *)

(* HOL4 riscvProgScript.sml:74-84: ML code, not ported *)

(* HOL4 riscvProgScript.sml:86-89: ML code, not ported *)

(* HOL4 riscvProgScript.sml:91: ML code, not ported *)

(* HOL4 riscvProgScript.sml:93-97: ML code, not ported *)

(* HOL4 riscvProgScript.sml:99-100: ML code, not ported *)

(* HOL4 riscvProgScript.sml:102-105: ML code, not ported *)

(* HOL4 riscvProgScript.sml:107-109: ML code, not ported *)

(* HOL4 riscvProgScript.sml:111-113: ML code, not ported *)

(* HOL4 riscvProgScript.sml:115-118: ML code, not ported *)

(* HOL4 riscvProgScript.sml:120-122: ML code, not ported *)

(* HOL4 riscvProgScript.sml:124-125: the ML values that the definitions
   below antiquote *)

(* HOL4 riscvProgScript.sml:127-130: ML code, not ported *)

(* HOL4 riscvProgScript.sml:132-139: ML code, not ported *)

(* HOL4 riscvProgScript.sml:141-142: the ML values that the definitions
   below antiquote *)

(* HOL4 riscvProgScript.sml:144-151: ML code, not ported *)

(* HOL4 riscvProgScript.sml:153-154: the ML values that the definitions
   below antiquote *)

(* HOL4 riscvProgScript.sml:156-157: the ML values that the definitions
   below antiquote *)

(* HOL4 riscvProgScript.sml:159-161: ML code, not ported *)

(* HOL4 riscvProgScript.sml:163-164: the ML values that the definitions
   below antiquote *)

(* HOL4 riscvProgScript.sml:166-169: ML code, not ported *)

(* HOL4 riscvProgScript.sml:171-174: the ML values that the definitions
   below antiquote *)

(* [local] *)
let notw2w = prove
 (`!a. ~(w2w a) = (--(n2w 1) ?? (w2w a))`,
  CHEAT_TAC);;

(* HOL4 riscvProgScript.sml:182: ML code, not ported *)

(* HOL4 riscvProgScript.sml:184-187: the ML values that the definitions
   below antiquote *)

(* [local] *)
let if_eq1w = prove
 (`((if w2w (c >>> m && ((n2w 1):word64)) = ((n2w 1):word20) then (n2w 1):word1
  else (n2w 0)) && (n2w 1)) =
   w2w (c >>> m && (n2w 1))`,
  CHEAT_TAC);;

(* HOL4 riscvProgScript.sml:198-201: ML code, not ported *)

(* HOL4 riscvProgScript.sml:203-209: ML code, not ported *)

(* HOL4 riscvProgScript.sml:211-212: ML code, not ported *)

(* HOL4 riscvProgScript.sml:214-217: ML code, not ported *)

(* HOL4 riscvProgScript.sml:219-222: ML code, not ported *)

(* HOL4 riscvProgScript.sml:224-226: the ML values that the definitions
   below antiquote *)

(* HOL4 riscvProgScript.sml:228-231: ML code, not ported *)

(* HOL4 riscvProgScript.sml:233-235: ML code, not ported *)

(* HOL4 riscvProgScript.sml:237-239: ML code, not ported *)

(* HOL4 riscvProgScript.sml:241-243: the ML values that the definitions
   below antiquote *)

(* HOL4 riscvProgScript.sml:245-254: ML code, not ported *)

let riscv_enc_Const_def = new_definition
  `riscv_enc_Const n c = riscv_enc (word_Inst (asm_Const n c))`;;

(* HOL4 riscvProgScript.sml:373-414: ML code, not ported *)

(* HOL4 riscvProgScript.sml:416: ML code, not ported *)

(* HOL4 riscvProgScript.sml:418: ML code, not ported *)

(* HOL4 riscvProgScript.sml:420: ML code, not ported *)

(* HOL4 riscvProgScript.sml:422-423: a theorem that HOL4 states as the value
   of an ML expression: riscv_config_v_thm *)


(* HOL4 riscvProgScript.sml:426: ML code, not ported *)

(* HOL4 riscvProgScript.sml:428: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
