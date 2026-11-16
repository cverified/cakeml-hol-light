(* ======================================================== *)
(*  arm7Prog: ported from HOL4's
    compiler/bootstrap/translation/arm7ProgScript.sml
    A definition theory, with 1 definition and 4 theorems.  Needed
    by ag32Prog.ml and compiler32Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the ARMv7 instruction encoder and ARMv7-specific config.
*)

needs "compiler/bootstrap/translation/from_pancake32Prog.ml";;
needs "compiler/bootstrap/translation/to_target32Prog.ml";;
needs "lib/bitstring.ml";;
needs "semantics/evaluate.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm7Prog"
  ["asmProps"; "asmSem"; "evaluate"; "from_pancake32Prog"; "ml_translator";
   "to_target32Prog"];;
(* HOL4 ancestors outside the port: arm7_target arm *)

(* HOL4 arm7ProgScript.sml:11-16: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:20-21: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:23: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:25-26: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let arm7Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 arm7ProgScript.sml:34: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:36-50: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 arm7ProgScript.sml:54-55: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:57: ML code, not ported *)

(* [local] *)
let v2w_rw = prove
 (`v2w [P] = if P then (n2w 1) else (n2w 0)`,
  CHEAT_TAC);;

(* [local] *)
let notw = prove
 (`!a. ~a = (--(n2w 1) ?? a)`,
  CHEAT_TAC);;

(* [local] *)
let if_ARM_BadCode = prove
 (`(match
   (if P then
      ARM c
   else BadCode d) with
     ARM w -> f w
   | BadCode w -> g w
   | Thumb w -> h w
   | Thumb2 w -> i w
   | ThumbEE w -> j w) =
   if P then f c else g d`,
  CHEAT_TAC);;

(* HOL4 arm7ProgScript.sml:88-131: code that the source has in a comment *)
(* HOL4 arm7ProgScript.sml:132-135: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:137: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:139-144: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:146-147: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:149-154: ML code, not ported *)

(* Skip *)
(* HOL4 arm7ProgScript.sml:157: ML code, not ported *)

(* Const *)
(* HOL4 arm7ProgScript.sml:160: ML code, not ported *)

(* Bop Reg *)
(* HOL4 arm7ProgScript.sml:163-164: ML code, not ported *)

(* TODO: Uses THE (EncodeARMImmediate)*)
(* Bop Imm *)
(* HOL4 arm7ProgScript.sml:168-171: ML code, not ported *)

(* Shift Imm *)
(* HOL4 arm7ProgScript.sml:174-177: ML code, not ported *)

(* Shift Ref *)
(* HOL4 arm7ProgScript.sml:180-183: ML code, not ported *)

(* Div: trivial *)

(* LongMul *)
(* HOL4 arm7ProgScript.sml:188: ML code, not ported *)

(* LongDiv: trivial *)

(* AddCarry *)
(* HOL4 arm7ProgScript.sml:193: ML code, not ported *)

(* Add/SubOverflow *)
(* HOL4 arm7ProgScript.sml:196-197: ML code, not ported *)

(* Mem Load *)
(* HOL4 arm7ProgScript.sml:200-203: ML code, not ported *)

(* Mem Load32 *)
(* HOL4 arm7ProgScript.sml:206-209: ML code, not ported *)

(* Mem Load16 *)
(* HOL4 arm7ProgScript.sml:212-215: ML code, not ported *)

(* Mem Load8 *)
(* HOL4 arm7ProgScript.sml:218-221: ML code, not ported *)

(* Mem Store *)
(* HOL4 arm7ProgScript.sml:224-227: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:229-232: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:234-237: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:239-242: ML code, not ported *)

(* FP *)
(* HOL4 arm7ProgScript.sml:245: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:247-250: ML code, not ported *)

(* Jump *)
(* HOL4 arm7ProgScript.sml:253-256: ML code, not ported *)

(* JumpCmp Reg *)
(* HOL4 arm7ProgScript.sml:259-265: ML code, not ported *)

(* JumpCmp Imm *)
(* HOL4 arm7ProgScript.sml:268-275: ML code, not ported *)

(* Call *)
(* HOL4 arm7ProgScript.sml:278-281: ML code, not ported *)

(* JumpReg *)
(* HOL4 arm7ProgScript.sml:284-287: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:289-292: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:294-295: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:297-299: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:301-311: ML code, not ported *)

let arm7_enc_Const_def = new_definition
  `arm7_enc_Const n c = arm7_enc (asm_Inst (asm_Const n c))`;;

(* HOL4 arm7ProgScript.sml:430-471: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:473-520: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:522: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:524: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:526: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:528: ML code, not ported *)


(* HOL4 arm7ProgScript.sml:531: ML code, not ported *)

(* HOL4 arm7ProgScript.sml:533: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
