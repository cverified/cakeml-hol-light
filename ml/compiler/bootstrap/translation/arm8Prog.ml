(* ======================================================== *)
(*  arm8Prog: ported from HOL4's
    compiler/bootstrap/translation/arm8ProgScript.sml
    A definition theory, with 2 definitions and 11 theorems.  Needed
    by riscvProg.ml.  *)
(* ======================================================== *)

(*
  Translate the ARMv8 instruction encoder and ARMv8-specific config.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/bootstrap/translation/x64Prog.ml";;
needs "lib/bitstring.ml";;
needs "semantics/evaluate.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm8Prog"
  ["evaluate"; "ml_translator"; "x64Prog"];;
(* HOL4 ancestors outside the port: arm8_target arm8 *)

(* HOL4 arm8ProgScript.sml:10-15: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:21-22: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:24: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:26-27: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let arm8Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 arm8ProgScript.sml:35: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:37-51: ML code, not ported *)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
(* HOL4 arm8ProgScript.sml:55-56: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:58: ML code, not ported *)

(* [local] *)
let IS_SOME_rw = prove
 (`(if IS_SOME a then b else c) =
     match a with
     SOME v -> b
   | NONE -> c`,
  CHEAT_TAC);;

(* v2w_rw[local] *)
let arm8Prog_v2w_rw = prove
 (`v2w [P] = if P then (n2w 1) else (n2w 0)`,
  CHEAT_TAC);;

(* TODO? more Manual rewrites to get rid of MachineCode type, which probably isn't that expensive *)

(* [local] *)
let exh_machine_code = prove
 (`!v f.
   (match
   (match v with
     (n,imms,immr) ->
       ARM8 (f n imms immr)) with
   ARM8 w -> g w
   | BadCode v3 -> h) =
   match v with (n,imms,immr) ->
   g (f n imms immr)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_BIND_option = prove
 (`LIST_BIND (match P with NONE -> a | SOME v -> b v) f =
   match P with NONE -> LIST_BIND a f | SOME v -> LIST_BIND (b v) f`,
  CHEAT_TAC);;

(* [local] *)
let LIST_BIND_pair = prove
 (`LIST_BIND (match P with (l,r) -> a l r) f =
   match P with (l,r) -> LIST_BIND (a l r) f`,
  CHEAT_TAC);;

(* notw[local] *)
let arm8Prog_notw = prove
 (`!a. ~a = (--(n2w 1) ?? a)`,
  CHEAT_TAC);;

(* HOL4 arm8ProgScript.sml:112-118: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:120-131: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:133-136: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:138: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:140-148: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:150-151: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:153-156: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:158-160: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:162-165: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:167-170: ML code, not ported *)
(*TODO: fix -- avoid MachineCode type*)

(* HOL4 arm8ProgScript.sml:173: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:175: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:177-180: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:182-189: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:191-192: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:194-201: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:203-204: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:206-207: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:209-211: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:213-214: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:216-220: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:222-226: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:228: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:230-231: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:233-234: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:236-242: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:244-245: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:247-250: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:252-255: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:257-259: the ML values that the definitions below
   antiquote *)

(* HOL4 arm8ProgScript.sml:261-262: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:264-265: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:267-269: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:271-272: the ML values that the definitions below
   antiquote *)

(* the termination relation that HOL4 gives is
     MEASURE (w2n o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 arm8ProgScript.sml:282-287: the tactic that proves the termination *)
let ct_curr_def,ct_curr_ind = define_guess
  `ct_curr b (w:word64) =
      if
        (~(((n2w 1) && w) = (n2w 0)) <=> b) \/
        (if b then w = (n2w 0) else w = (n2w 0xFFFFFFFFFFFFFFFF)) then
        0
      else 1 + ct_curr b (w >>> 1)`;;

(* [local] *)
let CountTrailing_eq = prove
 (`!b w. CountTrailing (b,w) = ct_curr b w`,
  CHEAT_TAC);;

(* HOL4 arm8ProgScript.sml:305: ML code, not ported *)

(* the encoder uses two special functions that need to be hand translated *)
(* HOL4 arm8ProgScript.sml:308-310: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:312-315: ML code, not ported *)

(* TODO: already in lexerProg but not stored *)
(* HOL4 arm8ProgScript.sml:318-321: a theorem that HOL4 states as the value
   of an ML expression: l2n_side *)

(* HOL4 arm8ProgScript.sml:323-326: a theorem that HOL4 states as the value
   of an ML expression: v2n_side *)

(* notw[local] *)
let arm8Prog_notw = prove
 (`!a. ~a = (--(n2w 1) ?? (a))`,
  CHEAT_TAC);;

(* HOL4 arm8ProgScript.sml:334: the ML values that the definitions below
   antiquote *)

(* Num_rw[local] *)
let num_rw = prove
 (`(if len < (&1) then NONE
   else f ((decProg_Tyapp (implode "num") []) len)) =
   if len < (&1) then NONE
     else f ((decProg_Tyapp (implode "num") []) (abs len))`,
  CHEAT_TAC);;

(* HOL4 arm8ProgScript.sml:348-354: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:356-359: a theorem that HOL4 states as the value
   of an ML expression: decodebitmasks_side *)

(* HOL4 arm8ProgScript.sml:361-362: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:364-374: ML code, not ported *)

let arm8_enc_Const_def = new_definition
  `arm8_enc_Const n c = arm8_enc (asm_Inst (asm_Const n c))`;;

(* HOL4 arm8ProgScript.sml:493-534: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:536: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:538: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:540: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:542-543: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:545-546: a theorem that HOL4 states as the value
   of an ML expression: arm8_config_v_thm *)


(* HOL4 arm8ProgScript.sml:549: ML code, not ported *)

(* HOL4 arm8ProgScript.sml:551: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
