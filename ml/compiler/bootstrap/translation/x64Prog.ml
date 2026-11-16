(* ======================================================== *)
(*  x64Prog: ported from HOL4's
    compiler/bootstrap/translation/x64ProgScript.sml
    A definition theory, with 1 definition and 19 theorems.  Needed
    by arm8Prog.ml.  *)
(* ======================================================== *)

(*
  Translate the x64 instruction encoder and x64-specific config.
*)

needs "compiler/bootstrap/translation/from_pancake64Prog.ml";;
needs "lib/bitstring.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "x64Prog"
  ["asmProps"; "asmSem"; "evaluate"; "from_pancake64Prog"; "ml_translator"];;

let _ = do_list hide_constant ["C"];;
(* HOL4 ancestors outside the port: x64_target x64 *)

(* HOL4 x64ProgScript.sml:10-15: ML code, not ported *)

(* HOL4 x64ProgScript.sml:19-20: ML code, not ported *)

(* HOL4 x64ProgScript.sml:22: ML code, not ported *)

(* HOL4 x64ProgScript.sml:24-25: ML code, not ported *)

(* NOT_NIL_AND_LEMMA[local] *)
let x64Prog_NOT_NIL_AND_LEMMA = prove
 (`(~(b = []) /\ x) = if b = [] then F else x`,
  CHEAT_TAC);;

(* HOL4 x64ProgScript.sml:33: ML code, not ported *)

(* HOL4 x64ProgScript.sml:35-51: ML code, not ported *)

(* HOL4 x64ProgScript.sml:53: ML code, not ported *)

(* v2w_rw[local] *)
let x64Prog_v2w_rw = prove
 (`v2w [P] = if P then (n2w 1) else (n2w 0)`,
  CHEAT_TAC);;

(* HOL4 x64ProgScript.sml:61: ML code, not ported *)

(* [local] *)
let zreg2num_totalnum2zerg = prove
 (`Zreg2num (total_num2Zreg n) = if n < 16 then n else 0`,
  CHEAT_TAC);;

(* [local] *)
let zreg2num_num2zerg_MOD8 = prove
 (`Zreg2num (num2Zreg (n MOD 8)) = n MOD 8`,
  CHEAT_TAC);;

(* [local] *)
let n2w_MOD8_simps = prove
 (`(n2w (n MOD 8):word4) = (n2w 0) /\
   (n2w (n MOD 8):word4) = n2w (n MOD 8) /\
   BITS 3 0 (n MOD 8) = n MOD 8`,
  CHEAT_TAC);;

(* Zbinop_name2num_x64_sh[local] *)
let zbinop_name2num_x64_sh = prove
 (`!s. Zbinop_name2num (x64_sh s) =
   match s with
     Lsl -> 12
   | Lsr -> 13
   | Asr -> 15
   | Ror -> 9`,
  CHEAT_TAC);;

(* [local] *)
let x64_sh_notZtest = prove
 (`!s. ~((x64_sh s) = Ztest)`,
  CHEAT_TAC);;

(* [local] *)
let exh_if_collapse = prove
 (`((if P then Ztest else Zcmp) = Ztest) <=> P`,
  CHEAT_TAC);;

(* [local] *)
let is_rax_zr_thm = prove
 (`is_rax (Zr (total_num2Zreg n)) <=>
   n = 0 \/ n >= 16`,
  CHEAT_TAC);;

(* [local] *)
let eq_rcx_thm = prove
 (`total_num2Zreg n = RCX <=> n = 1`,
  CHEAT_TAC);;

(* commute list case, option case and if *)
(* [local] *)
let case_ifs = prove
 (`((match
     (if P then
       l1
     else l2) with
     [] -> A
   | ls -> B ls) = if P then match l1 with [] -> A | ls -> B ls else match
     l2 with [] -> A | ls -> B ls)`,
  CHEAT_TAC);;

(* [local] *)
let case_ifs2 = prove
 (`((match
     (if P then
       SOME (a,b,c)
     else NONE) with
     NONE -> A
   | SOME (a,b,c) -> B a b c) = if P then B a b c else A)`,
  CHEAT_TAC);;

(* [local] *)
let if_neq = prove
 (`~((if P then [x] else []) = []) <=> P`,
  CHEAT_TAC);;

(* HOL4 x64ProgScript.sml:167: ML code, not ported *)

(* HOL4 x64ProgScript.sml:169-176: ML code, not ported *)

(* HOL4 x64ProgScript.sml:178-187: ML code, not ported *)

(* HOL4 x64ProgScript.sml:189: ML code, not ported *)

(* HOL4 x64ProgScript.sml:191: ML code, not ported *)

(* [local] *)
let simp_rw = prove
 (`(if (((n2w 1):word4) = (n2w 1)) then (n2w 1) else (n2w 0):word4) =
   ((n2w 1) && n2w (if n < 16 then n else 0) >>> 3)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_BIND_rw = prove
 (`list_CASE (LIST_BIND (if P then A else B) f) C D =
   if P then
     list_CASE (LIST_BIND A f) C D
   else list_CASE (LIST_BIND B f) C D`,
  CHEAT_TAC);;

(* [local] *)
let COND_RAND_pair = prove
 (`(\(a,b). f a b) (if P then A else B) =
   (if P then (\(a,b). f a b) A else (\(a,b). f a b) B)`,
  CHEAT_TAC);;

(* HOL4 x64ProgScript.sml:218-224: ML code, not ported *)

(* HOL4 x64ProgScript.sml:226-227: ML code, not ported *)

(* HOL4 x64ProgScript.sml:229-232: ML code, not ported *)

(* HOL4 x64ProgScript.sml:234: a comment with ML code after it, which the
   port does not have *)
(* HOL4 x64ProgScript.sml:235-237: ML code, not ported *)

(* HOL4 x64ProgScript.sml:239-241: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:243-245: ML code, not ported *)

(* HOL4 x64ProgScript.sml:247-249: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:251-252: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:254-257: ML code, not ported *)

(* HOL4 x64ProgScript.sml:259-262: ML code, not ported *)

(* HOL4 x64ProgScript.sml:264-266: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:268-270: ML code, not ported *)

(* HOL4 x64ProgScript.sml:272-274: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:276-277: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:279-281: ML code, not ported *)

(* HOL4 x64ProgScript.sml:283-284: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:286-289: ML code, not ported *)

(*TODO: can commute the NONE and if *)
(* HOL4 x64ProgScript.sml:292-295: the ML values that the definitions below
   antiquote *)

(* FP *)
(* HOL4 x64ProgScript.sml:298: ML code, not ported *)

(* HOL4 x64ProgScript.sml:300-305: ML code, not ported *)

(* HOL4 x64ProgScript.sml:307-308: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:310-313: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:315-316: ML code, not ported *)

(* HOL4 x64ProgScript.sml:318-324: ML code, not ported *)

(* HOL4 x64ProgScript.sml:326-327: ML code, not ported *)

(* HOL4 x64ProgScript.sml:329-332: ML code, not ported *)

(*bconv takes too long on this one*)
(* HOL4 x64ProgScript.sml:335-345: ML code, not ported *)

(* [local] *)
let case_append = prove
 (`(match APPEND (APPEND a [b; c]) d with [] -> x | ls -> ls) = APPEND
  (APPEND a [b; c]) d`,
  CHEAT_TAC);;

(* HOL4 x64ProgScript.sml:353-357: ML code, not ported *)

(* HOL4 x64ProgScript.sml:359-361: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:363: ML code, not ported *)

(* [local] *)
let case_append2 = prove
 (`(match APPEND a [b; c] with [] -> e | ls -> ls) = APPEND a [b; c]`,
  CHEAT_TAC);;

(* HOL4 x64ProgScript.sml:371-373: ML code, not ported *)

(* HOL4 x64ProgScript.sml:375-377: ML code, not ported *)

(* HOL4 x64ProgScript.sml:379-380: the ML values that the definitions below
   antiquote *)

(* HOL4 x64ProgScript.sml:382-392: ML code, not ported *)

let x64_enc_Const_def = new_definition
  `x64_enc_Const n c = x64_enc (asm_Inst (asm_Const n c))`;;

(* HOL4 x64ProgScript.sml:499-510: ML code, not ported *)

(* HOL4 x64ProgScript.sml:512-523: ML code, not ported *)

(* HOL4 x64ProgScript.sml:525-539: ML code, not ported *)

(* HOL4 x64ProgScript.sml:541-555: ML code, not ported *)

(* HOL4 x64ProgScript.sml:557-601: ML code, not ported *)

(* HOL4 x64ProgScript.sml:603: ML code, not ported *)

(* HOL4 x64ProgScript.sml:605: ML code, not ported *)

(* HOL4 x64ProgScript.sml:607: ML code, not ported *)

(* HOL4 x64ProgScript.sml:609: a theorem that HOL4 states as the value of an
   ML expression: x64_config_v_thm *)

(* HOL4 x64ProgScript.sml:611: ML code, not ported *)

(* HOL4 x64ProgScript.sml:613: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["C"];;

(* and the interface *)
let _ = unhide_overloads ();;
