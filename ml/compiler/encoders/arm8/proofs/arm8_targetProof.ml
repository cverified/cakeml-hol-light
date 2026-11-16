(* ======================================================== *)
(*  arm8_targetProof: ported from HOL4's
    compiler/encoders/arm8/proofs/arm8_targetProofScript.sml
    A proof theory, with no definitions and 21 theorems.  Needed by
    arm8_configProof.ml.  *)
(* ======================================================== *)

(*
  Prove `encoder_correct` for ARMv8
*)

needs "compiler/encoders/asm/asmProps.ml";;
needs "lib/bitstring.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "arm8_targetProof"
  ["asm"; "asmProps"; "asmSem"];;
(* HOL4 ancestors outside the port: arm8_target *)

(* HOL4 arm8_targetProofScript.sml:14: ML code, not ported *)

(* some lemmas ------------------------------------------------------------- *)

(* HOL4 arm8_targetProofScript.sml:20-25: a proof *)

let Decode_EncodeBitMask = prove
 (`(!(w:word32) n s r.
       (EncodeBitMask w = SOME (n,s,r)) ==>
       (?v. DecodeBitMasks (n,s,r,T) = SOME (w,v))) /\
   (!(w:word64) n s r.
       (EncodeBitMask w = SOME (n,s,r)) ==>
       (?v. DecodeBitMasks (n,s,r,T) = SOME (w,v)))`,
  CHEAT_TAC);;

(* HOL4 arm8_targetProofScript.sml:42: ML code, not ported *)

(* HOL4 arm8_targetProofScript.sml:44: the ML values that the definitions
   below antiquote *)

(* HOL4 arm8_targetProofScript.sml:46-49: ML code, not ported *)

(* [local] *)
let lsl_lem1 = prove
 (`!(w:word6).
       (if v2n (field 5 0 (w2v w)) + 1 < 64 then
           64
        else v2n (field 5 0 (w2v w)) + 1) = 64`,
  CHEAT_TAC);;

(* [local] *)
let lsl_lem2 = prove
 (`!(w:word6). (if w2n w + 1 < 64 then 64 else w2n w + 1) = 64`,
  CHEAT_TAC);;

(* HOL4 arm8_targetProofScript.sml:76-78: ML code, not ported *)

(* [local] *)
let lsl_lem4 = prove
 (`!n. n < 64 ==> ((64 - n + 63) MOD 64 = 63 - n)`,
  CHEAT_TAC);;

(* [local] *)
let lsl_lem5 = prove
 (`!n. n < 64 ==>
         ((v2w (PAD_LEFT F 64 (PAD_LEFT T n [])):word64) = (FCP (?_i i) <
           n))`,
  CHEAT_TAC);;

(* HOL4 arm8_targetProofScript.sml:101: the ML values that the definitions
   below antiquote *)

let lsl = prove
 (`!r q n x (wmask:word64) tmask.
       n < 64 /\
       Abbrev (r = n2w ((64 - n) MOD 64)) /\
       Abbrev (q = r + (n2w 63)) /\
       (DecodeBitMasks ((n2w 1),q,r,F) = SOME (wmask,tmask)) ==>
       (((tmask && wmask) && x #>> (w2n r)) = x << n)`,
  CHEAT_TAC);;

(* [local] *)
let lsr_lem1 = prove
 (`!n. v2n (field 5 0 (w2v (n2w n:word6))) = n MOD 64`,
  CHEAT_TAC);;

(* [local] *)
let lsr_lem2 = prove
 (`!n. v2w (rotate (PAD_LEFT F 64 (PAD_LEFT T 64 [])) n) = (word_T:word64)`,
  CHEAT_TAC);;

let lsr = prove
 (`!n x (wmask:word64) tmask.
       n < 64 /\
       (DecodeBitMasks ((n2w 1),(n2w 63),n2w n,F) = SOME (wmask,tmask)) ==>
       (((tmask && wmask) && x #>> n) = x >>> n)`,
  CHEAT_TAC);;

(* HOL4 arm8_targetProofScript.sml:196-200: a theorem that HOL4 states as
   the value of an ML expression: asr *)

(* [local] *)
let asr_lem1 = prove
 (`!m. m < 64 ==> (MIN m 64 = m)`,
  CHEAT_TAC);;

let asr2 = prove
 (`!n x (wmask:word64) tmask.
       n < 64 /\
       (DecodeBitMasks ((n2w 1),(n2w 63),n2w n,F) = SOME (wmask,tmask)) ==>
       (n2w (18446744073709551616 - 2 EXP (64 - MIN n 64)) =
        ((n2w 0xFFFFFFFFFFFFFFFF) && ~tmask))`,
  CHEAT_TAC);;

let ror = prove
 (`!(w:word64) n.
      n < 64 ==> ((v2w (shiftr (APPEND (w2v w) (w2v w)) n):word64) = w #>>
        n)`,
  CHEAT_TAC);;

let mul_long = prove
 (`!(a:word64) (b:word64).
     n2w ((w2n a * w2n b) DIV 18446744073709551616) =
     ((127 >< 64) (w2w a * (w2w b:word128)):word64)`,
  CHEAT_TAC);;

(* some custom tactics ----------------------------------------------------- *)

(* HOL4 arm8_targetProofScript.sml:268-269: ML code, not ported *)


(* -------------------------------------------------------------------------
   arm8 target_ok
   ------------------------------------------------------------------------- *)

(* [local] *)
let length_arm8_encode = prove
 (`!i. LENGTH (arm8_encode i) = 4`,
  CHEAT_TAC);;

(* [local] *)
let length_arm8_enc = prove
 (`!l. LENGTH (LIST_BIND l arm8_encode) = 4 * LENGTH l`,
  CHEAT_TAC);;

(* [local] *)
let arm8_encode_not_nil = prove
 (`!i. ~(arm8_encode i = [])`,
  CHEAT_TAC);;

(* [local] *)
let arm8_encoding = prove
 (`!i. let l = arm8_enc i in (LENGTH l MOD 4 = 0) /\ ~(l = [])`,
  CHEAT_TAC);;

(* HOL4 arm8_targetProofScript.sml:309-311: a theorem that HOL4 states as
   the value of an ML expression: arm8_encoding *)

(* [local] *)
let arm8_target_ok = prove
 (`target_ok arm8_target`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
   arm8 encoder_correct
   ------------------------------------------------------------------------- *)

(* HOL4 arm8_targetProofScript.sml:330-331: the ML values that the
   definitions below antiquote *)

let arm8_encoder_correct = prove
 (`encoder_correct arm8_target`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
