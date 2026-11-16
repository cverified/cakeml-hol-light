(* ======================================================== *)
(*  ag32_targetProof: ported from HOL4's
    compiler/encoders/ag32/proofs/ag32_targetProofScript.sml
    A proof theory, with no definitions and 17 theorems.  Needed by
    ag32_configProof.ml and ag32_ffi_codeProof.ml.  *)
(* ======================================================== *)

(*
  Prove `encoder_correct` for ag32, i.e. Silver ISA
*)

needs "compiler/encoders/asm/asmProps.ml";;
needs "lib/bitstring.ml";;
needs "lib/set_sep.ml";;
needs "misc/misc.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ag32_targetProof"
  ["asm"; "asmProps"; "asmSem"];;
(* HOL4 ancestors outside the port: ag32_target *)

(* HOL4 ag32_targetProofScript.sml:10: ML code, not ported *)

(* some lemmas ---------------------------------------------------------- *)

(* [local] *)
let bytes_in_memory_thm = prove
 (`!w s state a b c d.
       target_state_rel ag32_target s state /\
       bytes_in_memory (asm_state_pc s) [a; b; c; d] (asm_state_mem s)
         (asm_state_mem_domain s) ==>
       alignment_aligned 2 (?_PC state) /\
       (?_MEM state (?_PC state) = a) /\
       (?_MEM state (?_PC state + (n2w 1)) = b) /\
       (?_MEM state (?_PC state + (n2w 2)) = c) /\
       (?_MEM state (?_PC state + (n2w 3)) = d) /\ ?_PC
       state + (n2w 3) IN asm_state_mem_domain s /\ ?_PC
       state + (n2w 2) IN asm_state_mem_domain s /\ ?_PC
       state + (n2w 1) IN asm_state_mem_domain s /\ ?_PC
       state IN asm_state_mem_domain s`,
  CHEAT_TAC);;

(* [local] *)
let bytes_in_memory_thm2 = prove
 (`!w s state a b c d.
       target_state_rel ag32_target s state /\
       bytes_in_memory (asm_state_pc s + w) [a; b; c; d] (asm_state_mem s)
         (asm_state_mem_domain s) ==>
       (?_MEM state (?_PC state + w) = a) /\
       (?_MEM state (?_PC state + w + (n2w 1)) = b) /\
       (?_MEM state (?_PC state + w + (n2w 2)) = c) /\
       (?_MEM state (?_PC state + w + (n2w 3)) = d) /\ ?_PC
       state + w + (n2w 3) IN asm_state_mem_domain s /\ ?_PC
       state + w + (n2w 2) IN asm_state_mem_domain s /\ ?_PC
       state + w + (n2w 1) IN asm_state_mem_domain s /\ ?_PC
       state + w IN asm_state_mem_domain s`,
  CHEAT_TAC);;

(* [local] *)
let add_carry_lem = prove
 (`!(w:word32). 4294967296 <= w2n w + 4294967295 <=> ~(w = (n2w 0))`,
  CHEAT_TAC);;

(* [local] *)
let add_carry_lem2 = prove
 (`!a b. n2w (w2n a + (w2n b + 1)) = a + b + (n2w 1)`,
  CHEAT_TAC);;

(* [local] *)
let shift_lem = prove
 (`!n. n < 32 ==> (w2n (sw2sw (n2w n:word6):word32) = n)`,
  CHEAT_TAC);;

(* [local] *)
let long_mul_lem = prove
 (`!(a:word32) (b:word32).
     n2w ((w2n a * w2n b) DIV 4294967296) =
     ((63 >< 32) (w2w a * (w2w b:word64)):word32)`,
  CHEAT_TAC);;

(* HOL4 ag32_targetProofScript.sml:85-87: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:89-94: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:96-101: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:103-105: ML code, not ported *)

(* [local] *)
let load_lem2 = prove
 (`!(c:word32). alignment_aligned 2 c ==> ((31 >< 2) c @@ ((n2w 0):word2) =
  c)`,
  CHEAT_TAC);;

(* HOL4 ag32_targetProofScript.sml:114-117: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:119-123: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:125-128: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:130-132: ML code, not ported *)

(* some rewrites ---------------------------------------------------------- *)

(* HOL4 ag32_targetProofScript.sml:136-143: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:145-147: ML code, not ported *)

(* HOL4 ag32_targetProofScript.sml:149-150: ML code, not ported *)

(* some custom tactics ---------------------------------------------------- *)

(* -------------------------------------------------------------------------
   ag32 target_ok
   ------------------------------------------------------------------------- *)

(* [local] *)
let length_ag32_encode = prove
 (`!i. (LENGTH (ag32_encode1 i) = 4) /\ (~(ag32_encode1 i = []))`,
  CHEAT_TAC);;

(* HOL4 ag32_targetProofScript.sml:164-173: a theorem that HOL4 states as
   the value of an ML expression: ag32_encoding *)

(* [local] *)
let ag32_target_ok = prove
 (`target_ok ag32_target`,
  CHEAT_TAC);;

(* [local] *)
let aligned_pc = prove
 (`!(a:word32). alignment_aligned 2 a ==> (((31 >< 2) a:word30) @@ ((n2w
  0):word2) = a)`,
  CHEAT_TAC);;

let concat_bytes = prove
 (`!(w:word32). (31 >< 24) w @@ (23 >< 16) w @@ (15 >< 8) w @@ (7 >< 0) w = w`,
  CHEAT_TAC);;

(* [local] *)
let funcT_thm = prove
 (`!func.
      num2funcT (w2n (v2w
          [BIT 3 (funcT2num func); BIT 2 (funcT2num func);
           BIT 1 (funcT2num func); BIT 0 (funcT2num func)]:word4)) = func`,
  CHEAT_TAC);;

(* [local] *)
let shiftT_thm = prove
 (`!shiftOp.
      num2shiftT (w2n ((1 >< 0) (v2w
          [BIT 3 (shiftT2num shiftOp); BIT 2 (shiftT2num shiftOp);
           BIT 1 (shiftT2num shiftOp); BIT 0 (shiftT2num shiftOp)]:word4)))
             =
      shiftOp`,
  CHEAT_TAC);;

(* HOL4 ag32_targetProofScript.sml:226: ML code, not ported *)

(* The encoder and decoder are well-behaved *)
let Decode_Encode = prove
 (`!i. Decode (Encode i) = i`,
  CHEAT_TAC);;

(* [local] *)
let ag32_run = prove
 (`!i ms.
      (?_MEM ms (?_PC ms) = (7 >< 0) (Encode i)) /\
      (?_MEM ms (?_PC ms + (n2w 1)) = (15 >< 8) (Encode i)) /\
      (?_MEM ms (?_PC ms + (n2w 2)) = (23 >< 16) (Encode i)) /\
      (?_MEM ms (?_PC ms + (n2w 3)) = (31 >< 24) (Encode i)) /\
      alignment_aligned 2 (?_PC ms) ==>
      (Next ms = Run i ms)`,
  CHEAT_TAC);;

(* HOL4 ag32_targetProofScript.sml:273-303: the ML values that the
   definitions below antiquote *)

(* HOL4 ag32_targetProofScript.sml:305-322: a proof *)

(* [local] *)
let bytes_in_memory_IMP_all_pcs_MEM = prove
 (`!env a xs m dm.
    bytes_in_memory a xs m dm /\
    (
     // (!(i:num) ms'. (∀a. a ∈ dm ⇒ (env i ms').MEM a = ms'.MEM a)) ==>
     !(i:num) ms'. fun2set (?_MEM (env i ms'),dm) = fun2set (?_MEM ms',dm))
       ==>
    (!i ms'. (!pc'. pc' IN all_pcs (LENGTH xs) a 0 ==> ?_MEM (env i ms')
      pc' = ?_MEM ms' pc'))`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
   ag32 encoder_correct
   ------------------------------------------------------------------------- *)

(* HOL4 ag32_targetProofScript.sml:377: ML code, not ported *)

let ag32_encoder_correct = prove
 (`encoder_correct ag32_target`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
