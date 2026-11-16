(* ======================================================== *)
(*  x64_targetProof: ported from HOL4's
    compiler/encoders/x64/proofs/x64_targetProofScript.sml
    A proof theory, with no definitions and 33 theorems.  Needed by
    x64_configProof.ml.  *)
(* ======================================================== *)

(*
  Prove `encoder_correct` for x64
*)

needs "compiler/encoders/asm/asmProps.ml";;
needs "lib/bitstring.ml";;
needs "lib/integer_word.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "x64_targetProof"
  ["asm"; "asmProps"; "asmSem"];;
(* HOL4 ancestors outside the port: x64_target *)

(* HOL4 x64_targetProofScript.sml:14: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:16: the overload reg, which the port
   expands *)

(* some lemmas ---------------------------------------------------------- *)

(* HOL4 x64_targetProofScript.sml:20-21: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:23-26: ML code, not ported *)

(* [local] *)
let const_lem2 = prove
 (`!(c:word64).
        ([(7 >< 0) c; (15 >< 8) c; (23 >< 16) c; (31 >< 24) c]:word8 list) =
        [(7 >< 0) (w2w c:word32); (15 >< 8) (w2w c:word32);
         (23 >< 16) (w2w c:word32); (31 >< 24) (w2w c:word32)]`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:37-46: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:48-52: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:54-59: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:61-65: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:67-72: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:74-79: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:81-86: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:88-93: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:95-100: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:102: the ML values that the definitions
   below antiquote *)

(* HOL4 x64_targetProofScript.sml:104-106: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:108-112: ML code, not ported *)

(* [local] *)
let binop_lem1 = prove
 (`(~((if b then [x] else []) = [])) = b`,
  CHEAT_TAC);;

(* [local] *)
let binop_lem5 = prove
 (`!(c:word64). ([(7 >< 0) c]:word8 list) = [I (w2w c:word8)]`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:126-130: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:132-136: ML code, not ported *)

(* [local] *)
let binop_lem9b = prove
 (`!n. n < 64 ==>
         ((n2w 0xFFFFFFFFFFFFFF80):word64) <= n2w n /\ n2w n <= ((n2w
           0x7F):word64)`,
  CHEAT_TAC);;

(* [local] *)
let binop_lem9 = prove
 (`!(i:word64) n.
        n < 64 /\ Abbrev (i = n2w n) ==>
        (n2w 0xFFFFFFFFFFFFFF80) <= i /\ i <= (n2w 0x7F) /\ i <+ (n2w 64) /\
        (w2n (w2w i:word6) = n)`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:162-166: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:168-174: ML code, not ported *)

(* [local] *)
let mem_lem1 = prove
 (`!a n s state.
        target_state_rel x64_target s state /\ n < 16 /\ ~(n = 4) /\ ~(n =
          5) /\ asm_state_regs
        s n + a IN asm_state_mem_domain s ==>
        (?_MEM state (?_REG state (num2Zreg n) + a) = asm_state_mem s
          (asm_state_regs s n + a))`,
  CHEAT_TAC);;

(* [local] *)
let mem_lem2 = prove
 (`!a n s state.
     target_state_rel x64_target s state /\ n < 16 /\ ~(n = 4) /\ ~(n = 5)
       /\ asm_state_regs
     s n + a IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 1) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 2) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 3) IN asm_state_mem_domain s ==>
     (read_mem32 (?_MEM state) (?_REG state (num2Zreg n) + a) =
       asm_state_mem
      s (asm_state_regs s n + a + (n2w 3)) @@ asm_state_mem s
        (asm_state_regs s n + a + (n2w 2)) @@ asm_state_mem
      s (asm_state_regs s n + a + (n2w 1)) @@ asm_state_mem s
        (asm_state_regs s n + a))`,
  CHEAT_TAC);;

(* [local] *)
let mem_lem2b = prove
 (`!a n s state.
     target_state_rel x64_target s state /\ n < 16 /\ ~(n = 4) /\ ~(n = 5)
       /\ asm_state_regs
     s n + a IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 1) IN asm_state_mem_domain s ==>
     (read_mem16 (?_MEM state) (?_REG state (num2Zreg n) + a) =
       asm_state_mem
      s (asm_state_regs s n + a + (n2w 1)) @@ asm_state_mem s
        (asm_state_regs s n + a))`,
  CHEAT_TAC);;

(* [local] *)
let mem_lem3 = prove
 (`!a n s state.
     target_state_rel x64_target s state /\ n < 16 /\ ~(n = 4) /\ ~(n = 5)
       /\ asm_state_regs
     s n + a IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 1) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 2) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 3) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 4) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 5) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 6) IN asm_state_mem_domain s /\ asm_state_regs
     s n + a + (n2w 7) IN asm_state_mem_domain s ==>
     (read_mem64 (?_MEM state) (?_REG state (num2Zreg n) + a) =
       asm_state_mem
      s (asm_state_regs s n + a + (n2w 7)) @@ asm_state_mem s
        (asm_state_regs s n + a + (n2w 6)) @@ asm_state_mem
      s (asm_state_regs s n + a + (n2w 5)) @@ asm_state_mem s
        (asm_state_regs s n + a + (n2w 4)) @@ asm_state_mem
      s (asm_state_regs s n + a + (n2w 3)) @@ asm_state_mem s
        (asm_state_regs s n + a + (n2w 2)) @@ asm_state_mem
      s (asm_state_regs s n + a + (n2w 1)) @@ asm_state_mem s
        (asm_state_regs s n + a))`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:233-235: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:237-241: ML code, not ported *)

(* [local] *)
let mem_lem6 = prove
 (`!r. ~((2 >< 0) r = ((n2w 4):word3)) /\ ~((2 >< 0) r = ((n2w 5):word3)) ==>
         (r = RegNot4or5 r)`,
  CHEAT_TAC);;

(* [local] *)
let mem_lem7 = prove
 (`!r. ~((2 >< 0) r = ((n2w 4):word3)) ==> (r = RegNot4 r)`,
  CHEAT_TAC);;

(* [local] *)
let mem_lem8 = prove
 (`!(r:word4) n.
        ~(3 < n) /\ Abbrev (r = n2w n) ==> ~(num2Zreg (w2n r) = RSP)
          /\ ~(num2Zreg (w2n r) = RBP) /\ ~(num2Zreg (w2n r) = RSI)
          /\ ~(num2Zreg (w2n r) = RDI)`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:270-292: code that the source has in a
   comment *)

(* HOL4 x64_targetProofScript.sml:294-296: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:298-300: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:302-304: ML code, not ported *)

(* [local] *)
let mem_lem14 = prove
 (`!w (m:word64->word8).
    ((w + (n2w 7)) =+ b7)
      (((w + (n2w 6)) =+ b6)
         (((w + (n2w 5)) =+ b5)
            (((w + (n2w 4)) =+ b4)
               (((w + (n2w 3)) =+ b3)
                  (((w + (n2w 2)) =+ b2)
                     (((w + (n2w 1)) =+ b1)
                        ((w =+ b0) m))))))) =
    (w =+ b0)
      (((w + (n2w 1)) =+ b1)
         (((w + (n2w 2)) =+ b2)
            (((w + (n2w 3)) =+ b3)
               (((w + (n2w 4)) =+ b4)
                  (((w + (n2w 5)) =+ b5)
                     (((w + (n2w 6)) =+ b6)
                        (((w + (n2w 7)) =+ b7) m)))))))`,
  CHEAT_TAC);;

(* [local] *)
let mem_lem15 = prove
 (`!w (v:word64) (m:word64->word8).
    ((w + (n2w 3)) =+ b3) (((w + (n2w 2)) =+ b2) (((w + (n2w 1)) =+ b1) ((w
      =+ b0) m))) =
    (w =+ b0) (((w + (n2w 1)) =+ b1) (((w + (n2w 2)) =+ b2) (((w + (n2w
      3)) =+ b3) m)))`,
  CHEAT_TAC);;

(* [local] *)
let mem_lem15b = prove
 (`!w (v:word64) (m:word64->word8).
   ((w + (n2w 1)) =+ b1) ((w =+ b0) m) = (w =+ b0) (((w + (n2w 1)) =+ b1)
     m)`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:351-354: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:356-360: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:362-370: ML code, not ported *)

(* [local] *)
let cmp_lem4 = prove
 (`!(w:word64) a b. CONS ((7 >< 0) w) (CONS a (b:word8 list)) = CONS (I (w2w
  w:word8)) (CONS a b)`,
  CHEAT_TAC);;

(* [local] *)
let cmp_lem5 = prove
 (`!(c:word64).
        (n2w 0xFFFFFFFFFFFFFF80) <= c /\ c <= (n2w 0x7F) ==>
        (((if (7 >< 7) c = ((n2w 1):word8) then (n2w 0xFFFFFFFFFFFFFF00)
          else (n2w 0)) ||
          ((7 >< 0) c)) = c)`,
  CHEAT_TAC);;

(* [local] *)
let cmp_lem6 = prove
 (`!(c:word64).
        (n2w 0xFFFFFFFF80000000) <= c /\ c <= (n2w 0x7FFFFFFF) ==>
        (((if (31 >< 31) c = ((n2w 1):word32) then (n2w 0xFFFFFFFF00000000)
          else (n2w 0)) ||
          (31 >< 0) c) = c)`,
  CHEAT_TAC);;

(* [local] *)
let cmp_lem7 = prove
 (`!rm. is_rax rm = (Zr RAX = rm)`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:407-411: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:413-417: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:419-423: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:425-429: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:431-439: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:441-447: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:449-457: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:459-461: the ML values that the
   definitions below antiquote *)

(* HOL4 x64_targetProofScript.sml:463: the ML values that the definitions
   below antiquote *)

(* HOL4 x64_targetProofScript.sml:465-466: the ML values that the
   definitions below antiquote *)

(* [local] *)
let is_rax = prove
 (`!n. n < 16 ==> ((RAX = num2Zreg n) = (n = 0))`,
  CHEAT_TAC);;

(* [local] *)
let is_rdx = prove
 (`!n. n < 16 ==> ((RDX = num2Zreg n) = (n = 2))`,
  CHEAT_TAC);;

(* [local] *)
let xmm_reg = prove
 (`(!n. n < 8 ==> ((3 >< 3) (n2w n:word4) = ((n2w 0):word1))) /\
    (!n. n < 8 ==> ((3 >< 3) (w2w (n2w n:word3):word4) = ((n2w 0):word1)))
      /\
    (!n. n < 8 ==> ~(word_bit 3 (n2w n:word4))) /\
    (!n. n < 16 /\ ~(n < 8) ==> ((3 >< 3) (n2w n:word4) = ((n2w 1):word1)))
      /\
    (!n. n < 16 /\ ~(n < 8) ==> word_bit 3 (n2w n:word4))`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:495-500: ML code, not ported *)

(* [local] *)
let xmm_reg2 = prove
 (`(!n (r:word4).
       n < 8 /\ Abbrev (r = n2w n) ==>
       (RexReg (F,v2w [FAPPLY r 2; FAPPLY r 1; FAPPLY r 0]) = num2Zreg n))
         /\
    (!n (r:word4).
       ~(n < 8) /\ n < 16 /\ Abbrev (r = n2w n) ==>
       (RexReg (T,v2w [FAPPLY r 2; FAPPLY r 1; FAPPLY r 0]) = num2Zreg n))`,
  CHEAT_TAC);;

(* [local] *)
let xmm_reg3 = prove
 (`!n. n < 8 ==> (w2w (n2w n:word3) = (n2w n:word4))`,
  CHEAT_TAC);;

(* HOL4 x64_targetProofScript.sml:522-530: ML code, not ported *)

(* [local] *)
let fp_abs = prove
 (`!w. fp64_abs w = ((n2w 0x7FFFFFFFFFFFFFFF) && w)`,
  CHEAT_TAC);;

(* [local] *)
let fp_neg = prove
 (`!w. fp64_negate w = ((n2w 0x8000000000000000) ?? w)`,
  CHEAT_TAC);;

(* [local] *)
let fp_compare = prove
 (`(!a b. fp64_equal a b = (fp64_compare a b = binary_ieee_EQ)) /\
    (!a b. fp64_lessThan a b = (fp64_compare a b = binary_ieee_LT)) /\
    (!a b. fp64_lessEqual a b =
           ((fp64_compare a b = binary_ieee_LT) \/ (fp64_compare a b =
             binary_ieee_EQ)))`,
  CHEAT_TAC);;

(* [local] *)
let fp_to_int_lem = prove
 (`!i (w:word32).
       (w2i w = i) ==> --2147483648 <= i /\ i <= 2147483647`,
  CHEAT_TAC);;

(* some rewrites ---------------------------------------------------------- *)

(* HOL4 x64_targetProofScript.sml:585-598: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:600-602: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:604-609: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:611-612: ML code, not ported *)

(* some custom tactics ---------------------------------------------------- *)

(* HOL4 x64_targetProofScript.sml:616: ML code, not ported *)

(* HOL4 x64_targetProofScript.sml:618-726: the ML values that the
   definitions below antiquote *)

(* HOL4 x64_targetProofScript.sml:800-894: the ML values that the
   definitions below antiquote *)

(* HOL4 x64_targetProofScript.sml:896-904: a proof *)

(* -------------------------------------------------------------------------
   x64 target_ok
   ------------------------------------------------------------------------- *)

(* [local] *)
let x64_encoding = prove
 (`!i. ~(x64_enc i = [])`,
  CHEAT_TAC);;

(* [local] *)
let x64_cmp_neq_p = prove
 (`!cmp. ~(x64_cmp cmp = Z_P)`,
  CHEAT_TAC);;

(* [local] *)
let x64_target_ok = prove
 (`target_ok x64_target`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
   x64 encoder_correct
   ------------------------------------------------------------------------- *)

(* HOL4 x64_targetProofScript.sml:949: ML code, not ported *)

let word_extract_6 = prove
 (`w <+ (n2w 64) ==>
   (((5 >< 0) (w:word64)):word6) = (w2w w)`,
  CHEAT_TAC);;

let x64_encoder_correct = prove
 (`encoder_correct x64_target`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
