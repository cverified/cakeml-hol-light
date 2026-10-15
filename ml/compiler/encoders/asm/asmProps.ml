(* ======================================================== *)
(*  asmProps: ported from HOL4's
    compiler/encoders/asm/asmPropsScript.sml  *)
(* ======================================================== *)

(*
  Proofs of general properties of the asm language
*)

needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmSem.ml";;

(* -- semantics is deterministic -- *)

(* -- well-formedness of encoding -- *)

let offset_monotonic_def = cake_define
  `offset_monotonic enc c a1 a2 i1 i2 <=>
   asm_ok i1 c /\ asm_ok i2 c ==>
   ((n2w 0) <= a1 /\ (n2w 0) <= a2 /\ a1 <= a2 ==> LENGTH (enc i1) <=
     LENGTH (enc i2)) /\
   (a1 < (n2w 0) /\ a2 < (n2w 0) /\ a2 <= a1 ==> LENGTH (enc i1)
     <= LENGTH (enc i2))`;;

let enc_ok_def = cake_define
  `enc_ok (c:'a asm_config) <=>
     (2 EXP asm_config_code_alignment c = LENGTH (asm_config_encode c
       (asm_Inst asm_Skip))) /\
     (!w. (LENGTH (asm_config_encode c w) MOD 2 EXP
       asm_config_code_alignment c = 0) /\ ~(
           LENGTH (asm_config_encode c w) = 0)) /\
     (!w1 w2. offset_monotonic (asm_config_encode c) c w1 w2
       (asm_Jump w1) (asm_Jump w2)) /\
     (!cmp r ri w1 w2.
        offset_monotonic (asm_config_encode c) c w1 w2
           (asm_JumpCmp cmp r ri w1) (asm_JumpCmp cmp r ri w2)) /\
     (!w1 w2. offset_monotonic (asm_config_encode c) c w1 w2
       (asm_Call w1) (asm_Call w2)) /\
     (!w1 w2 r. offset_monotonic (asm_config_encode c) c w1 w2
       (asm_Loc r w1) (asm_Loc r w2))`;;

(* -- correctness property to be proved for each backend -- *)

let target_FIELDS = define_record "target"
  ["config","'a asm_config";
   "next","'b->'b";
   "get_pc","'b->'a word";
   "get_reg","'b->num->'a word";
   "get_fp_reg","'b->num->word64";
   "get_byte","'b->'a word->word8";
   "state_ok","'b->bool";
   "proj","('a word->bool)->'b->'c"];;
hol4_overload "next" "target_next";;
hol4_overload "next_fupd" "target_next_fupd";;

let target_state_rel_def = cake_define
  `target_state_rel t s ms <=> target_state_ok
   t ms /\ (target_get_pc t ms = asm_state_pc s) /\
   (!a. a IN asm_state_mem_domain s ==> (target_get_byte t ms a =
     asm_state_mem s a)) /\
   (!i. i < asm_config_reg_count (target_config t) /\ ~MEM i
     (asm_config_avoid_regs (target_config t)) ==>
        (target_get_reg t ms i = asm_state_regs s i)) /\
   (!i. i < asm_config_fp_reg_count (target_config t) ==>
     (target_get_fp_reg t ms i = asm_state_fp_regs s i))`;;

let target_ok_def = cake_define
  `target_ok t <=>
   enc_ok (target_config t) /\
   (!ms1 ms2 s.
     (target_proj t (asm_state_mem_domain s) ms1 = target_proj t
       (asm_state_mem_domain s) ms2) ==>
     (target_state_rel t s ms1 = target_state_rel t s ms2) /\
     (target_state_ok t ms1 = target_state_ok t ms2) /\
     (target_get_pc t ms1 = target_get_pc t ms2) /\
     (!a. a IN asm_state_mem_domain s ==> target_get_byte t ms1 a
       = target_get_byte t ms2 a))`;;

let interference_ok_def = cake_define
  `interference_ok env proj <=> (!(i:num ms). proj (env i ms) = proj
  ms)`;;
let all_pcs_def = cake_define
  `all_pcs n a k =
        match n with
          0 -> {}
        | n -> a INSERT all_pcs (n - (2 EXP k)) (a + n2w (2 EXP
          k)) k`;;

let asserts_def = cake_define_list
  [`asserts 0 next ms _1 Q <=> Q (next 0 ms)`;
   `asserts (SUC n) next ms P Q <=>
         (let ms' = next (SUC n) ms in P ms' /\ asserts n next
           ms' P Q)`];;

let asserts2_def = cake_define
  `(asserts2 n fi fc ms P =
    (if n = 0 then T else
      P ms (fc ms) /\
      asserts2 (n - 1) fi fc (fi n (fc ms)) P))`;;

let encoder_correct_def = cake_define
  `encoder_correct t <=>
     target_ok t /\
     (!s1 i s2 ms.
       asm_step (target_config t) s1 i s2 /\ target_state_rel t s1 ms
         ==>
       (?n. !env.
             interference_ok (env:num->'b->'b) (target_proj t
               (asm_state_mem_domain s1)) ==>
             (let pcs = all_pcs (LENGTH (asm_config_encode
               (target_config t) i)) (asm_state_pc s1) in
             asserts n (\k s. env (n - k) (target_next t s)) ms
               (\ms'. target_state_ok t ms' /\
                      (!pc. pc IN pcs 0 ==> target_get_byte t ms' pc
                        = target_get_byte t ms pc) /\ target_get_pc
                      t ms' IN pcs (asm_config_code_alignment
                        (target_config t)))
               (\ms'. target_state_rel t s2 ms') /\
             asserts2 (n + 1) (\k. env ((n + 1) - k)) (target_next t)
               ms
               (\ms1 ms2. !x. ~(x IN asm_state_mem_domain s1) ==>
                 target_get_byte t ms1 x = target_get_byte t ms2
                 x))))`;;

(* lemma for proofs *)

(* HOL4 ML code, not ported:
local
  fun genlist f 0 = []
    | genlist f n = genlist f (n-1) @ [f (n-1)]
  fun suc_num 0 = ``0:num``
    | suc_num n = mk_comb(``SUC``,suc_num (n-1))
  fun gen_rw n =
    ``asserts ^(suc_num n) next (s:'a) P Q``
    |> ONCE_REWRITE_CONV [asserts_def] |> SIMP_RULE std_ss []
in
*)

(* HOL4 ML code, not ported:
local
  fun gen_rw n =
    ``asserts2 ^(numSyntax.term_of_int n) fi fc (s:'a) P``
    |> ONCE_REWRITE_CONV [asserts2_def] |> SIMP_RULE std_ss []
in
*)
