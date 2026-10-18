(* ======================================================== *)
(*  asmProps: ported from HOL4's
    compiler/encoders/asm/asmPropsScript.sml
    A proof theory about asm.ml, with 9 definitions, 1 datatype and
    31 theorems.  Needed by lab_to_targetProof.ml, targetProps.ml
    and targetSem.ml.  *)
(* ======================================================== *)

(*
  Proofs of general properties of the asm language
*)

needs "compiler/encoders/asm/asm.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "misc/misc.ml";;

(* -- semantics is deterministic -- *)

let asm_deterministic = cake_theorem "asm_deterministic"
  (fun () ->
    `!c i s1 s2 s3. asm_step c s1 i s2 /\ asm_step c s1 i s3 ==> (s2 =
  s3)`)
  CHEAT_TAC;;

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
hol4_field_overload "next" "target_next";;
hol4_field_overload "next_fupd" "target_next_fupd";;

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
  `interference_ok env proj <=> (!(i:num) ms. proj (env i ms) = proj
  ms)`;;
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let all_pcs_def = cake_define_cheat CHEAT_TAC
  `all_pcs n a k =
        match n with
          0 -> {}
        | n -> a INSERT all_pcs (n - (2 EXP k)) (a + n2w (2 EXP
          k)) k`;;

let all_pcs_thm = cake_theorem "all_pcs_thm"
  (fun () ->
    `all_pcs n a k = {a + n2w (i * (2 EXP k)) | i | i * (2 EXP k) < n}`)
  CHEAT_TAC;;

let asserts_def = cake_define_list
  [`asserts 0 next' ms _1 Q <=> Q (next' 0 ms)`;
   `asserts (SUC n) next' ms P Q <=>
         (let ms' = next' (SUC n) ms in P ms' /\ asserts n
           next' ms' P Q)`];;

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
                      (!pc'. pc' IN pcs 0 ==> target_get_byte t ms'
                        pc' = target_get_byte t ms pc') /\ target_get_pc
                      t ms' IN pcs (asm_config_code_alignment
                        (target_config t)))
               (\ms'. target_state_rel t s2 ms') /\
             asserts2 (n + 1) (\k. env ((n + 1) - k)) (target_next t)
               ms
               (\ms1 ms2. !x. ~(x IN asm_state_mem_domain s1) ==>
                 target_get_byte t ms1 x = target_get_byte t ms2
                 x))))`;;

(* lemma for proofs *)

let bytes_in_memory_all_pcs = cake_theorem "bytes_in_memory_all_pcs"
  (fun () ->
    `!xs pc'. bytes_in_memory pc' xs m d ==> all_pcs (LENGTH xs) pc' k
  SUBSET d`)
  CHEAT_TAC;;

let read_bytearray_IMP_bytes_in_memory =
  cake_theorem "read_bytearray_IMP_bytes_in_memory"
  (fun () ->
    `!p n m ba m' md.
     (n = LENGTH ba) /\
     (!k. k IN all_words p n ==> k IN md /\ (m k = SOME (m' k))) /\
     (read_bytearray (p:'a word) n m = SOME ba) ==>
     bytes_in_memory p ba m' md`)
  CHEAT_TAC;;

let sym_target_state_rel = cake_theorem "sym_target_state_rel"
  (fun () ->
    `!t s ms.
       target_state_rel t s ms <=> target_state_ok
       t ms /\ (asm_state_pc s = target_get_pc t ms) /\
       (!a. a IN asm_state_mem_domain s ==> (asm_state_mem s a =
         target_get_byte t ms a)) /\
       (!i. i < asm_config_reg_count (target_config t) /\ ~MEM i
         (asm_config_avoid_regs (target_config t)) ==>
            (asm_state_regs s i = target_get_reg t ms i)) /\
       (!i. i < asm_config_fp_reg_count (target_config t) ==>
         (asm_state_fp_regs s i = target_get_fp_reg t ms i))`)
  CHEAT_TAC;;

(* HOL4 asmPropsScript.sml:197-205: ML code, not ported *)
(* HOL4 asmPropsScript.sml:206-207: a theorem that HOL4 states as the
   value of an ML expression *)

let asserts_IMP_FOLDR_COUNT_LIST =
  cake_theorem "asserts_IMP_FOLDR_COUNT_LIST"
  (fun () ->
    `!n next' ms P Q. asserts n next' ms P Q ==>
        Q (ITLIST next' (COUNT_LIST n) (next' n ms))`)
  CHEAT_TAC;;

let asserts_IMP_FOLDR_COUNT_LIST_LESS =
  cake_theorem "asserts_IMP_FOLDR_COUNT_LIST_LESS"
  (fun () ->
    `!k n next' ms P Q. asserts n next' ms P Q /\ k < n ==>
        P (ITLIST next' (REVERSE (GENLIST ((-) n) (SUC k))) ms)`)
  CHEAT_TAC;;

let asserts_WEAKEN = cake_theorem "asserts_WEAKEN"
  (fun () ->
    `!n next' s P Q.
        (!k. k <= n ==>
          (next' k = next' k) /\
          (P (ITLIST next' (REVERSE (GENLIST ((-) n) (SUC k))) s)
            ==>
           P' (ITLIST next' (REVERSE (GENLIST ((-) n) (SUC k)))
             s))) ==>
        asserts n next' s P Q ==>
        asserts n next' s P' Q`)
  CHEAT_TAC;;

(* HOL4 asmPropsScript.sml:269-273: ML code, not ported *)
(* HOL4 asmPropsScript.sml:274-275: a theorem that HOL4 states as the
   value of an ML expression *)

let asserts2_change_interfer = cake_theorem "asserts2_change_interfer"
  (fun () ->
    `asserts2 n fi fc ms P /\
     (!k. k <= n ==> fi k = fi2 k) ==>
     asserts2 n fi2 fc ms P`)
  CHEAT_TAC;;

let asserts2_first = cake_theorem "asserts2_first"
  (fun () ->
    `1 <= n /\ asserts2 n fi fc ms P ==> P ms (fc ms)`)
  CHEAT_TAC;;

let asserts2_every = cake_theorem "asserts2_every"
  (fun () ->
    `!n ms j.
     asserts2 n (\k. f) g ms P /\ j < n ==>
     P (FUNPOW (f o g) j ms) (g (FUNPOW (f o g) j ms))`)
  CHEAT_TAC;;

let upd_pc_simps = cake_theorem "upd_pc_simps[simp]"
  (fun () ->
    `(asm_state_align (asmSem_upd_pc x s) = asm_state_align s) /\
     (asm_state_mem_domain (asmSem_upd_pc x s) =
       asm_state_mem_domain s) /\
     (asm_state_failed (asmSem_upd_pc x s) = asm_state_failed s) /\
     (asm_state_be (asmSem_upd_pc x s) = asm_state_be s) /\
     (asm_state_mem (asmSem_upd_pc x s) = asm_state_mem s) /\
     (asm_state_regs (asmSem_upd_pc x s) = asm_state_regs s) /\
     (asm_state_fp_regs (asmSem_upd_pc x s) = asm_state_fp_regs s)
       /\
     (asm_state_lr (asmSem_upd_pc x s) = asm_state_lr s) /\
     (asm_state_pc (asmSem_upd_pc x s) = x)`)
  CHEAT_TAC;;

let asm_failed_ignore_new_pc = cake_theorem "asm_failed_ignore_new_pc"
  (fun () ->
    `!i v w s. asm_state_failed (asmSem_asm i w s) <=>
  asm_state_failed (asmSem_asm i v s)`)
  CHEAT_TAC;;

let asm_mem_ignore_new_pc = cake_theorem "asm_mem_ignore_new_pc"
  (fun () ->
    `!i v w s. asm_state_mem (asmSem_asm i w s) = asm_state_mem
  (asmSem_asm i v s)`)
  CHEAT_TAC;;

let SND_read_mem_word_consts =
  cake_theorem "SND_read_mem_word_consts[local]"
  (fun () ->
    `!n a s. (asm_state_be (SND (read_mem_word a n s)) = asm_state_be s)
  /\
               (asm_state_lr (SND (read_mem_word a n s)) =
                 asm_state_lr s) /\
               (asm_state_align (SND (read_mem_word a n s)) =
                 asm_state_align s) /\
               (asm_state_mem_domain (SND (read_mem_word a n s))
                 = asm_state_mem_domain s)`)
  CHEAT_TAC;;

let write_mem_word_consts = cake_theorem "write_mem_word_consts[local]"
  (fun () ->
    `!n a w s. (asm_state_be (write_mem_word a n w s) = asm_state_be s)
  /\
                 (asm_state_lr (write_mem_word a n w s) =
                   asm_state_lr s) /\
                 (asm_state_align (write_mem_word a n w s) =
                   asm_state_align s) /\
                 (asm_state_mem_domain (write_mem_word a n w s) =
                   asm_state_mem_domain s)`)
  CHEAT_TAC;;

let binop_upd_consts = cake_theorem "binop_upd_consts[simp]"
  (fun () ->
    `(asm_state_mem_domain (asmSem_binop_upd a b c d x) =
  asm_state_mem_domain x) /\
     (asm_state_align (asmSem_binop_upd a b c d x) =
       asm_state_align x) /\
     (asm_state_failed (asmSem_binop_upd a b c d x) =
       asm_state_failed x) /\
     (asm_state_mem (asmSem_binop_upd a b c d x) = asm_state_mem x)
       /\
     (asm_state_lr (asmSem_binop_upd a b c d x) = asm_state_lr x)
       /\
     (asm_state_be (asmSem_binop_upd a b c d x) = asm_state_be x)`)
  CHEAT_TAC;;

let arith_upd_consts = cake_theorem "arith_upd_consts[simp]"
  (fun () ->
    `(asm_state_mem_domain (asmSem_arith_upd a x) = asm_state_mem_domain
  x) /\
     (asm_state_align (asmSem_arith_upd a x) = asm_state_align x)
       /\
     (asm_state_mem (asmSem_arith_upd a x) = asm_state_mem x) /\
     (asm_state_lr (asmSem_arith_upd a x) = asm_state_lr x) /\
     (asm_state_be (asmSem_arith_upd a x) = asm_state_be x)`)
  CHEAT_TAC;;

let fp_upd_consts = cake_theorem "fp_upd_consts[simp]"
  (fun () ->
    `(asm_state_mem_domain (asmSem_fp_upd a x) = asm_state_mem_domain x)
  /\
     (asm_state_align (asmSem_fp_upd a x) = asm_state_align x) /\
     (asm_state_mem (asmSem_fp_upd a x) = asm_state_mem x) /\
     (asm_state_lr (asmSem_fp_upd a x) = asm_state_lr x) /\
     (asm_state_be (asmSem_fp_upd a x) = asm_state_be x)`)
  CHEAT_TAC;;

let asm_consts = cake_theorem "asm_consts[simp]"
  (fun () ->
    `!i w s. (asm_state_be (asmSem_asm i w s) = asm_state_be s) /\
              (asm_state_lr (asmSem_asm i w s) = asm_state_lr s) /\
              (asm_state_align (asmSem_asm i w s) = asm_state_align
                s) /\
              (asm_state_mem_domain (asmSem_asm i w s) =
                asm_state_mem_domain s)`)
  CHEAT_TAC;;

let RTC_asm_step_consts = cake_theorem "RTC_asm_step_consts"
  (fun () ->
    `RTC (\s1 s2. ?i. asm_step c s1 i s2) s1 s2 ==>
  (asm_state_mem_domain s2 = asm_state_mem_domain s1) /\
      (asm_state_lr s2 = asm_state_lr s1) /\
      (asm_state_align s2 = asm_state_align s1) /\
      (asm_state_be s2 = asm_state_be s1)`)
  CHEAT_TAC;;

let read_mem_word_IMP_mem_eq = cake_theorem "read_mem_word_IMP_mem_eq"
  (fun () ->
    `!a k s w s'. (read_mem_word a k s = (w,s')) ==> (asm_state_mem s'
  = asm_state_mem s)`)
  CHEAT_TAC;;

let write_mem_word_mem_domain = cake_theorem "write_mem_word_mem_domain"
  (fun () ->
    `!k b a s. asm_state_mem_domain (write_mem_word b k a s) =
  asm_state_mem_domain s`)
  CHEAT_TAC;;

let write_mem_word_mem_eq = cake_theorem "write_mem_word_mem_eq"
  (fun () ->
    `!k b a s x.
        ~asm_state_failed (write_mem_word b k a s) /\ ~(x IN
          asm_state_mem_domain s) ==>
        (asm_state_mem (write_mem_word b k a s) x = asm_state_mem
          s x)`)
  CHEAT_TAC;;

let mem_op_outside_mem_domain = cake_theorem "mem_op_outside_mem_domain"
  (fun () ->
    `!m n a s x. ~(x IN asm_state_mem_domain s) /\ ~asm_state_failed
  (asmSem_mem_op m n a s) ==>
                 (asm_state_mem (asmSem_mem_op m n a s) x =
                   asm_state_mem s x)`)
  CHEAT_TAC;;

let inst_outside_mem_domain = cake_theorem "inst_outside_mem_domain"
  (fun () ->
    `!i. ~(x IN asm_state_mem_domain s) /\ ~asm_state_failed
  (asmSem_inst i s) ==> (asm_state_mem (asmSem_inst i s) x =
  asm_state_mem s x)`)
  CHEAT_TAC;;

let asm_outside_mem_domain = cake_theorem "asm_outside_mem_domain"
  (fun () ->
    `!i p s x. ~(x IN asm_state_mem_domain s) /\ ~asm_state_failed
  (asmSem_asm i p s) ==> (asm_state_mem (asmSem_asm i p s) x =
  asm_state_mem s x)`)
  CHEAT_TAC;;

let asm_step_outside_mem_domain =
  cake_theorem "asm_step_outside_mem_domain"
  (fun () ->
    `asm_step c s1 i s2 ==>
     (!x. ~(x IN asm_state_mem_domain s1) ==> (asm_state_mem s2 x
       = asm_state_mem s1 x))`)
  CHEAT_TAC;;

let RTC_asm_step_outside_mem_domain =
  cake_theorem "RTC_asm_step_outside_mem_domain"
  (fun () ->
    `!s1 s2.
     RTC (\s1 s2. ?i. asm_step c s1 i s2) s1 s2 ==> (!a. ~(a IN
       asm_state_mem_domain s1) ==> (asm_state_mem s2 a =
       asm_state_mem s1 a))`)
  CHEAT_TAC;;
