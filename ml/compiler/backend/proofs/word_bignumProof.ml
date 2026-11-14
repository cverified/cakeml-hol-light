(* ======================================================== *)
(*  word_bignumProof: ported from HOL4's
    compiler/backend/proofs/word_bignumProofScript.sml
    A proof theory about word_bignum.ml, with 25 definitions, 1
    datatype and 74 theorems.  Needed by 4 files of the port.  *)
(* ======================================================== *)

(*
  Correctness proof for word_bignum
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/byte.ml";;
needs "lib/mc_multiword.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "lib/tailrec.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "word_bignumProof"
  ["ast"; "backend_common"; "mllist"; "wordLang"; "wordProps";
   "wordSem"; "word_bignum"];;

let _ = do_list hide_constant ["shift"];;

(* HOL4 word_bignumProofScript.sml:11-12: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:16: ML code, not ported *)


(* semantics of the little language *)

let word_bignumProof_state_FIELDS =
  define_record "word_bignumProof_state"
  ["regs","(num,'a word)fmap";
   "arrays","address->('a word) list";
   "clock","num"];;

let _ = size_thms "wordLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let eval_exp_def,eval_exp_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_exp_size (\x. 0) x1)`
  [`eval_exp s (wordLang_Const w) = w /\
   eval_exp s (wordLang_Var v) = FAPPLY (word_bignumProof_state_regs
     s) v /\
   eval_exp s (wordLang_Op asm_Add [x1; x2]) = eval_exp s x1 +
     eval_exp s x2 /\
   eval_exp s (wordLang_Op asm_Sub [x1; x2]) = eval_exp s x1 -
     eval_exp s x2 /\
   eval_exp s (wordLang_Op asm_And [x1; x2]) = word_and (eval_exp s
     x1) (eval_exp s x2) /\
   eval_exp s (wordLang_Op asm_Or [x1; x2]) = word_or (eval_exp s
     x1) (eval_exp s x2) /\
   eval_exp s (wordLang_Op asm_Xor [x1; x2]) = word_xor (eval_exp s
     x1) (eval_exp s x2) /\
   eval_exp s (wordLang_Shift Lsl x1 x2) = eval_exp s x1 << (w2n
     (eval_exp s x2)) /\
   eval_exp s (wordLang_Shift Asr x1 x2) = eval_exp s x1 >> (w2n
     (eval_exp s x2)) /\
   eval_exp s (wordLang_Shift Lsr x1 x2) = eval_exp s x1 >>> (w2n
     (eval_exp s x2)) /\
   eval_exp s (wordLang_Shift Ror x1 x2) = word_ror (eval_exp s
     x1) (w2n (eval_exp s x2))`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let eval_exp_pre_def,eval_exp_pre_ind = define_wf
  `MEASURE (\(x0,x1). wordLang_exp_size (\x. 0) x1)`
  [`eval_exp_pre s x2 =
        match x2 with
          wordLang_Const w -> T
        | (wordLang_Var v) -> v IN FDOM (word_bignumProof_state_regs
          s)
        | (wordLang_Op _1 [x; y]) -> eval_exp_pre s x /\
          eval_exp_pre s y
        | (wordLang_Shift sh x1 x2) ->
        eval_exp_pre s x1 /\ eval_exp_pre s x2 /\ (w2n (eval_exp s
          x2) < 32)
        | _2 -> F`];;

let eval_ri_pre_def = define_cases
  [`eval_ri_pre (s:'a word_bignumProof_state) (Reg r) <=>
    eval_exp_pre (s:'a word_bignumProof_state) ((wordLang_Var r):'a
    wordLang_exp)`;
   `eval_ri_pre (s:'a word_bignumProof_state) (Imm (w:'a word)) <=>
    T`];;

let eval_ri_def = define_cases
  [`eval_ri (s:'a word_bignumProof_state) (Reg r) =
      eval_exp s ((Var r):'a wordLang_exp)`;
   `eval_ri (s:'a word_bignumProof_state) (Imm (w:'a word)) = w`];;

let word_bignumProof_dec_clock_def = new_definition
  `word_bignumProof_dec_clock s = word_bignumProof_state_clock_fupd
  (K (word_bignumProof_state_clock s - 1)) s`;;

let reg_write_def = define_cases
  [`reg_write v NONE (s:'a word_bignumProof_state) =
    word_bignumProof_state_regs_fupd (K (word_bignumProof_state_regs
    s \\ v)) s`;
   `reg_write n (SOME v) (s:'a word_bignumProof_state) =
    word_bignumProof_state_regs_fupd (K
    (word_bignumProof_state_regs s |+ (n,v))) s`];;

let delete_vars_def,delete_vars_ind = define_rec
  [`delete_vars [] s = s`;
   `delete_vars (CONS v vs) s = reg_write v NONE (delete_vars vs s)`];;

let array_write_def = new_definition
  `array_write n v s = word_bignumProof_state_arrays_fupd (K ((n =+
  v) (word_bignumProof_state_arrays s))) s`;;

let clock_write_def = new_definition
  `clock_write l s = word_bignumProof_state_clock_fupd (K l) s`;;

let copy_vars_def,copy_vars_ind = define_rec
  [`word_bignumProof_copy_vars [] s t = SOME t`;
   `word_bignumProof_copy_vars (CONS n ns) s t =
         (match FLOOKUP s n with NONE -> NONE | SOME x ->
             word_bignumProof_copy_vars ns s (reg_write n (SOME x)
             t))`];;

let eval = cake_inductive
  `(!r s. word_bignumProof_Eval r s word_bignum_Skip (INR (s:'a
  word_bignumProof_state))) /\
   (!r s. word_bignumProof_Eval r s wordSem_Continue (INL s)) /\
   (!r vs s. word_bignumProof_Eval r s (word_bignum_Delete vs) (INR
     (delete_vars vs (s:'a word_bignumProof_state)))) /\
   (!r s x n.
      eval_exp_pre s x ==>
      word_bignumProof_Eval r s (word_bignum_Assign n x) (INR
        (reg_write n (SOME (eval_exp s x)) s))) /\
   (!r s1 s2 s3 p1 p2.
      word_bignumProof_Eval r s1 p1 (INR s2) /\ word_bignumProof_Eval
        r s2 p2 s3 ==>
      word_bignumProof_Eval r s1 (word_bignum_Seq p1 p2) s3) /\
   (!rec s1 c r ri p1 p2 s2.
      r IN FDOM (word_bignumProof_state_regs s1) /\ eval_ri_pre s1 ri
        /\
      word_bignumProof_Eval rec s1 (if wordSem_word_cmp c (eval_exp
        s1 (wordLang_Var r)) (eval_ri s1 ri) then p1 else p2) s2 ==>
      word_bignumProof_Eval rec s1 (word_bignum_If c r ri p1 p2) s2)
        /\
   (!rec s r i a w.
      (FLOOKUP (word_bignumProof_state_regs s) i = SOME w) /\
      w2n w < LENGTH (word_bignumProof_state_arrays s a) ==>
      word_bignumProof_Eval rec s (word_bignum_Load r i a) (INR
        (reg_write r (SOME (EL (w2n w) (word_bignumProof_state_arrays s
        a))) s))) /\
   (!rec s r i w wr.
      (FLOOKUP (word_bignumProof_state_regs s) i = SOME w) /\
        (FLOOKUP (word_bignumProof_state_regs s) r = SOME wr) /\
      w2n w < LENGTH (word_bignumProof_state_arrays s Out) ==>
      word_bignumProof_Eval rec s (word_bignum_Store r i) (INR
        (array_write Out (LUPDATE wr (w2n w)
        (word_bignumProof_state_arrays s Out)) s))) /\
   (!r s.
      word_bignumProof_Eval r s word_bignum_Swap (INR (array_write
        In1 (word_bignumProof_state_arrays s In2)
                       (array_write In2
                         (word_bignumProof_state_arrays s In1) s)))) /\
   (!r s r1 r2.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s n4
        /\ eval_ri_pre s n5 /\
      (~(eval_ri s n5 = (n2w 0)) ==> eval_ri s n5 = (n2w 1)) /\ ~(n1
        = n2) /\
      (single_add_word (FAPPLY (word_bignumProof_state_regs s) n3)
        (eval_ri s n4) (eval_ri s n5) = (r1,r2)) ==>
      word_bignumProof_Eval r s (asm_Add n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r s n1 n2 n3 n4 n5 r1 r2.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s n4
        /\ eval_ri_pre s n5 /\
      (~(eval_ri s n5 = (n2w 0)) ==> eval_ri s n5 = (n2w 1)) /\ ~(n1
        = n2) /\
      (single_sub_word (FAPPLY (word_bignumProof_state_regs s) n3)
        (eval_ri s n4) (eval_ri s n5) = (r1,r2)) ==>
      word_bignumProof_Eval r s (asm_Sub n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r s n1 n2 n3 n4.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ n4 IN FDOM
        (word_bignumProof_state_regs s) /\ ~(n1 = n2) ==>
      word_bignumProof_Eval r s (word_bignum_Mul n1 n2 n3 n4)
       (INR (reg_write n1 (SOME (FST (single_mul (FAPPLY
         (word_bignumProof_state_regs s) n3) (FAPPLY
         (word_bignumProof_state_regs s) n4) (n2w 0))))
            (reg_write n2 (SOME (SND (single_mul (FAPPLY
              (word_bignumProof_state_regs s) n3) (FAPPLY
              (word_bignumProof_state_regs s) n4) (n2w 0)))) s)))) /\
   (!r s n1 n2 n3 n4 n5.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ n4 IN FDOM
        (word_bignumProof_state_regs s) /\ n5 IN FDOM
        (word_bignumProof_state_regs s) /\ ~(n1 = n2) /\
      single_div_pre (FAPPLY (word_bignumProof_state_regs s) n3)
        (FAPPLY (word_bignumProof_state_regs s) n4) (FAPPLY
        (word_bignumProof_state_regs s) n5) ==>
      word_bignumProof_Eval r s (word_bignum_Div n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME (FST (single_div (FAPPLY
         (word_bignumProof_state_regs s) n3) (FAPPLY
         (word_bignumProof_state_regs s) n4) (FAPPLY
         (word_bignumProof_state_regs s) n5))))
            (reg_write n2 (SOME (SND (single_div (FAPPLY
              (word_bignumProof_state_regs s) n3) (FAPPLY
              (word_bignumProof_state_regs s) n4) (FAPPLY
              (word_bignumProof_state_regs s) n5)))) s)))) /\
   (!r s1 p vs s2 rec.
      word_bignumProof_Eval (if rec then SOME p else NONE)
        (delete_vars vs (word_bignumProof_dec_clock s1))
        (word_bignum_LoopBody p) (INR s2) /\
          ~(word_bignumProof_state_clock s1 = 0) ==>
      word_bignumProof_Eval r s1 (word_bignum_Loop rec vs p) (INR
        s2)) /\
   (!s1 save_regs vs p s2 s3.
      word_bignumProof_Eval (SOME p) (delete_vars vs
        (word_bignumProof_dec_clock s1)) (word_bignum_LoopBody p) (INR
        s2) /\
      word_bignumProof_copy_vars save_regs
        (word_bignumProof_state_regs s1) s2 = SOME s3 /\
        ~(word_bignumProof_state_clock
      s1 = 0) ==>
      word_bignumProof_Eval (SOME p) s1 (word_bignum_Rec save_regs
        vs) (INR s3)) /\
   (!r s1 p s2.
      word_bignumProof_Eval r s1 p (INR s2) ==>
      word_bignumProof_Eval r s1 (word_bignum_LoopBody p) (INR s2))
        /\
   (!r s1 s2 s3 p.
      word_bignumProof_Eval r s1 p (INL s2) /\
        ~(word_bignumProof_state_clock s2 = 0) /\
      word_bignumProof_Eval r (word_bignumProof_dec_clock s2)
        (word_bignum_LoopBody p) (INR s3) ==>
      word_bignumProof_Eval r s1 (word_bignum_LoopBody p) (INR
        s3))`;;

(* HOL4 word_bignumProofScript.sml:158: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:160-177: ML code, not ported *)

let Eval_NONE_IMP = prove
 (`!s1 c s2 p. word_bignumProof_Eval NONE s1 c s2 ==>
  word_bignumProof_Eval (SOME p) s1 c s2`,
  CHEAT_TAC);;


(* verification of compiler to wordLang *)

let array_rel_def = new_definition
  `array_rel arr v1 v2 v3 m dm frame =
     (?a1 a2 a3 rest1 rest2.
       v1 = SOME (wordLang_Word a1) /\
       v2 = SOME (wordLang_Word a2) /\
       v3 = SOME (wordLang_Word a3) /\
       (misc_word_list a1 (MAP wordLang_Word (arr In1)) *
        misc_word_list a3 (MAP wordLang_Word (arr Out)) * rest1)
          (fun2set (m,dm)) /\
       (misc_word_list a2 (MAP wordLang_Word (arr In2)) *
        misc_word_list a3 (MAP wordLang_Word (arr Out)) * rest2)
          (fun2set (m,dm)) /\
       (misc_word_list a3 (MAP wordLang_Word (arr Out)) * frame)
         (fun2set (m,dm)))`;;

let code_subset_def = new_definition
  `code_subset (n1,cs1) (n2,cs2) <=>
     (!n v. ALOOKUP cs1 n = SOME v ==> ALOOKUP cs2 n = SOME v)`;;

let word_bignumProof_code_rel_def = new_definition
  `word_bignumProof_code_rel cs code <=>
     (!prog n p2.
        ALOOKUP (SND cs) prog = SOME (n,p2) ==>
        (?cs1 l2 i2 cs2.
          word_bignum_compile n 2 1 cs1 prog = (p2,l2,i2,cs2) /\
          sptree_lookup n code = SOME (1,word_bignum_Seq p2
            (wordLang_Return 0 [0])) /\
          code_subset cs2 cs))`;;

let div_code_assum_def = new_definition
  `div_code_assum (:'ffi) (:'c) code =
     (!(t1:('a,'c,'ffi)wordSem_state) n l i0 i1 i2 i3 i4 w3 w4 w5
       ret_val.
       0 < i0 /\ 0 < i1 /\ 0 < i2 /\ 0 < i3 /\ 0 < i4 /\
       ALL_DISTINCT [i0; i1; i2; i3; i4] /\ wordSem_state_code
       t1 = code /\ ~(wordSem_state_termdep t1 = 0) /\
       wordSem_get_var 0 t1 = SOME ret_val /\ single_div_pre w3 w4 w5
         ==>
       (?max'.
         wordSem_evaluate
           (DivCode n l i0 i1 i2 i3 i4,wordSem_state_locals_fupd (K
                 (sptree_insert i2 (wordLang_Word w3) (sptree_insert
                   i3 (wordLang_Word w4) (sptree_insert i4
                   (wordLang_Word w5) (wordSem_state_locals
                   t1)))))
            t1) =
         (NONE,
           (let (w1,w2) = single_div w3 w4 w5 in
             (wordSem_set_var 0 ret_val o wordSem_set_var i1
               (wordLang_Word w2) o
              wordSem_set_var i0 (wordLang_Word w1) o
                wordSem_set_store (Temp (n2w 28)) (wordLang_Word w2)) (
             wordSem_state_stack_max_fupd (K max')
               (wordSem_state_locals_fupd (K LN)
               (wordSem_state_permute_fupd (K (\n.
               wordSem_state_permute t1 (n + 1))) t1)))))))`;;

(* HOL4 word_bignumProofScript.sml:244: the overload max_var_name,
   which the port expands *)

let word_bignumProof_state_rel_def = new_definition
  `word_bignumProof_state_rel s (t:('a,'c,'ffi)wordSem_state) cs t0
  frame <=> word_bignumProof_state_clock
     // clock related
     s = wordSem_state_clock t /\
     // array related
     array_rel (word_bignumProof_state_arrays s) (FLOOKUP
       (wordSem_state_store t) TempIn1)
                        (FLOOKUP (wordSem_state_store t) TempIn2)
                        (FLOOKUP (wordSem_state_store t) TempOut)
                          (wordSem_state_memory t)
                          (wordSem_state_mdomain t) frame /\
     (
      // regs related
      !a v.
        FLOOKUP (word_bignumProof_state_regs s) a = SOME v ==>
        a < 25 /\
        FLOOKUP (wordSem_state_store t) (Temp (n2w a)) = SOME
          (wordLang_Word v)) /\
     // code assumption
     word_bignumProof_code_rel cs (wordSem_state_code t) /\
     div_code_assum (:'ffi) (:'c) (wordSem_state_code t) /\
       ~(wordSem_state_termdep
     t = 0) /\ wordSem_state_gc_fun
     // rest same as original
     t0 = wordSem_state_gc_fun t /\ wordSem_state_handler
     t0 = wordSem_state_handler t /\ wordSem_state_termdep
     t0 = wordSem_state_termdep t /\ wordSem_state_code
     t0 = wordSem_state_code t /\ wordSem_state_be
     t0 = wordSem_state_be t /\ state_ffi
     t0 = wordSem_state_ffi t /\ wordSem_state_compile
     t0 = wordSem_state_compile t /\ wordSem_state_compile_oracle
     t0 = wordSem_state_compile_oracle t /\ wordSem_state_code_buffer
     t0 = wordSem_state_code_buffer t /\ wordSem_state_data_buffer
     t0 = wordSem_state_data_buffer t /\ wordSem_state_stack_limit
     // t0.locals_size = t.locals_size /\
     // t0.stack_max = t.stack_max /\
     t0 = wordSem_state_stack_limit t /\ wordSem_state_stack_size
     t0 = wordSem_state_stack_size t /\
     FLOOKUP (wordSem_state_store t) TempOut = FLOOKUP
       (wordSem_state_store t0) TempOut /\
     (!n. (!r. ~(n = Temp r)) ==> FLOOKUP (wordSem_state_store t)
       n = FLOOKUP (wordSem_state_store t0) n)`;;

(* [local] *)
let state_rel_delete_vars = prove
 (`word_bignumProof_state_arrays
       s1 = word_bignumProof_state_arrays s2 /\
         word_bignumProof_state_clock s1 = word_bignumProof_state_clock
         s2 /\ word_bignumProof_state_regs
       s2 SUBMAP word_bignumProof_state_regs s1 ==>
       word_bignumProof_state_rel s1 t1 cs t0 frame ==>
       word_bignumProof_state_rel s2 t1 cs t0 frame`,
  CHEAT_TAC);;

(* state_rel_delete_vars[local] *)
let word_bignumProof_state_rel_delete_vars = prove
 (`!vs. word_bignumProof_state_rel s1 t1 cs t0 frame ==>
        word_bignumProof_state_rel (delete_vars vs s1) t1 cs t0
          frame`,
  CHEAT_TAC);;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let exp_ok_def,exp_ok_ind = define_wf
  `MEASURE (\x0. wordLang_exp_size (\x. 0) x0)`
  [`exp_ok x1 =
        match x1 with
          wordLang_Const _4 -> T
        | (wordLang_Var i) -> i < (25)
        | (wordLang_Op _5 [x; y]) -> exp_ok x /\ exp_ok y
        | (wordLang_Shift sh e n) -> exp_ok e
        | _6 -> F`];;

let syntax_ok_aux_def,syntax_ok_aux_ind = define_shaped_rec
  "match"
  [`syntax_ok_aux x1 =
      match x1 with
        word_bignum_Loop r vs body -> syntax_ok_aux body
      | (word_bignum_LoopBody body) -> F
      | (word_bignum_Seq p1 p2) -> syntax_ok_aux p1 /\ syntax_ok_aux
        p2
      | (word_bignum_Assign t1 e) -> t1 < (25) /\ exp_ok e
      | (word_bignum_Load t1 t2 _7) -> t1 < (25) /\ t2 < (25)
      | (word_bignum_Store t1 t2) -> t1 < (25) /\ t2 < (25)
      | (word_bignum_If t1 t2 t3 p1 p2) ->
      t2 < (25) /\ (!r. t3 = Reg r ==> r < (25)) /\
      syntax_ok_aux p1 /\ syntax_ok_aux p2
      | (asm_Add n1 n2 n3 n4 n5) ->
      n1 < (25) /\ n2 < (25) /\ n3 < (25) /\
      (!r. n4 = Reg r ==> r < (25)) /\
      (!r. n5 = Reg r ==> r < (25))
      | (asm_Sub n1 n2 n3 n4 n5) ->
      n1 < (25) /\ n2 < (25) /\ n3 < (25) /\
      (!r. n4 = Reg r ==> r < (25)) /\
      (!r. n5 = Reg r ==> r < (25))
      | (word_bignum_Mul n1 n2 n3 n4) ->
      n1 < (25) /\ n2 < (25) /\
      n3 < (25) /\ n4 < (25)
      | (word_bignum_Div n1 n2 n3 n4 n5) ->
      n1 < (25) /\ n2 < (25) /\
      n3 < (25) /\ n4 < (25) /\ n5 < (25)
      | (word_bignum_Rec save_regs _8) ->
      ALL (\n. n < (25)) save_regs /\ ALL_DISTINCT save_regs
      | _9 -> T`];;

let word_bignumProof_syntax_ok_def = new_definition
  `word_bignumProof_syntax_ok p =
      match p with
        word_bignum_LoopBody body -> syntax_ok_aux body
      | p -> syntax_ok_aux p`;;

let evaluate_Seq_Seq = prove
 (`!p1 p2 p3 t1.
      wordSem_evaluate (wordLang_Seq p1 (wordLang_Seq p2 p3),t1) =
        wordSem_evaluate (wordLang_Seq (wordLang_Seq p1 p2) p3,t1)`,
  CHEAT_TAC);;

(* [local] *)
let env_to_list_insert_0_LN = prove
 (`env_to_list (sptree_insert 0 ret_val LN) p = ([0,ret_val],(\n. p (n
  + 1)))`,
  CHEAT_TAC);;

(* [local] *)
let code_subset_refl = prove
 (`!c1. code_subset c1 c1`,
  CHEAT_TAC);;

(* [local] *)
let code_subset_trans = prove
 (`!c1 c2 c3. code_subset c1 c2 /\ code_subset c2 c3 ==> code_subset
  c1 c3`,
  CHEAT_TAC);;

(* [local] *)
let compile_IMP_code_subset = prove
 (`!prog n l i cs p1 l1 i1 cs1.
     word_bignum_compile n l i cs prog = (p1,l1,i1,cs1) ==>
       code_subset cs cs1 /\ i <= i1`,
  CHEAT_TAC);;

(* [local] *)
let has_compiled_lemma = prove
 (`word_bignumProof_state_rel s1 t1 cs2 t0 frame /\
   has_compiled p cs = INL x /\ code_subset cs cs2 ==>
   (?cs0 p1 l1 i1 cs' cs1.
     word_bignum_compile x 2 1 cs' p = (p1,l1,i1,cs1) /\ code_subset
       cs1 cs2 /\
     sptree_lookup x (wordSem_state_code t1) = SOME
       (1,word_bignum_Seq p1 (wordLang_Return 0 [0])))`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_IN_FDOM = prove
 (`word_bignumProof_state_rel s1 t1 cs2 t0 frame /\ r IN FDOM
  (word_bignumProof_state_regs s1) ==>
   Temp (n2w r) IN FDOM (wordSem_state_store t1) /\ FAPPLY
     (wordSem_state_store
   t1) (Temp (n2w r)) = wordLang_Word (FAPPLY
     (word_bignumProof_state_regs s1) r)`,
  CHEAT_TAC);;


(* compile_exp_thm[local] *)
let word_bignumProof_compile_exp_thm = prove
 (`word_bignumProof_state_rel s1 t1 cs2 t0 frame /\ eval_exp_pre s1 x /\
  good_dimindex (:'a) ==>
   wordSem_word_exp t1 (word_bignum_compile_exp x) = SOME
     (wordLang_Word (eval_exp s1 (x:'a wordLang_exp)))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_SeqTemp = prove
 (`wordSem_evaluate (SeqTemp i r p,t) =
   (if Temp (n2w r) IN FDOM (wordSem_state_store t) then
      wordSem_evaluate (p,wordSem_set_var i (FAPPLY
        (wordSem_state_store t) (Temp (n2w r))) t) else
        wordSem_evaluate (SeqTemp i r p,t))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_SeqTempImm = prove
 (`wordSem_evaluate (SeqTempImm i ri p,t) =
   (if !r. ri = Reg r ==> Temp (n2w r) IN FDOM (wordSem_state_store
     t) then
      wordSem_evaluate (p,wordSem_set_var i (match ri with Imm w ->
        wordLang_Word w | Reg r -> FAPPLY (wordSem_state_store t)
        (Temp (n2w r))) t) else wordSem_evaluate (SeqTempImm i ri
        p,t))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_SeqTempImmNot = prove
 (`wordSem_evaluate (SeqTempImmNot i ri p,t) =
   (if !r. ri = Reg r ==> Temp (n2w r) IN FDOM (wordSem_state_store
     t) /\
                         (?w. FAPPLY (wordSem_state_store t) (Temp
                           (n2w r)) = wordLang_Word w) then
      wordSem_evaluate (p,wordSem_set_var i (match ri with Imm w ->
        wordLang_Word (word_not w) | Reg r -> (match FAPPLY
        (wordSem_state_store t) (Temp (n2w r)) with wordLang_Word w ->
        wordLang_Word (word_not w))) t) else wordSem_evaluate
        (SeqTempImmNot i ri p,t))`,
  CHEAT_TAC);;

(* [local] *)
let LESS_LENGTH_IMP_APPEND = prove
 (`!xs n. n < LENGTH xs ==>
          (?ys z zs. xs = APPEND ys (CONS z zs) /\ LENGTH ys = n)`,
  CHEAT_TAC);;

(* word_list_APPEND *)
let word_bignumProof_word_list_APPEND = prove
 (`!xs ys a. misc_word_list a (APPEND xs ys) =
              misc_word_list a xs * misc_word_list (a + n2w (LENGTH
                xs) * bytes_in_word) ys`,
  CHEAT_TAC);;

(* [local] *)
let shift_eq_bytes_in_word = prove
 (`good_dimindex (:'a) ==>
   (w << (backend_common_word_shift (:'a) MOD dimword (:'a)) = w *
     (bytes_in_word:'a word))`,
  CHEAT_TAC);;

(* [local] *)
let b2w_if = prove
 (`b2w b = (if b then (n2w 1) else (n2w 0))`,
  CHEAT_TAC);;

(* [local] *)
let b2n_if = prove
 (`b2n b = (if ~b then 0 else 1)`,
  CHEAT_TAC);;
(*Is this worth the hassle*)
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let list_update_def,list_update_ind = define_wf
  `MEASURE (\(x0,x1,x2). list_size (\n. n) x0)`
  [`list_update [] ys t = t`;
   `list_update (CONS x xs) (CONS y ys) t = sptree_insert x y
    (list_update xs ys t)`;
   `list_update (CONS x xs) [] t = sptree_insert x ARB (list_update
    xs [] t)`];;

let list_update_alist_insert = prove
 (`!xs ys t.
   LENGTH xs = LENGTH ys ==>
   list_update xs ys t = alist_insert xs ys t`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_LoadRegs = prove
 (`!save_regs vals t1.
     word_bignumProof_state_rel s1 t1 cs2 t0 frame /\
     ALL (\n. n < (25)) save_regs /\ ALL_DISTINCT save_regs /\
     ALL2 (\n v. FLOOKUP (word_bignumProof_state_regs s1) n = SOME v)
       save_regs vals ==>
     wordSem_evaluate (LoadRegs save_regs p,t1) =
     wordSem_evaluate (p,wordSem_state_locals_fupd (K
          (list_update (MAP (\n. n + 2) save_regs) (MAP
            wordLang_Word vals) (wordSem_state_locals t1))) t1)`,
  CHEAT_TAC);;

(* [local] *)
let domain_list_update = prove
 (`!xs ys x t. x IN domain (list_update xs ys t) <=> MEM x xs \/ x IN
  domain t`,
  CHEAT_TAC);;

let list_store_def,list_store_ind = define_rec
  [`list_store [] ys s = s`;
   `list_store (CONS x xs) ys s = (list_store xs (TL ys) s) |+
    (Temp (n2w x),HD ys)`];;

(* [local] *)
let list_store_FUPDATE = prove
 (`!save_regs st ys.
     ~(MEM h save_regs) /\ h < (25) /\
     ALL (\n. n < (25)) save_regs ==>
     list_store save_regs ys (st |+ (Temp (n2w h),wordLang_Word v)) =
     list_store save_regs ys st |+ (Temp (n2w h),wordLang_Word v)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_SaveRegs = prove
 (`!save_regs t7 vals.
     ALL2 (\n v. sptree_lookup (n + 2) (wordSem_state_locals t7) =
       SOME (wordLang_Word v)) save_regs vals /\
     ALL_DISTINCT save_regs /\ ALL (\n. n < (25)) save_regs ==>
     wordSem_evaluate (SaveRegs save_regs,t7) =
       (NONE,wordSem_state_store_fupd (K (list_store save_regs (MAP
         wordLang_Word vals) (wordSem_state_store t7))) t7)`,
  CHEAT_TAC);;

(* [local] *)
let FLOOKUP_list_store_ignore = prove
 (`!save_regs vals st.
   ALL (\n. n < (25)) save_regs ==>
   FLOOKUP (list_store save_regs vals st) TempIn1 = FLOOKUP st
     TempIn1 /\
   FLOOKUP (list_store save_regs vals st) TempIn2 = FLOOKUP st
     TempIn2 /\
   FLOOKUP (list_store save_regs vals st) TempOut = FLOOKUP st
     TempOut /\
   (!n. (!r. ~(n = Temp r)) ==>
       FLOOKUP (list_store save_regs vals st) n = FLOOKUP st n)`,
  CHEAT_TAC);;

(* [local] *)
let copy_vars_const = prove
 (`!save_regs s2 s3.
     word_bignumProof_copy_vars save_regs
       (word_bignumProof_state_regs s1) s2 = SOME s3 ==>
       word_bignumProof_state_clock
     s3 = word_bignumProof_state_clock s2 /\
       word_bignumProof_state_arrays s3 =
       word_bignumProof_state_arrays s2`,
  CHEAT_TAC);;

(* [local] *)
let lookup_list_update_ADD_2 = prove
 (`!save_regs ws.
     sptree_lookup 0 (list_update (MAP (\n. n + 2) save_regs) ws l)
       = sptree_lookup 0 l`,
  CHEAT_TAC);;

(* [local] *)
let copy_vars_ignore = prove
 (`!save_regs regs' s2 s3.
     word_bignumProof_copy_vars save_regs regs' s2 = SOME s3 /\
     ~(MEM a save_regs) /\ a < (25) /\
     ALL (\n. n < (25)) save_regs ==> FAPPLY
       (word_bignumProof_state_regs
     s3) a = FAPPLY (word_bignumProof_state_regs s2) a`,
  CHEAT_TAC);;

(* [local] *)
let copy_vars_IMP = prove
 (`!save_regs s2 s3.
     word_bignumProof_copy_vars save_regs
       (word_bignumProof_state_regs s1) s2 = SOME s3 ==>
     (?vals. ALL2 (\n v. FLOOKUP (word_bignumProof_state_regs s1) n
       = SOME v) save_regs vals)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_REL_lemma = prove
 (`!xs ys.
     (!x y. MEM x xs /\ MEM y ys ==> P x y ==> Q x y) ==>
     ALL2 P xs ys ==>
     ALL2 Q xs ys`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:677-680: ML code, not ported *)

(* compile_thm *)
let word_bignumProof_compile_thm = prove
 (`!rec s1 prog s2.
      word_bignumProof_Eval rec s1 prog s2 ==>
      (!n l i cs p1 l1 i1 cs1 cs2 t1 (ret_val:'a word_loc) p9.
        word_bignum_compile n l i cs prog = (p1,l1,i1,cs1) /\
        word_bignumProof_state_rel s1 t1 cs2 t0 frame /\ 0 < i /\
        word_bignumProof_syntax_ok prog /\ code_subset cs1 cs2 /\
        (!body. rec = SOME body ==>
                (?l i cs p1 l1 i1 cs1.
                  word_bignum_compile n l i cs body = (p1,l1,i1,cs1)
                    /\
                  0 < i /\ syntax_ok_aux body /\ code_subset cs1 cs2
                    /\
                  sptree_lookup n (wordSem_state_code t1) = SOME
                    (1,word_bignum_Seq p1 (wordLang_Return 0 [0])))) /\
        (!body. prog = word_bignum_LoopBody body ==>
                p9 = wordLang_Return 0 [0] /\
                sptree_lookup n (wordSem_state_code t1) = SOME
                  (1,word_bignum_Seq p1 (wordLang_Return 0 [0]))) /\
        wordSem_get_var 0 t1 = SOME ret_val /\ good_dimindex (:'a)
          ==>
        (?t2 res.
          (wordSem_evaluate (word_bignum_Seq p1 p9,t1) = res) /\
          (match s2 with INR s -> res = wordSem_evaluate (p9,t2) /\
                     0 < i1 /\ stack
                     t2 = stack t1 /\
                     wordSem_get_var 0 t2 = SOME ret_val /\
                     word_bignumProof_state_rel s t2 cs2 t0 frame /\
                       wordSem_state_code t2 = wordSem_state_code t1 |
                       INL s -> res = wordSem_evaluate (wordLang_Call
                       NONE (SOME n) [0] NONE,t2) /\
                     0 < i1 /\ stack
                     t2 = stack t1 /\
                     wordSem_get_var 0 t2 = SOME ret_val /\
                     word_bignumProof_state_rel s t2 cs2 t0 frame
                       /\ wordSem_state_code t2 = wordSem_state_code
                       t1)))`,
  CHEAT_TAC);;

let good_code_def = new_definition
  `word_bignumProof_good_code cs3 =
     (!prog n p2.
       MEM (prog,n,p2) (SND cs3) ==>
       (?cs1 l2' i2 cs2.
         word_bignum_compile n 2 1 cs1 prog = (p2,l2',i2,cs2) /\
           code_subset cs2 cs3))`;;

let _ = size_thms "mini";;
(* [local] *)
let compile_LESS_mini_size = prove
 (`!k l1 l2 yy5 code xx1 xx2 xx3 xx5.
     word_bignum_compile k l1 l2 yy5 code = (xx1,xx2,xx3,xx5) ==>
     (!x. MEM x (SND xx5) /\ ~(MEM x (SND yy5)) ==>
         mini_size (K 0) (FST x) < mini_size (K 0) code)`,
  CHEAT_TAC);;

(* [local] *)
let MEM_compile = prove
 (`!k l1 l2 yy5 code xx1 xx2 xx3 xx5.
     word_bignumProof_good_code yy5 /\
     word_bignum_compile k l1 l2 yy5 code = (xx1,xx2,xx3,xx5) ==>
     word_bignumProof_good_code xx5`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:1327-1330: a theorem that HOL4
   states as the value of an ML expression: compile_NIL_IMP *)


(* correctenss judgement *)

(* HOL4 word_bignumProofScript.sml:1335: ML code, not ported *)

let corr_def = new_definition
  `Corr prog (s:'a word_bignumProof_state) s1 p <=>
     (p ==> word_bignumProof_Eval NONE s prog s1)`;;

(* [local] *)
let Corr_Skip = prove
 (`Corr word_bignum_Skip s (INR s) T`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Seq = prove
 (`Corr p2 s1 s2 q2 ==>
   Corr p1 s (INR s1) q1 ==>
   Corr (word_bignum_Seq p1 p2) s s2 (q1 /\ q2)`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Seq_alt = prove
 (`(b ==> Corr p2 s1 s2 q2) ==>
   Corr p1 s (INR s1) q1 ==>
   b ==> Corr (word_bignum_Seq p1 p2) s s2 (q1 /\ q2)`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Continue = prove
 (`Corr wordSem_Continue s (INL s) T`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Assign = prove
 (`Corr (word_bignum_Assign n x) s
     (INR (reg_write n (SOME (eval_exp s x)) s))
     (eval_exp_pre s x)`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Delete = prove
 (`Corr (word_bignum_Delete vs) s (INR (delete_vars vs s)) T`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Load = prove
 (`Corr (word_bignum_Load r i a) s
       (INR (reg_write r (SOME (EL (w2n (FAPPLY
         (word_bignumProof_state_regs s) i))
         (word_bignumProof_state_arrays s a))) s))
       (i IN FDOM (word_bignumProof_state_regs s) /\ w2n (FAPPLY
         (word_bignumProof_state_regs s) i) < LENGTH
         (word_bignumProof_state_arrays s a))`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Store = prove
 (`Corr (word_bignum_Store r i) s
       (INR (array_write Out (LUPDATE (FAPPLY
         (word_bignumProof_state_regs s) r) (w2n (FAPPLY
         (word_bignumProof_state_regs s) i))
                   (word_bignumProof_state_arrays s Out)) s))
       (r IN FDOM (word_bignumProof_state_regs s) /\ i IN FDOM
         (word_bignumProof_state_regs s) /\
        w2n (FAPPLY (word_bignumProof_state_regs s) i) < LENGTH
          (word_bignumProof_state_arrays s Out))`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Swap = prove
 (`Corr word_bignum_Swap s
     (INR (array_write In1 (word_bignumProof_state_arrays s In2)
       (array_write In2 (word_bignumProof_state_arrays s In1) s))) T`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Add = prove
 (`Corr (asm_Add n1 n2 n3 ri1 ri2) s
    (INR (reg_write n1
           (SOME (FST (single_add_word (FAPPLY
             (word_bignumProof_state_regs s) n3) (eval_ri s ri1)
             (eval_ri s ri2))))
         (reg_write n2
           (SOME (SND (single_add_word (FAPPLY
             (word_bignumProof_state_regs s) n3) (eval_ri s ri1)
             (eval_ri s ri2)))) s)))
    (n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s ri1
      /\ eval_ri_pre s ri2 /\
     (~(eval_ri s ri2 = (n2w 0)) ==> eval_ri s ri2 = (n2w 1)) /\
       ~(n1 = n2))`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Sub = prove
 (`Corr (asm_Sub n1 n2 n3 ri1 ri2) s
    (INR (reg_write n1
           (SOME (FST (single_sub_word (FAPPLY
             (word_bignumProof_state_regs s) n3) (eval_ri s ri1)
             (eval_ri s ri2))))
         (reg_write n2
           (SOME (SND (single_sub_word (FAPPLY
             (word_bignumProof_state_regs s) n3) (eval_ri s ri1)
             (eval_ri s ri2)))) s)))
    (n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s ri1
      /\ eval_ri_pre s ri2 /\
     (~(eval_ri s ri2 = (n2w 0)) ==> eval_ri s ri2 = (n2w 1)) /\
       ~(n1 = n2))`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Mul = prove
 (`Corr (word_bignum_Mul n1 n2 n3 n4) s
    (INR (reg_write n1 (SOME (FST (single_mul (FAPPLY
      (word_bignumProof_state_regs s) n3) (FAPPLY
      (word_bignumProof_state_regs s) n4) (n2w 0))))
         (reg_write n2 (SOME (SND (single_mul (FAPPLY
           (word_bignumProof_state_regs s) n3) (FAPPLY
           (word_bignumProof_state_regs s) n4) (n2w 0)))) s)))
    (n3 IN FDOM (word_bignumProof_state_regs s) /\ n4 IN FDOM
      (word_bignumProof_state_regs s) /\ ~(n1 = n2))`,
  CHEAT_TAC);;

(* [local] *)
let Corr_Div = prove
 (`Corr (word_bignum_Div n1 n2 n3 n4 n5) s
    (INR (reg_write n1
            (SOME (FST (single_div (FAPPLY
              (word_bignumProof_state_regs s) n3) (FAPPLY
              (word_bignumProof_state_regs s) n4) (FAPPLY
              (word_bignumProof_state_regs s) n5))))
         (reg_write n2
            (SOME (SND (single_div (FAPPLY
              (word_bignumProof_state_regs s) n3) (FAPPLY
              (word_bignumProof_state_regs s) n4) (FAPPLY
              (word_bignumProof_state_regs s) n5)))) s)))
    (n3 IN FDOM (word_bignumProof_state_regs s) /\ n4 IN FDOM
      (word_bignumProof_state_regs s) /\ n5 IN FDOM
      (word_bignumProof_state_regs s) /\ ~(n1 = n2) /\
     single_div_pre (FAPPLY (word_bignumProof_state_regs s) n3)
       (FAPPLY (word_bignumProof_state_regs s) n4) (FAPPLY
       (word_bignumProof_state_regs s) n5))`,
  CHEAT_TAC);;

(* [local] *)
let Corr_If = prove
 (`Corr p1 s f1 q1 /\ Corr p2 s f2 q2 ==>
   Corr (word_bignum_If c r ri p1 p2) s
     (if wordSem_word_cmp c (eval_exp s (wordLang_Var r)) (eval_ri s
       ri) then f1 else f2)
     (r IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s ri
       /\
      (if wordSem_word_cmp c (eval_exp s (wordLang_Var r)) (eval_ri
        s ri) then q1 else q2))`,
  CHEAT_TAC);;

let loop_app_def = new_definition
  `loop_app f g x =
     (match f x with INL s -> (INL (word_bignumProof_dec_clock
       s),(g x /\ ~(word_bignumProof_state_clock s = 0))) | INR s ->
       (INR s,g x))`;;

(* [local] *)
let Corr_LoopBody = prove
 (`(!s. Corr p s (f s) (q s)) ==>
   (!s. Corr (word_bignum_LoopBody p) s (INR (SHORT_TAILREC (loop_app
     f q) s))
                              (SHORT_TAILREC_PRE (loop_app f q) s))`,
  CHEAT_TAC);;

let tick_before_def = new_definition
  `tick_before vs f s =
     (if word_bignumProof_state_clock s = 0 then (s,F) else f
       (delete_vars vs (word_bignumProof_dec_clock s)))`;;

(* [local] *)
let Corr_Loop_lemma = prove
 (`(!s. Corr (word_bignum_LoopBody p) s (INR (f s)) (q s)) ==>
   Corr (word_bignum_Loop F vs p) s (INR (f (delete_vars vs
     (word_bignumProof_dec_clock s))))
     (q (delete_vars vs (word_bignumProof_dec_clock s)) /\
       ~(word_bignumProof_state_clock s = 0))`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:1514: ML code, not ported *)

(* [local] *)
let Corr_STRENGTHEN_TERM = prove
 (`Corr p s f q ==>
   (!f' q'.
     (q' ==> (f = INR f') /\ q) ==>
     Corr p s (INR f') q')`,
  CHEAT_TAC);;


(* derive Corr thm from AST *)

(* [local] *)
let dec_clock_thm = prove
 (`word_bignumProof_dec_clock s = clock_write
  (word_bignumProof_state_clock s - 1) s`,
  CHEAT_TAC);;

let array_write_cancel = prove
 (`array_write n (word_bignumProof_state_arrays s n) s = s`,
  CHEAT_TAC);;
add_simp array_write_cancel;;

let reg_write_cancel = prove
 (`(n IN FDOM (word_bignumProof_state_regs s) ==> reg_write n (SOME
  (FAPPLY (word_bignumProof_state_regs s) n)) s = s) /\
    (~(n IN FDOM (word_bignumProof_state_regs s)) ==> reg_write n
      NONE s = s)`,
  CHEAT_TAC);;
add_simp reg_write_cancel;;

(* [local] *)
let state_eq_lemma = prove
 (`(s0 = s1) <=> word_bignumProof_state_clock
   s0 = word_bignumProof_state_clock s1 /\
   FDOM (word_bignumProof_state_regs s0) = FDOM
     (word_bignumProof_state_regs s1) /\
   (!n. n IN FDOM (word_bignumProof_state_regs s0) ==> FAPPLY
     (word_bignumProof_state_regs s0) n = FAPPLY
     (word_bignumProof_state_regs s1) n) /\
   (!n. word_bignumProof_state_arrays s0 n =
     word_bignumProof_state_arrays s1 n)`,
  CHEAT_TAC);;

let clock_write_simp = prove
 (`word_bignumProof_state_regs
      (clock_write n s) = word_bignumProof_state_regs s /\
        word_bignumProof_state_arrays
       (clock_write n s) = word_bignumProof_state_arrays s /\
         word_bignumProof_state_clock
       (clock_write n s) = n`,
  CHEAT_TAC);;
add_simp clock_write_simp;;

let dec_clock_write_simp = prove
 (`word_bignumProof_state_regs
      (word_bignumProof_dec_clock s) = word_bignumProof_state_regs s
        /\ word_bignumProof_state_arrays
       (word_bignumProof_dec_clock s) = word_bignumProof_state_arrays
         s /\ word_bignumProof_state_clock
       (word_bignumProof_dec_clock s) =
         word_bignumProof_state_clock s - 1`,
  CHEAT_TAC);;
add_simp dec_clock_write_simp;;

let reg_write_simp = prove
 (`word_bignumProof_state_regs
      (reg_write n NONE s) = word_bignumProof_state_regs s \\ n /\
        word_bignumProof_state_regs
       (reg_write n (SOME w) s) = word_bignumProof_state_regs s |+
         (n,w) /\ word_bignumProof_state_arrays
       (reg_write n v s) = word_bignumProof_state_arrays s /\
         word_bignumProof_state_clock
       (reg_write n v s) = word_bignumProof_state_clock s`,
  CHEAT_TAC);;
add_simp reg_write_simp;;

let reg_write_simp_alt = prove
 (`(FAPPLY (word_bignumProof_state_regs (reg_write n NONE s)) m = (if n
  = m then FAPPLY FEMPTY m else FAPPLY (word_bignumProof_state_regs s)
  m)) /\
    (FAPPLY (word_bignumProof_state_regs (reg_write n (SOME w) s)) m
      = (if n = m then w else FAPPLY (word_bignumProof_state_regs s) m))
      /\
    (FDOM (word_bignumProof_state_regs (reg_write n NONE s)) = FDOM
      (word_bignumProof_state_regs s) DELETE n) /\
    (FDOM (word_bignumProof_state_regs (reg_write n (SOME w) s)) =
      n INSERT FDOM (word_bignumProof_state_regs s))`,
  CHEAT_TAC);;

let array_write_simp = prove
 (`word_bignumProof_state_regs
      (array_write n w s) = word_bignumProof_state_regs s /\
        word_bignumProof_state_arrays
       (array_write n w s) = (n =+ w) (word_bignumProof_state_arrays
         s) /\ word_bignumProof_state_clock
       (array_write n w s) = word_bignumProof_state_clock s`,
  CHEAT_TAC);;
add_simp array_write_simp;;

let delete_vars_simp = prove
 (`!vs. word_bignumProof_state_clock
      (delete_vars vs s) = word_bignumProof_state_clock s /\
        word_bignumProof_state_arrays
      (delete_vars vs s) = word_bignumProof_state_arrays s /\
      (FLOOKUP (word_bignumProof_state_regs (delete_vars vs s)) n =
         (if MEM n vs then NONE else FLOOKUP
           (word_bignumProof_state_regs s) n)) /\
      ((n IN FDOM (word_bignumProof_state_regs (delete_vars vs s))) =
         (if MEM n vs then F else (n IN FDOM
           (word_bignumProof_state_regs s))))`,
  CHEAT_TAC);;
add_simp delete_vars_simp;;

(* HOL4 word_bignumProofScript.sml:1618-1619: ML code, not ported *)

let FLOOKUP_DOMSUB = prove
 (`FLOOKUP (f \\ n) m = (if m = n then NONE else FLOOKUP f m)`,
  CHEAT_TAC);;
add_simp FLOOKUP_DOMSUB;;

(* HOL4 word_bignumProofScript.sml:1627: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1629-1640: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1642-1647: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1649-1650: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1652-1654: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1656: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1658-1659: ML code, not ported *)

(* order: clock then array then reg_write *)
(* HOL4 word_bignumProofScript.sml:1662-1684: a theorem that HOL4
   states as the value of an ML expression: sort_lemma *)

(* HOL4 word_bignumProofScript.sml:1686-1690: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1692-1698: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1700-1713: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1715: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1717-1744: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1746-1748: code that the source
   has in a comment *)

(* HOL4 word_bignumProofScript.sml:1750-1773: a theorem that HOL4
   states as the value of an ML expression: lemma *)
(* HOL4 word_bignumProofScript.sml:1750-1773: the ML values that the
   definitions below antiquote *)

(* [local] *)
let reg_read_lemma1 = prove
 (`!v n. FLOOKUP (word_bignumProof_state_regs s) n = SOME v ==> (n IN
  FDOM (word_bignumProof_state_regs s) <=> T)`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:1781-1782: ML code, not ported *)

(* [local] *)
let reg_read_lemma2 = prove
 (`!v n. FLOOKUP (word_bignumProof_state_regs s) n = SOME v ==> FAPPLY
  (word_bignumProof_state_regs s) n = v`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:1790-1791: ML code, not ported *)

(* [local] *)
let array_read_lemma = prove
 (`!v n. word_bignumProof_state_arrays s n = v ==>
  word_bignumProof_state_arrays s n = v`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:1799-1800: ML code, not ported *)

(* [local] *)
let clock_read_lemma = prove
 (`word_bignumProof_state_clock
       s = l ==> word_bignumProof_state_clock s = l`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:1808-1809: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1811-1832: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1834-1840: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1842-1849: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1851-1852: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1854-1856: ML code, not ported *)

(* Corr_move_pre[local] *)
let corr_move_pre = prove
 (`(b ==> Corr code s f p) <=> Corr code s f (b /\ p)`,
  CHEAT_TAC);;

(* [local] *)
let loop_app_EQ = prove
 (`(loop_app f g x = (INR t,T) <=> f x = INR t /\ g x) /\
   (loop_app f g x = (INL t,T) <=>
      (?x'. f x = INL x' /\ word_bignumProof_dec_clock x' = t /\ g
        x /\ ~(word_bignumProof_state_clock x' = 0)))`,
  CHEAT_TAC);;

(* [local] *)
let true_pres = prove
 (`mc_single_mul_pre (r0,r1,r2) /\
   mc_mul_by_single2_pre (r6,r7,r8) /\
   mc_cmp3_pre (r1,r2,r3,r9,r10,r11) /\
   mc_cmp_mul2_pre (r6,r7,r8,r9,r10,r11) /\
   mc_cmp2_pre (r0,r2,r10,r11) /\
   mc_adj_cmp_pre (r0,r3,r8) /\
   mc_idiv_mod_header_pre (r6,r11) /\
   mc_iadd1_pre (r1,r2,xs,ys) /\
   mc_iadd2_pre (r1,r2,r3,r4,xs,ys) /\
   mc_iadd3_pre (r1,xs,ys) /\
   mc_isub_flip_pre (r1,r2) /\
   mc_imul1_pre (r10,r11) /\
   mc_sub1_pre r6 /\ mc_cmp2_pre (r0,r2,r10,r11)`,
  CHEAT_TAC);;

(* [local] *)
let single_add_word_imp_0_1 = prove
 (`single_add_word x1 x2 x3 = (y1,y2) ==> ~(y2 = (n2w 0)) ==> y2 =
  (n2w 1)`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:1902-1913: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1915-1926: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1928-1937: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1939-1941: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1943-1956: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1958: code that the source has in
   a comment *)

(* HOL4 word_bignumProofScript.sml:1960: ML code, not ported *)

  (* look up definitions *)
(* HOL4 word_bignumProofScript.sml:1963-1970: ML code, not ported *)
  (* compute ret and cont Corr thms *)
(* HOL4 word_bignumProofScript.sml:1972-2008: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2010-2058: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:2060-2072: ML code, not ported *)
  (* -- *)
(* HOL4 word_bignumProofScript.sml:2074-2129: the ML values that the
   definitions below antiquote *)

(*
  max_print_depth := 15
*)

(* HOL4 word_bignumProofScript.sml:2135-2170: a theorem that HOL4
   states as the value of an ML expression: lemma *)
(* HOL4 word_bignumProofScript.sml:2135-2170: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2172-2186: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2188-2209: a theorem that HOL4
   states as the value of an ML expression: lemma1 *)
(* HOL4 word_bignumProofScript.sml:2188-2209: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2211-2224: a theorem that HOL4
   states as the value of an ML expression: lemma *)
(* HOL4 word_bignumProofScript.sml:2211-2224: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2226-2228: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:2230: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:2232-2256: code that the source
   has in a comment *)

(* connecting all the theormes *)

(* HOL4 word_bignumProofScript.sml:2260-2262: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:2264: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2266: ML code, not ported *)

(* [local] *)
let i2mw_NOT_NIL = prove
 (`~(SND (i2mw i2) = []) <=> ~(i2 = (&0))`,
  CHEAT_TAC);;

(* [local] *)
let mw_ok_SND_i2mw = prove
 (`mw_ok (SND (i2mw fg))`,
  CHEAT_TAC);;

(* code_subset_refl[local] *)
let word_bignumProof_code_subset_refl = prove
 (`!cs. code_subset cs cs`,
  CHEAT_TAC);;

(* HOL4 word_bignumProofScript.sml:2287: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:2289-2333: a theorem that HOL4
   states as the value of an ML expression: evaluate_mc_iop *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["shift"];;

(* and the interface *)
let _ = unhide_overloads ();;
