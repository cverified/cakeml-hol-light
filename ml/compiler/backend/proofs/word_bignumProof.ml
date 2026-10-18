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
needs "lib/mc_multiword.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "lib/tailrec.ml";;
needs "semantics/ast.ml";;

(* HOL4 word_bignumProofScript.sml:11-12: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:16: ML code, not ported *)


(* semantics of the little language *)

let word_bignumProof_state_FIELDS =
  define_record "word_bignumProof_state"
  ["regs","(num,'a word)fmap";
   "arrays","address->('a word) list";
   "clock","num"];;
hol4_overload "regs" "word_bignumProof_state_regs";;
hol4_overload "regs_fupd" "word_bignumProof_state_regs_fupd";;
hol4_overload "state_clock" "word_bignumProof_state_clock";;
hol4_overload "state_clock_fupd" "word_bignumProof_state_clock_fupd";;

let eval_exp_def = cake_define
  `eval_exp s (wordLang_Const w) = w /\
   eval_exp s (Var v) = FAPPLY (word_bignumProof_state_regs s) v /\
   eval_exp s (wordLang_Op asm_Add [x1; x2]) = eval_exp s x1 +
     eval_exp s x2 /\
   eval_exp s (wordLang_Op asm_Sub [x1; x2]) = eval_exp s x1 -
     eval_exp s x2 /\
   eval_exp s (wordLang_Op And [x1; x2]) = word_and (eval_exp s x1)
     (eval_exp s x2) /\
   eval_exp s (wordLang_Op asm_Or [x1; x2]) = word_or (eval_exp s x1)
     (eval_exp s x2) /\
   eval_exp s (wordLang_Op Xor [x1; x2]) = word_xor (eval_exp s x1)
     (eval_exp s x2) /\
   eval_exp s (Shift Lsl x1 x2) = eval_exp s x1 << (w2n (eval_exp s
     x2)) /\
   eval_exp s (Shift Asr x1 x2) = eval_exp s x1 >> (w2n (eval_exp s
     x2)) /\
   eval_exp s (Shift Lsr x1 x2) = eval_exp s x1 >>> (w2n (eval_exp s
     x2)) /\
   eval_exp s (Shift Ror x1 x2) = word_ror (eval_exp s x1) (w2n
     (eval_exp s x2))`;;

let eval_exp_pre_def = cake_define
  `eval_exp_pre s x2 =
        match x2 with
          wordLang_Const w -> T
        | (Var v) -> v IN FDOM (word_bignumProof_state_regs s)
        | (wordLang_Op _1 [x; y]) -> eval_exp_pre s x /\ eval_exp_pre
          s y
        | (Shift sh x1 x2) ->
        eval_exp_pre s x1 /\ eval_exp_pre s x2 /\ (w2n (eval_exp s
          x2) < 32)
        | _2 -> F`;;

let eval_ri_pre_def = cake_define_list
  [`eval_ri_pre (s:'a word_bignumProof_state) (Reg r) <=>
  eval_exp_pre (s:'a word_bignumProof_state) ((Var r):'a
  wordLang_exp)`;
   `eval_ri_pre (s:'a word_bignumProof_state) (Imm (w:'a word)) <=>
  T`];;

let eval_ri_def = cake_define_list
  [`eval_ri (s:'a word_bignumProof_state) (Reg r) =
      eval_exp s ((Var r):'a wordLang_exp)`;
   `eval_ri (s:'a word_bignumProof_state) (Imm (w:'a word)) = w`];;

let dec_clock_def = cake_define
  `word_bignumProof_dec_clock s = state_clock_fupd (K (state_clock s
  - 1)) s`;;
hol4_overload "dec_clock" "word_bignumProof_dec_clock";;

let reg_write_def = cake_define_list
  [`reg_write v NONE (s:'a word_bignumProof_state) =
  word_bignumProof_state_regs_fupd (K (word_bignumProof_state_regs s
  \\ v)) s`;
   `reg_write n (SOME v) (s:'a word_bignumProof_state) =
  word_bignumProof_state_regs_fupd (K (word_bignumProof_state_regs
  s |+ (n,v))) s`];;

let delete_vars_def = cake_define_list
  [`delete_vars [] s = s`;
   `delete_vars (v :: vs) s = reg_write v NONE (delete_vars vs s)`];;

let array_write_def = cake_define
  `array_write n v s = word_bignumProof_state_arrays_fupd (K ((n =+
  v) (word_bignumProof_state_arrays s))) s`;;

let clock_write_def = cake_define
  `clock_write l s = state_clock_fupd (K l) s`;;

let copy_vars_def = cake_define_list
  [`word_bignumProof_copy_vars [] s t = SOME t`;
   `word_bignumProof_copy_vars (n :: ns) s t =
         (match FLOOKUP s n with NONE -> NONE | SOME x ->
           word_bignumProof_copy_vars ns s (reg_write n (SOME x)
           t))`];;
hol4_overload "copy_vars" "word_bignumProof_copy_vars";;

let eval = cake_inductive
  `(!r s. word_bignumProof_Eval r s Skip (INR (s:'a
  word_bignumProof_state))) /\
   (!r s. word_bignumProof_Eval r s Continue (INL s)) /\
   (!r vs s. word_bignumProof_Eval r s (word_bignum_Delete vs) (INR
     (delete_vars vs (s:'a word_bignumProof_state)))) /\
   (!r s x n.
      eval_exp_pre s x ==>
      word_bignumProof_Eval r s (Assign n x) (INR (reg_write n (SOME
        (eval_exp s x)) s))) /\
   (!r s1 s2 s3 p1 p2.
      word_bignumProof_Eval r s1 p1 (INR s2) /\ word_bignumProof_Eval
        r s2 p2 s3 ==>
      word_bignumProof_Eval r s1 (Seq p1 p2) s3) /\
   (!rec s1 c r ri p1 p2 s2.
      r IN FDOM (word_bignumProof_state_regs s1) /\ eval_ri_pre s1 ri
        /\
      word_bignumProof_Eval rec s1 (if word_cmp c (eval_exp s1 (Var
        r)) (eval_ri s1 ri) then p1 else p2) s2 ==>
      word_bignumProof_Eval rec s1 (If c r ri p1 p2) s2) /\
   (!rec s r i a w.
      (FLOOKUP (word_bignumProof_state_regs s) i = SOME w) /\
      w2n w < LENGTH (word_bignumProof_state_arrays s a) ==>
      word_bignumProof_Eval rec s (Load r i a) (INR (reg_write r
        (SOME (EL (w2n w) (word_bignumProof_state_arrays s a))) s))) /\
   (!rec s r i w wr.
      (FLOOKUP (word_bignumProof_state_regs s) i = SOME w) /\
        (FLOOKUP (word_bignumProof_state_regs s) r = SOME wr) /\
      w2n w < LENGTH (word_bignumProof_state_arrays s Out) ==>
      word_bignumProof_Eval rec s (Store r i) (INR (array_write Out
        (LUPDATE wr (w2n w) (word_bignumProof_state_arrays s Out)) s)))
        /\
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
      word_bignumProof_Eval r s (Add n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r s n1 n2 n3 n4 n5 r1 r2.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s n4
        /\ eval_ri_pre s n5 /\
      (~(eval_ri s n5 = (n2w 0)) ==> eval_ri s n5 = (n2w 1)) /\ ~(n1
        = n2) /\
      (single_sub_word (FAPPLY (word_bignumProof_state_regs s) n3)
        (eval_ri s n4) (eval_ri s n5) = (r1,r2)) ==>
      word_bignumProof_Eval r s (Sub n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r s n1 n2 n3 n4.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ n4 IN FDOM
        (word_bignumProof_state_regs s) /\ ~(n1 = n2) ==>
      word_bignumProof_Eval r s (Mul n1 n2 n3 n4)
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
      word_bignumProof_Eval r s (Div n1 n2 n3 n4 n5)
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
        (delete_vars vs (dec_clock s1))
        (word_bignum_LoopBody p) (INR s2) /\ ~(state_clock s1 = 0)
          ==>
      word_bignumProof_Eval r s1 (Loop rec vs p) (INR s2)) /\
   (!s1 save_regs vs p s2 s3.
      word_bignumProof_Eval (SOME p) (delete_vars vs (dec_clock s1))
        (word_bignum_LoopBody p) (INR s2) /\
      word_bignumProof_copy_vars save_regs
        (word_bignumProof_state_regs s1) s2 = SOME s3 /\ ~(state_clock
      s1 = 0) ==>
      word_bignumProof_Eval (SOME p) s1 (word_bignum_Rec save_regs
        vs) (INR s3)) /\
   (!r s1 p s2.
      word_bignumProof_Eval r s1 p (INR s2) ==>
      word_bignumProof_Eval r s1 (word_bignum_LoopBody p) (INR s2))
        /\
   (!r s1 s2 s3 p.
      word_bignumProof_Eval r s1 p (INL s2) /\ ~(state_clock s2 = 0)
        /\
      word_bignumProof_Eval r (dec_clock s2) (word_bignum_LoopBody p)
        (INR s3) ==>
      word_bignumProof_Eval r s1 (word_bignum_LoopBody p) (INR
        s3))`;;
hol4_overload "Eval" "word_bignumProof_Eval";;

(* HOL4 word_bignumProofScript.sml:158: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:160-177: ML code, not ported *)


(* verification of compiler to wordLang *)

let array_rel_def = cake_define
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

let code_subset_def = cake_define
  `code_subset (n1,cs1) (n2,cs2) <=>
     (!n v. ALOOKUP cs1 n = SOME v ==> ALOOKUP cs2 n = SOME v)`;;

let code_rel_def = cake_define
  `word_bignumProof_code_rel cs code <=>
     (!prog n p2.
        ALOOKUP (SND cs) prog = SOME (n,p2) ==>
        (?cs1 l2 i2 cs2.
          word_bignum_compile n 2 1 cs1 prog = (p2,l2,i2,cs2) /\
          sptree_lookup n code = SOME (1,Seq p2 (Return 0 [0])) /\
          code_subset cs2 cs))`;;
hol4_overload "code_rel" "word_bignumProof_code_rel";;

let div_code_assum_def = cake_define
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

let state_rel_def = cake_define
  `word_bignumProof_state_rel s (t:('a,'c,'ffi)wordSem_state) cs t0
  frame <=> state_clock
     s = state_clock t /\
     array_rel (word_bignumProof_state_arrays s) (FLOOKUP
       (wordSem_state_store t) TempIn1)
                        (FLOOKUP (wordSem_state_store t) TempIn2)
                        (FLOOKUP (wordSem_state_store t) TempOut)
                          (wordSem_state_memory t)
                          (wordSem_state_mdomain t) frame /\
     (!a v.
        FLOOKUP (word_bignumProof_state_regs s) a = SOME v ==>
        a < 25 /\
        FLOOKUP (wordSem_state_store t) (Temp (n2w a)) = SOME
          (wordLang_Word v)) /\
     word_bignumProof_code_rel cs (wordSem_state_code t) /\
     div_code_assum (:'ffi) (:'c) (wordSem_state_code t) /\
       ~(wordSem_state_termdep
     t = 0) /\ wordSem_state_gc_fun
     t0 = wordSem_state_gc_fun t /\ wordSem_state_handler
     t0 = wordSem_state_handler t /\ wordSem_state_termdep
     t0 = wordSem_state_termdep t /\ wordSem_state_code
     t0 = wordSem_state_code t /\ wordSem_state_be
     t0 = wordSem_state_be t /\ state_ffi
     t0 = state_ffi t /\ wordSem_state_compile
     t0 = wordSem_state_compile t /\ wordSem_state_compile_oracle
     t0 = wordSem_state_compile_oracle t /\ wordSem_state_code_buffer
     t0 = wordSem_state_code_buffer t /\ wordSem_state_data_buffer
     t0 = wordSem_state_data_buffer t /\ wordSem_state_stack_limit
     t0 = wordSem_state_stack_limit t /\ wordSem_state_stack_size
     t0 = wordSem_state_stack_size t /\
     FLOOKUP (wordSem_state_store t) TempOut = FLOOKUP
       (wordSem_state_store t0) TempOut /\
     (!n. (!r. ~(n = Temp r)) ==> FLOOKUP (wordSem_state_store t)
       n = FLOOKUP (wordSem_state_store t0) n)`;;
hol4_overload "state_rel" "word_bignumProof_state_rel";;

let exp_ok_def = cake_define
  `exp_ok x1 =
        match x1 with
          wordLang_Const _4 -> T
        | (Var i) -> i < (25)
        | (wordLang_Op _5 [x; y]) -> exp_ok x /\ exp_ok y
        | (Shift sh e n) -> exp_ok e
        | _6 -> F`;;

let syntax_ok_aux_def = cake_define
  `syntax_ok_aux x1 =
      match x1 with
        word_bignum_Loop r vs body -> syntax_ok_aux body
      | (word_bignum_LoopBody body) -> F
      | (Seq p1 p2) -> syntax_ok_aux p1 /\ syntax_ok_aux p2
      | (Assign t1 e) -> t1 < (25) /\ exp_ok e
      | (Load t1 t2 _7) -> t1 < (25) /\ t2 < (25)
      | (Store t1 t2) -> t1 < (25) /\ t2 < (25)
      | (If t1 t2 t3 p1 p2) ->
      t2 < (25) /\ (!r. t3 = Reg r ==> r < (25)) /\
      syntax_ok_aux p1 /\ syntax_ok_aux p2
      | (Add n1 n2 n3 n4 n5) ->
      n1 < (25) /\ n2 < (25) /\ n3 < (25) /\
      (!r. n4 = Reg r ==> r < (25)) /\
      (!r. n5 = Reg r ==> r < (25))
      | (Sub n1 n2 n3 n4 n5) ->
      n1 < (25) /\ n2 < (25) /\ n3 < (25) /\
      (!r. n4 = Reg r ==> r < (25)) /\
      (!r. n5 = Reg r ==> r < (25))
      | (Mul n1 n2 n3 n4) ->
      n1 < (25) /\ n2 < (25) /\
      n3 < (25) /\ n4 < (25)
      | (Div n1 n2 n3 n4 n5) ->
      n1 < (25) /\ n2 < (25) /\
      n3 < (25) /\ n4 < (25) /\ n5 < (25)
      | (word_bignum_Rec save_regs _8) ->
      EVERY (\n. n < (25)) save_regs /\ ALL_DISTINCT save_regs
      | _9 -> T`;;

let syntax_ok_def = cake_define
  `word_bignumProof_syntax_ok p =
      match p with
        word_bignum_LoopBody body -> syntax_ok_aux body
      | p -> syntax_ok_aux p`;;
hol4_overload "syntax_ok" "word_bignumProof_syntax_ok";;
(*Is this worth the hassle*)
let list_update_def = cake_define_list
  [`list_update [] ys t = t`;
   `list_update (x :: xs) (y :: ys) t = sptree_insert x y
  (list_update xs ys t)`;
   `list_update (x :: xs) [] t = sptree_insert x ARB (list_update
  xs [] t)`];;

let list_store_def = cake_define_list
  [`list_store [] ys s = s`;
   `list_store (x :: xs) ys s = (list_store xs (TL ys) s) |+ (Temp
  (n2w x),HD ys)`];;

(* HOL4 word_bignumProofScript.sml:677-680: ML code, not ported *)

let good_code_def = cake_define
  `word_bignumProof_good_code cs3 =
     (!prog n p2.
       MEM (prog,n,p2) (SND cs3) ==>
       (?cs1 l2' i2 cs2.
         word_bignum_compile n 2 1 cs1 prog = (p2,l2',i2,cs2) /\
           code_subset cs2 cs3))`;;
hol4_overload "good_code" "word_bignumProof_good_code";;


(* correctenss judgement *)

(* HOL4 word_bignumProofScript.sml:1335: ML code, not ported *)

let corr_def = cake_define
  `Corr prog (s:'a word_bignumProof_state) s1 p <=>
     (p ==> word_bignumProof_Eval NONE s prog s1)`;;

let loop_app_def = cake_define
  `loop_app f g x =
     (match f x with INL s -> (INL (dec_clock s),(g x /\
       ~(state_clock s = 0))) | INR s -> (INR s,g x))`;;

let tick_before_def = cake_define
  `tick_before vs f s =
     (if state_clock s = 0 then (s,F) else f (delete_vars vs
       (dec_clock s)))`;;

(* HOL4 word_bignumProofScript.sml:1514: ML code, not ported *)


(* derive Corr thm from AST *)

(* HOL4 word_bignumProofScript.sml:1618-1619: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1627: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1629-1640: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1642-1647: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1649-1650: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1652-1654: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1656: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1658-1659: ML code, not ported *)

(* order: clock then array then reg_write *)
(* HOL4 word_bignumProofScript.sml:1662-1684: a proof *)

(* HOL4 word_bignumProofScript.sml:1686-1690: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1692-1698: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1700-1713: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1715: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1717-1744: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1746-1748: code that the source
   has in a comment *)

(* HOL4 word_bignumProofScript.sml:1750-1773: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1781-1782: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1790-1791: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1799-1800: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1808-1809: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1811-1832: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:1834-1840: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1842-1849: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1851-1852: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1854-1856: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1902-1913: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1915-1926: ML code, not ported *)

(* HOL4 word_bignumProofScript.sml:1928-1937: the ML values that the
   definitions below antiquote *)

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

(* HOL4 word_bignumProofScript.sml:2135-2170: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2172-2186: the ML values that the
   definitions below antiquote *)

(* HOL4 word_bignumProofScript.sml:2188-2209: the ML values that the
   definitions below antiquote *)

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

(* HOL4 word_bignumProofScript.sml:2287: ML code, not ported *)
