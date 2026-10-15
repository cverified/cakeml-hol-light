(* ======================================================== *)
(*  word_bignumProof: ported from HOL4's
    compiler/backend/proofs/word_bignumProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for word_bignum
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/multiword.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
(* HOL4 ancestors outside the port: tailrec mc_multiword *)

(* HOL4 ML code, not ported:
val good_dimindex_def = miscTheory.good_dimindex_def;
val env_to_list_lookup_equiv = wordPropsTheory.env_to_list_lookup_equiv;
*)

(* HOL4 ML code, not ported:
val shift_def = backend_commonTheory.word_shift_def
*)


(* semantics of the little language *)

let word_bignumProof_state_FIELDS =
  define_record "word_bignumProof_state"
  ["regs","(num,'a word)fmap";
   "arrays","address->('a word) list";
   "clock","num"];;

let eval_exp_def = cake_define_list
  [`eval_exp s (wordLang_Const w) = w`;
   `eval_exp s (wordLang_Var v) = FAPPLY (word_bignumProof_state_regs
  s) v`;
   `eval_exp s (wordLang_Op Add [x1; x2]) = eval_exp s x1 + eval_exp
  s x2`;
   `eval_exp s (wordLang_Op Sub [x1; x2]) = eval_exp s x1 - eval_exp
  s x2`;
   `eval_exp s (wordLang_Op And [x1; x2]) = word_and (eval_exp s x1)
  (eval_exp s x2)`;
   `eval_exp s (wordLang_Op Or [x1; x2]) = word_or (eval_exp s x1)
  (eval_exp s x2)`;
   `eval_exp s (wordLang_Op Xor [x1; x2]) = word_xor (eval_exp s x1)
  (eval_exp s x2)`;
   `eval_exp s (wordLang_Shift Lsl x1 x2) = eval_exp s x1 << (w2n
  (eval_exp s x2))`;
   `eval_exp s (wordLang_Shift Asr x1 x2) = eval_exp s x1 >> (w2n
  (eval_exp s x2))`;
   `eval_exp s (wordLang_Shift Lsr x1 x2) = eval_exp s x1 >>> (w2n
  (eval_exp s x2))`;
   `eval_exp s (wordLang_Shift Ror x1 x2) = word_ror (eval_exp s x1)
  (w2n (eval_exp s x2))`];;

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
  [`eval_ri_pre s (Reg r) <=> eval_exp_pre (s:'a
  word_bignumProof_state) ((Var r):'a wordLang_exp)`;
   `eval_ri_pre s (Imm (w:'a word)) <=> T`];;

let eval_ri_def = cake_define_list
  [`eval_ri s (Reg r) = eval_exp s (Var r)`;
   `eval_ri s (Imm w) = w`];;

let dec_clock_def = cake_define
  `word_bignumProof_dec_clock s = ?_clock_fupd (K (?_clock s - 1)) s`;;

let reg_write_def = cake_define
  `reg_write v NONE (s:'a word_bignumProof_state) =
  word_bignumProof_state_regs_fupd (K (word_bignumProof_state_regs s \\
  v /\
   reg_write n (SOME v) s = word_bignumProof_state_regs_fupd (K
     (word_bignumProof_state_regs s |+ (n,v))) s)) s`;;

let delete_vars_def = cake_define_list
  [`delete_vars [] s = s`;
   `delete_vars (v :: vs) s = reg_write v NONE (delete_vars vs s)`];;

let array_write_def = cake_define
  `array_write n v s = word_bignumProof_state_arrays_fupd (K ((n =+
  v) (word_bignumProof_state_arrays s))) s`;;

let clock_write_def = cake_define
  `clock_write l s = ?_clock_fupd (K l) s`;;

let copy_vars_def = cake_define_list
  [`word_bignumProof_copy_vars [] s t = SOME t`;
   `word_bignumProof_copy_vars (n :: ns) s t =
         (match FLOOKUP s n with NONE -> NONE | SOME x ->
           word_bignumProof_copy_vars ns s (reg_write n (SOME x) t))`];;

let eval = cake_inductive
  `(!r s. ast_Eval r s Skip (INR (s:'a word_bignumProof_state))) /\
   (!r s. ast_Eval r s Continue (INL s)) /\
   (!r vs s. ast_Eval r s (word_bignum_Delete vs) (INR (delete_vars
     vs (s:'a word_bignumProof_state)))) /\
   (!r s x n.
      eval_exp_pre s x ==>
      ast_Eval r s (Assign n x) (INR (reg_write n (SOME (eval_exp s
        x)) s))) /\
   (!r s1 s2 s3 p1 p2.
      ast_Eval r s1 p1 (INR s2) /\ ast_Eval r s2 p2 s3 ==>
      ast_Eval r s1 (Seq p1 p2) s3) /\
   (!rec s1 c r ri p1 p2 s2.
      r IN FDOM (word_bignumProof_state_regs s1) /\ eval_ri_pre s1 ri
        /\
      ast_Eval rec s1 (if word_cmp c (eval_exp s1 (Var r)) (eval_ri
        s1 ri) then p1 else p2) s2 ==>
      ast_Eval rec s1 (If c r ri p1 p2) s2) /\
   (!rec s r i a w.
      (FLOOKUP (word_bignumProof_state_regs s) i = SOME w) /\
      w2n w < LENGTH (word_bignumProof_state_arrays s a) ==>
      ast_Eval rec s (Load r i a) (INR (reg_write r (SOME (EL (w2n w)
        (word_bignumProof_state_arrays s a))) s))) /\
   (!rec s r i w wr.
      (FLOOKUP (word_bignumProof_state_regs s) i = SOME w) /\
        (FLOOKUP (word_bignumProof_state_regs s) r = SOME wr) /\
      w2n w < LENGTH (word_bignumProof_state_arrays s Out) ==>
      ast_Eval rec s (Store r i) (INR (array_write Out (LUPDATE wr
        (w2n w) (word_bignumProof_state_arrays s Out)) s))) /\
   (!r s.
      ast_Eval r s word_bignum_Swap (INR (array_write In1
        (word_bignumProof_state_arrays s In2)
                       (array_write In2
                         (word_bignumProof_state_arrays s In1) s)))) /\
   (!r s r1 r2.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s n4
        /\ eval_ri_pre s n5 /\
      (~(eval_ri s n5 = (n2w 0)) ==> eval_ri s n5 = (n2w 1)) /\ ~(n1
        = n2) /\
      (single_add_word (FAPPLY (word_bignumProof_state_regs s) n3)
        (eval_ri s n4) (eval_ri s n5) = (r1,r2)) ==>
      ast_Eval r s (Add n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r s n1 n2 n3 n4 n5 r1 r2.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ eval_ri_pre s n4
        /\ eval_ri_pre s n5 /\
      (~(eval_ri s n5 = (n2w 0)) ==> eval_ri s n5 = (n2w 1)) /\ ~(n1
        = n2) /\
      (single_sub_word (FAPPLY (word_bignumProof_state_regs s) n3)
        (eval_ri s n4) (eval_ri s n5) = (r1,r2)) ==>
      ast_Eval r s (Sub n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME r1) (reg_write n2 (SOME r2) s)))) /\
   (!r s n1 n2 n3 n4.
      n3 IN FDOM (word_bignumProof_state_regs s) /\ n4 IN FDOM
        (word_bignumProof_state_regs s) /\ ~(n1 = n2) ==>
      ast_Eval r s (Mul n1 n2 n3 n4)
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
      ast_Eval r s (Div n1 n2 n3 n4 n5)
       (INR (reg_write n1 (SOME (FST (single_div (FAPPLY
         (word_bignumProof_state_regs s) n3) (FAPPLY
         (word_bignumProof_state_regs s) n4) (FAPPLY
         (word_bignumProof_state_regs s) n5))))
            (reg_write n2 (SOME (SND (single_div (FAPPLY
              (word_bignumProof_state_regs s) n3) (FAPPLY
              (word_bignumProof_state_regs s) n4) (FAPPLY
              (word_bignumProof_state_regs s) n5)))) s)))) /\
   (!r s1 p vs s2 rec.
      ast_Eval (if rec then SOME p else NONE) (delete_vars vs
        (word_bignumProof_dec_clock s1))
        (word_bignum_LoopBody p) (INR s2) /\ ~(?_clock s1 = 0) ==>
      ast_Eval r s1 (Loop rec vs p) (INR s2)) /\
   (!s1 save_regs vs p s2 s3.
      ast_Eval (SOME p) (delete_vars vs (word_bignumProof_dec_clock
        s1)) (word_bignum_LoopBody p) (INR s2) /\
      word_bignumProof_copy_vars save_regs
        (word_bignumProof_state_regs s1) s2 = SOME s3 /\ ~(?_clock
      s1 = 0) ==>
      ast_Eval (SOME p) s1 (word_bignum_Rec save_regs vs) (INR s3))
        /\
   (!r s1 p s2.
      ast_Eval r s1 p (INR s2) ==>
      ast_Eval r s1 (word_bignum_LoopBody p) (INR s2)) /\
   (!r s1 s2 s3 p.
      ast_Eval r s1 p (INL s2) /\ ~(?_clock s2 = 0) /\
      ast_Eval r (word_bignumProof_dec_clock s2)
        (word_bignum_LoopBody p) (INR s3) ==>
      ast_Eval r s1 (word_bignum_LoopBody p) (INR s3))`;;

(* HOL4 ML code, not ported:
val raw_eval_cases = eval_cases;
*)

(* HOL4 ML code, not ported:
val eval_cases =
  map (SIMP_CONV (srw_ss()) [Once raw_eval_cases])
    [``Eval rec s1 Skip s2``,
     ``Eval rec s1 Continue s2``,
     ``Eval rec s1 (Delete vs) s2``,
     ``Eval rec s1 (Seq p1 p2) s2``,
     ``Eval rec s1 (Assign n x) s2``,
     ``Eval rec s1 (If c r ri p1 p2) s2``,
     ``Eval rec s1 (Load r i a) s2``,
     ``Eval rec s1 (Store r i) s2``,
     ``Eval rec s1 Swap s2``,
     ``Eval rec s1 (Add r1 r2 r3 r4 r5) s2``,
     ``Eval rec s1 (Sub r1 r2 r3 r4 r5) s2``,
     ``Eval rec s1 (Mul r1 r2 r3 r4) s2``,
     ``Eval rec s1 (Div r1 r2 r3 r4 r5) s2``,
     ``Eval rec s1 (Rec save_regs vs) s2``,
     ``Eval rec s1 (Loop r vs p) s2``,
     ``Eval rec s1 (LoopBody p) s2``] |> LIST_CONJ;
*)


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

let div_code_assum_def = cake_define
  `div_code_assum (:'ffi) (:'c) code =
     (!(t1:('a,'c,'ffi)wordSem_state) n l i0 i1 i2 i3 i4 w3 w4 w5
       ret_val.
       0 < i0 /\ 0 < i1 /\ 0 < i2 /\ 0 < i3 /\ 0 < i4 /\
       ALL_DISTINCT [i0; i1; i2; i3; i4] /\ wordSem_state_code
       t1 = code /\ ~(wordSem_state_termdep t1 = 0) /\
       get_var 0 t1 = SOME ret_val /\ single_div_pre w3 w4 w5 ==>
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
             (set_var 0 ret_val o set_var i1 (wordLang_Word w2) o
              set_var i0 (wordLang_Word w1) o set_store (Temp (n2w
                28)) (wordLang_Word w2)) (
             wordSem_state_stack_max_fupd (K max')
               (wordSem_state_locals_fupd (K LN)
               (wordSem_state_permute_fupd (K (\n.
               wordSem_state_permute t1 (n + 1))) t1)))))))`;;

(* HOL4 overload (expanded in the port):
     max_var_name = 25n *)

let state_rel_def = cake_define
  `word_bignumProof_state_rel s (t:('a,'c,'ffi)wordSem_state) cs t0
  frame <=> ?_clock
     s = ?_clock t /\
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
     t0 = wordSem_state_be t /\ ?_ffi
     t0 = ?_ffi t /\ wordSem_state_compile
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

let exp_ok_def = cake_define
  `exp_ok x1 =
        match x1 with
          wordLang_Const _3 -> T
        | (Var i) -> i < (25)
        | (wordLang_Op _4 [x; y]) -> exp_ok x /\ exp_ok y
        | (Shift sh e n) -> exp_ok e
        | _5 -> F`;;

let syntax_ok_aux_def = cake_define
  `syntax_ok_aux x1 =
      match x1 with
        word_bignum_Loop r vs body -> syntax_ok_aux body
      | (word_bignum_LoopBody body) -> F
      | (Seq p1 p2) -> syntax_ok_aux p1 /\ syntax_ok_aux p2
      | (Assign t1 e) -> t1 < (25) /\ exp_ok e
      | (Load t1 t2 _6) -> t1 < (25) /\ t2 < (25)
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
      | (word_bignum_Rec save_regs _7) ->
      EVERY (\n. n < (25)) save_regs /\ ALL_DISTINCT save_regs
      | _8 -> T`;;

let syntax_ok_def = cake_define
  `syntax_ok p =
      match p with
        word_bignum_LoopBody body -> syntax_ok_aux body
      | p -> syntax_ok_aux p`;;
(*Is this worth the hassle*)
let list_update_def = cake_define_list
  [`list_update [] ys t = t`;
   `list_update (x :: xs) (y :: ys) t = sptree_insert x y
  (list_update xs ys t)`;
   `list_update (x :: xs) [] t = sptree_insert x ARB (list_update xs
  [] t)`];;

let list_store_def = cake_define_list
  [`list_store [] ys s = s`;
   `list_store (x :: xs) ys s = (list_store xs (TL ys) s) |+ (Temp
  (n2w x),HD ys)`];;

(* HOL4 ML code, not ported:
fun uncurry_case_rand x = x
                         |> TypeBase.case_rand_of
                         |> ISPEC ``(UNCURRY (A:'uniquea -> 'uniqueb ->
                           'uniquec))``
                         |> GEN ``(A:'uniquea -> 'uniqueb ->
                           'uniquec)``;
*)

let good_code_def = cake_define
  `word_bignumProof_good_code cs3 =
     (!prog n p2.
       MEM (prog,n,p2) (SND cs3) ==>
       (?cs1 l2' i2 cs2.
         word_bignum_compile n 2 1 cs1 prog = (p2,l2',i2,cs2) /\
           code_subset cs2 cs3))`;;


(* correctenss judgement *)

(* HOL4 ML code, not ported:
val all_corrs = ref (tl [TRUTH]);
*)

let corr_def = cake_define
  `Corr prog (s:'a word_bignumProof_state) s1 p <=>
     (p ==> ast_Eval NONE s prog s1)`;;

let loop_app_def = cake_define
  `loop_app f g x =
     (match f x with INL s -> (INL (word_bignumProof_dec_clock
       s),(g x /\ ~(?_clock s = 0))) | INR s -> (INR s,g x))`;;

let tick_before_def = cake_define
  `tick_before vs f s =
     (if ?_clock s = 0 then (s,F) else f (delete_vars vs
       (word_bignumProof_dec_clock s)))`;;

(* HOL4 ML code, not ported:
val Corr_Loop = MATCH_MP Corr_Loop_lemma (Corr_LoopBody |> UNDISCH) |>
  DISCH_ALL;
*)


(* derive Corr thm from AST *)

(* HOL4 ML code, not ported:
val write_simps = LIST_CONJ [array_write_simp, reg_write_simp,
  dec_clock_write_simp, clock_write_simp]
*)

(* HOL4 ML code, not ported:
val s_var = Corr_def |> concl |> dest_forall |> snd |> dest_forall |>
  fst
*)

(* HOL4 ML code, not ported:
fun find_ret_tuple tm =
  if is_var tm then
    tm
  else if pairSyntax.is_pair tm then
    tm
  else if is_let tm then
    pairSyntax.dest_anylet tm |> snd |> find_ret_tuple
  else if is_cond tm then let
    val (_,x1,x2) = dest_cond tm
    in find_ret_tuple x1 handle HOL_ERR _ =>
       find_ret_tuple x2 end
  else fail()
*)

(* HOL4 ML code, not ported:
fun get_array_name a = let
  val a = a |> dest_var |> fst
  val a = if a = "xs" then ``In1`` else
          if a = "ys" then ``In2`` else
          if a = "zs" then ``Out`` else fail()
  in a end
*)

(* HOL4 ML code, not ported:
fun get_pat th =
  th |> SPEC_ALL |> UNDISCH_ALL |> concl |> rator |> rator |> rator |>
    rand;
*)

(* HOL4 ML code, not ported:
fun D th = let
  val th1 = th |> DISCH_ALL |> PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM
    CONJ_ASSOC]
  in if th1 |> concl |> is_imp then th1 else DISCH T th end
*)

(* HOL4 ML code, not ported:
val const_def = el 1 (all_code_defs |> CONJUNCTS |> rev)
*)

(* HOL4 ML code, not ported:
val simp_var_assums_conv =
  SIMP_CONV (srw_ss()) [FLOOKUP_UPDATE,APPLY_UPDATE_THM]
*)

(* order: clock then array then reg_write *)
(* HOL4 ML code, not ported:
val sort_lemma = prove(
  ``(clock_write l1 (clock_write l2 s) = clock_write l1 s) /\
*)
    (* array_write move inwards *)
(* HOL4 ML code, not ported:
    (array_write a1 x1 (clock_write l s) = clock_write l (array_write a1
      x1 s)) /\
    (array_write a1 x1 (array_write a1 x2 s) = array_write a1 x1 s) /\
    (array_write In2 x1 (array_write In1 x2 s) =
     array_write In1 x2 (array_write In2 x1 s)) /\
    (array_write Out x1 (array_write In1 x2 s) =
     array_write In1 x2 (array_write Out x1 s)) /\
    (array_write Out x1 (array_write In2 x2 s) =
     array_write In2 x2 (array_write Out x1 s)) /\
*)
    (* reg_write move inwards *)
(* HOL4 ML code, not ported:
    (n2 < n1 ==>
     reg_write n1 w1 (reg_write n2 w2 s) = reg_write n2 w2 (reg_write n1
       w1 s)) /\
    (reg_write n1 w1 (reg_write n1 w2 s) = reg_write n1 w1 s) /\
    (reg_write n1 w1 (clock_write l s) = clock_write l (reg_write n1 w1
      s)) /\
    (reg_write n1 w1 (array_write a1 x1 s) = array_write a1 x1
      (reg_write n1 w1 s))``,
  Cases_on `w1`
  \\ Cases_on `w2`
  \\ rw
    [state_eq_lemma,EXTENSION,FAPPLY_FUPDATE_THM,array_write_def
    ,clock_write_def]
  \\ TRY eq_tac \\ rw [] \\ CCONTR_TAC \\ fs [DOMSUB_FAPPLY_THM]
  \\ rfs [FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
  \\ rpt (pop_assum mp_tac) \\ rw []) |> CONJUNCTS |> map GEN_ALL |>
    LIST_CONJ;
*)

(* HOL4 ML code, not ported:
val reg_write_pat = ``reg_write n v s``
val clock_write_pat = clock_write_def |> SPEC_ALL |> concl |> lhs
val array_write_pat = array_write_def |> SPEC_ALL |> concl |> lhs
val dec_clock_pat = dec_clock_def |> SPEC_ALL |> concl |> lhs
val delete_vars_pat = ``delete_vars vs s``
*)

(* HOL4 ML code, not ported:
local val s = HolKernel.syntax_fns2 "word_bignumProof" in
  val (clock_write_tm,mk_clock_write,dest_clock_write,is_clock_write) =
    s "clock_write"
end
local val s = HolKernel.syntax_fns3 "word_bignumProof" in
  val (reg_write_tm,mk_reg_write,dest_reg_write,is_reg_write) = s
    "reg_write"
  val (array_write_tm,mk_array_write,dest_array_write,is_array_write) =
    s "array_write"
end
*)

(* HOL4 ML code, not ported:
val sort_thms = let
  val xs = sort_lemma |> CONJUNCTS |> map SPEC_ALL
  val x = first (is_imp o concl) xs
  fun up_to 0 = []
    | up_to n = n-1 :: up_to (n-1)
  fun pairs 0 = []
    | pairs n = map (fn m => (n-1,m)) (up_to (n-1)) @ pairs (n-1)
  fun f (n1,n2) =
    x |> INST [``n1:num``|->numSyntax.term_of_int n1,
               ``n2:num``|->numSyntax.term_of_int n2]
      |> SIMP_RULE std_ss []
  val ys = filter (not o is_imp o concl) xs @
             map f (pairs 23) (* all variables have names < 23 *)
  in ys end
*)

(* HOL4 ML code, not ported:
val all_goals = ref (tl [T]);
*)

(* HOL4 ML code, not ported:
val sort_writes_conv = let
  val raw_sort_conv = QCONV (REWRITE_CONV sort_thms)
  val cc = REWRITE_CONV [delete_vars_def,dec_clock_thm,write_simps]
  fun do_it_conv tm = let
    fun dest_writes tm =
      let
        val (l,s) = dest_clock_write tm
      in rator (mk_clock_write(genvar(type_of l),s_var)) :: dest_writes
        s end
      handle HOL_ERR _ =>
      let
        val (a,x,s) = dest_array_write tm
      in rator (mk_array_write(a,genvar(type_of x),s_var)) ::
        dest_writes s end
      handle HOL_ERR _ =>
      let
        val (a,x,s) = dest_reg_write tm
      in rator (mk_reg_write(a,genvar(type_of x),s_var)) :: dest_writes
        s end
      handle HOL_ERR _ => []
    val xs = dest_writes tm
    fun make_term [] = s_var
      | make_term (x::xs) = mk_comb(x,make_term xs)
    val lemma = raw_sort_conv (make_term xs)
    in REWR_CONV lemma tm end
  fun is_inl_inr_conv tm =
    if can (match_term reg_write_pat) tm
       orelse can (match_term clock_write_pat) tm
       orelse can (match_term array_write_pat) tm
    then ALL_CONV tm else NO_CONV tm
  in cc THENC ONCE_DEPTH_CONV (is_inl_inr_conv THENC do_it_conv) end
*)

(*
val th = (Corr_Skip |> INST [s_var |-> ret_tm])
*)

(* HOL4 ML code, not ported:
fun remove_write_from_init th = let
  val tm = concl th |> rator |> rator |> rand
  val del_pat = ``delete_vars vs ^s_var``
  val xs = find_terms (can (match_term del_pat)) tm |> map (rand o
    rator)
             |> map (fst o listSyntax.dest_list) |> Lib.flatten
  val del_assums = map (fn tm => ``~(^tm IN FDOM ^s_var.regs)``) xs
  val reg_pat = reg_write_def |> CONJUNCT2 |> SPEC_ALL |> concl |> lhs
    |> rator
  val xs = find_terms (can (match_term reg_pat)) tm
  val reg_assums =
    map (fn tm => ``FLOOKUP s.regs ^(tm |> rator |> rand) = ^(tm |>
      rand)``) xs
  val clock_pat = clock_write_def |> SPEC_ALL |> concl |> lhs |> rator
  val xs = find_terms (can (match_term clock_pat)) tm
  val clock_assums = map (fn tm => ``^(s_var).clock = ^(tm |> rand)``)
    xs
  val array_pat = array_write_def |> SPEC_ALL |> concl |> lhs |> rator
  val xs = find_terms (can (match_term array_pat)) tm
  val array_assums =
    map (fn tm => ``s.arrays ^(tm |> rator |> rand) = ^(tm |> rand)``)
      xs
  val goal = foldr mk_imp (mk_eq(tm,s_var)) (array_assums @ del_assums @
                reg_assums @ clock_assums)
  val lemma = prove(``^goal``,
    CONV_TAC sort_writes_conv
    \\ rw [] \\ fs [FLOOKUP_DEF] \\ rw []
    \\ fs [state_eq_lemma,clock_write_def]) |> UNDISCH_ALL
  in th |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV) (REWR_CONV
    lemma)) end
*)

(* HOL4 ML code, not ported:
val reg_read_lemma1_pat =
  reg_read_lemma1 |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs
*)

(* HOL4 ML code, not ported:
val reg_read_lemma2_pat =
  reg_read_lemma2 |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs
*)

(* HOL4 ML code, not ported:
val array_read_lemma_pat =
  array_read_lemma |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs
*)

(* HOL4 ML code, not ported:
val clock_read_lemma_pat =
  clock_read_lemma |> SPEC_ALL |> concl |> dest_imp |> snd |> lhs
*)

(* HOL4 ML code, not ported:
fun read_conv tm =
  if can (match_term reg_read_lemma1_pat) tm then let
    val n = tm |> rator |> rand
    val nn = "r" ^ int_to_string (numSyntax.int_of_term n)
    val lemma = reg_read_lemma1 |> SPECL [mk_var(nn,``:'a word``), n]
    in UNDISCH lemma end
  else if can (match_term reg_read_lemma2_pat) tm then let
    val n = tm |> rand
    val nn = "r" ^ int_to_string (numSyntax.int_of_term n)
    val lemma = reg_read_lemma2 |> SPECL [mk_var(nn,``:'a word``), n]
    in UNDISCH lemma end
  else if can (match_term clock_read_lemma_pat) tm then let
    val lemma = clock_read_lemma
    in UNDISCH lemma end
  else if can (match_term array_read_lemma_pat) tm then let
    val n = tm |> rand
    val nn = dest_const n |> fst
    val nn = if nn = "In1" then "xs" else
             if nn = "In2" then "ys" else "zs"
    val lemma = array_read_lemma |> SPECL [mk_var(nn,type_of tm), n]
    in UNDISCH lemma end
  else NO_CONV tm
*)

(* HOL4 ML code, not ported:
fun make_new_vars th = let
  val vs = D th |> concl |> free_vars
  fun f v =
    if v ~~ s_var then s_var |-> s_var else let
      val (n,ty) = dest_var v
      in v |-> mk_var("new_" ^ n,ty) end
  in INST (map f vs) th end
*)

(* HOL4 ML code, not ported:
fun remove_new_vars th = let
  val vs = D th |> concl |> free_vars
  fun f v = let
    val (n,ty) = dest_var v
    in if String.isPrefix "new_" n then
         v |-> mk_var(String.substring(n,4,size(n)-4),ty)
       else v |-> v end
  in INST (map f vs) th end
*)

(* HOL4 ML code, not ported:
fun let_intro_conv v =
   UNBETA_CONV v THENC REWR_CONV (GSYM LET_THM);
*)

(* HOL4 ML code, not ported:
fun list_let_intro_conv [] = ALL_CONV
  | list_let_intro_conv (v::vs) =
      let_intro_conv v THENC list_let_intro_conv vs
*)

(* HOL4 ML code, not ported:
fun first_let_if_conv c tm =
  if is_cond tm then
    (RATOR_CONV o RATOR_CONV o RAND_CONV) c tm
  else if can pairSyntax.dest_anylet tm then
    (RAND_CONV) c tm
  else if is_var tm then ALL_CONV tm
  else if is_const tm then ALL_CONV tm
  else if is_abs tm then ABS_CONV (first_let_if_conv c) tm
  else if is_comb tm then
    (RATOR_CONV (first_let_if_conv c) THENC
     RAND_CONV (first_let_if_conv c)) tm
  else ALL_CONV tm
*)

(* HOL4 ML code, not ported:
local val s = HolKernel.syntax_fns1 "word_bignum" in
  val (Delete_tm,mk_Delete,dest_Delete,is_Delete) = s "Delete"
end
local val s = HolKernel.syntax_fns2 "word_bignum" in
  val (Assign_tm,mk_Assign,dest_Assign,is_Assign) = s "Assign"
  val (Seq_tm,mk_Seq,dest_Seq,is_Seq) = s "Seq"
  val (Store_tm,mk_Store,dest_Store,is_Store) = s "Store"
end
local val s = HolKernel.syntax_fns3 "word_bignum" in
  val (Loop_tm,mk_Loop,dest_Loop,is_Loop) = s "Loop"
  val (Load_tm,mk_Load,dest_Load,is_Load) = s "Load"
end
*)

(* HOL4 ML code, not ported:
local
  val word_ty = ``:'a word``
in
  fun dest_reg v = let
    val (n,ty) = dest_var v
    val _ = ty = word_ty orelse fail()
    val n = String.substring(n,1,String.size(n)-1) |> string_to_int
    val n = numSyntax.term_of_int n
    in n end handle Subscript => fail()
end;
*)

(* HOL4 ML code, not ported:
val Skip_tm = ``Skip:'a word_bignum$mini``
val Swap_tm = ``Swap:'a word_bignum$mini``
val Continue_tm = ``Continue:'a word_bignum$mini``
*)

(* HOL4 ML code, not ported:
val If_pat = ``word_bignum$If c r (ri:'a reg_imm) p1 p2``
fun dest_If tm = let
  val i = fst (match_term If_pat tm)
  fun list_dest f tm = let
    val (x,y) = f tm
    in list_dest f x @ list_dest f y end handle HOL_ERR _ => [tm]
  val ts = list_dest dest_comb If_pat
  in (subst i (el 2 ts),
      subst i (el 3 ts),
      subst i (el 4 ts),
      subst i (el 5 ts),
      subst i (el 6 ts)) end
fun mk_If (c,r,ri,p1,p2) = ``word_bignum$If ^c ^r ^ri ^p1 ^p2``;
fun is_If tm = can dest_If tm
*)

(* val _ = diminish_srw_ss ["LET"]; *)

(* HOL4 ML code, not ported:
fun derive_corr_thm const_def = let
*)

  (* look up definitions *)
(* HOL4 ML code, not ported:
  val (r,l) = const_def |> concl |> dest_eq
  val name = r |> dest_const |> fst
  val name = String.substring(name,0,size(name)-5)
  val def = fetch "mc_multiword" (name ^ "_def")
  val pre_def = fetch "mc_multiword" (name ^ "_pre_def")
  val def_tail = fetch "mc_multiword" (name)
  val pre_tail = fetch "mc_multiword" (name ^ "_pre")
  val _ = print ("derive_corr_thm " ^ name ^ " \t")
*)
  (* compute ret and cont Corr thms *)
(* HOL4 ML code, not ported:
  val inp = def |> concl |> lhs |> rand
  val out = find_ret_tuple (def |> concl |> rhs)
  val is = helperLib.list_dest pairSyntax.dest_pair inp
  val os = helperLib.list_dest pairSyntax.dest_pair out
  fun add_all_writes ws dels tm = let
    val vs = map (fn v => dest_reg v handle HOL_ERR _ => s_var) ws
    fun add_extra_writes tm = mk_comb(``(delete_vars ^dels):α state -> α
      state``,tm)
    fun add_writes [] tm = tm
      | add_writes (v::vs) tm = let
          val n = dest_reg v
          in add_writes vs (``reg_write ^n (SOME ^v) ^tm``) end
        handle HOL_ERR _ => let
          val _ = type_of v = ``:num`` orelse fail()
          in add_writes vs (``clock_write ^v ^tm``) end
        handle HOL_ERR _ => let
          val n = get_array_name v
          in add_writes vs (``array_write ^n ^v ^tm``) end
        handle HOL_ERR _ => failwith("add_writes should not break")
    in add_extra_writes (add_writes ws tm) end
  val del_pat = ``Seq (Delete vs) Skip:'a mini``
  val dels = find_term (can (match_term del_pat)) l |> rator |> rand |>
    rand
             handle HOL_ERR _ => ``[]:num list``
  val ret_tm = add_all_writes (rev os) dels s_var
  val del_pat = ``Seq (Delete vs) Continue:'a mini``
  val dels = find_term (can (match_term del_pat)) l |> rator |> rand |>
    rand
             handle HOL_ERR _ => ``[]:num list``
  val cont_tm = add_all_writes (rev is) dels s_var
  val skip_thm = remove_write_from_init (Corr_Skip |> INST [s_var |->
    ret_tm])
  val cont_thm = remove_write_from_init (Corr_Continue |> INST [s_var
    |-> cont_tm])
  fun close_corr th = let
      val th = th |> DISCH_ALL |> REWRITE_RULE [flookup_thm,GSYM
        AND_IMP_INTRO]
                  |> UNDISCH_ALL
      val ss = filter (can dest_eq) (hyp th)
      val th = INST (map (fn tm => rhs tm |-> lhs tm) ss) th
      val th = th |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
      val th = th |> REWRITE_RULE [Corr_move_pre]
      in th end
*)

(* HOL4 ML code, not ported:
  fun get_corr tm =
    if tm ~~ Skip_tm then skip_thm else
    if tm ~~ Continue_tm then cont_thm else
    if is_If tm then let
      val i = fst (match_term (get_pat Corr_If) tm)
      val p1 = get_corr (tm |> rator |> rand)
      val p2 = get_corr (tm |> rand)
      val th = REWRITE_RULE
        [eval_exp_def,eval_exp_pre_def,asmTheory.word_cmp_def,
                 eval_ri_pre_def,eval_ri_def] (INST i Corr_If)
               |> CONV_RULE (DEPTH_CONV read_conv) |> REWRITE_RULE []
      in MATCH_MP th (CONJ p1 p2) end
    else if is_Seq tm then let
      val (p1,p2) = dest_Seq tm
      val th2 = get_corr p2
      val th2 = th2 |> D |> INST [s_var |-> mk_var("t",type_of s_var)]
      val lemmas = [Corr_Assign,Corr_Delete,
                    Corr_Load,Corr_Store,Corr_Swap,
                    Corr_Add,Corr_Sub,Corr_Mul,Corr_Div] @ (!all_corrs)
      val lemma = first (fn th => can (match_term (get_pat th)) p1)
        lemmas
      val i = fst (match_term (get_pat lemma) p1)
      val th1 = REWRITE_RULE [eval_exp_def,eval_exp_pre_def,
                  eval_ri_pre_def,eval_ri_def] (INST i lemma)
      val th1 = CONV_RULE (DEPTH_CONV read_conv) th1
      val th1 = make_new_vars th1
      val th = MATCH_MP (MATCH_MP Corr_Seq_alt th2) th1 |> REWRITE_RULE
        []
      val th = th |> CONV_RULE ((RATOR_CONV o RAND_CONV)
        simp_var_assums_conv)
      val th = th |> PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] |>
        UNDISCH_ALL
      val th = CONV_RULE sort_writes_conv th
      val ss = filter (fn tm => not (tmem s_var (free_vars (lhs tm))))
        (hyp th)
      val cc = list_let_intro_conv (map rhs ss)
      val th = th |> CONV_RULE (RAND_CONV cc THENC (RATOR_CONV o
        RAND_CONV) cc)
      val th = INST (map (fn tm => rhs tm |-> lhs tm) ss) th
      val th = DISCH_ALL th |> REWRITE_RULE [] |> UNDISCH_ALL
      val th = remove_new_vars th
      in th end
    else if can (match_term (get_pat Corr_Loop)) tm then let
      val i = fst (match_term (get_pat Corr_Loop) tm)
      val th = get_corr (tm |> rand)
      val th = th |> DISCH_ALL |> REWRITE_RULE [flookup_thm,GSYM
        AND_IMP_INTRO]
                  |> UNDISCH_ALL
      val ss = filter (can dest_eq) (hyp th)
      val th = INST (map (fn tm => rhs tm |-> lhs tm) ss) th
      val th = th |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO]
      val th = th |> REWRITE_RULE [Corr_move_pre]
      val th = th |> CONV_RULE
        (RAND_CONV (UNBETA_CONV s_var) THENC
         (RATOR_CONV o RAND_CONV) (UNBETA_CONV s_var)) |> GEN s_var
      in MATCH_MP Corr_Loop th |> INST i end
    else fail ()
*)

(* HOL4 ML code, not ported:
  val raw_thm = get_corr l |> REWRITE_RULE [GSYM const_def] |>
    close_corr
  val LOOP_pat = loop_app_def |> SPEC_ALL |> concl |> lhs |> rator
  val r1 = raw_thm |> concl |> rator |> rand
  val r2 = raw_thm |> concl |> rand
  val (r1,is_rec) = (find_term (can (match_term LOOP_pat)) r1 |> rator
    |> rand, true)
                    handle HOL_ERR _ => (r1, false)
  val (r2,is_rec) = (find_term (can (match_term LOOP_pat)) r2 |> rand,
    true)
                    handle HOL_ERR _ => (r2, false)
  val v = mk_var(name ^ "_raw", type_of (mk_abs(s_var,r1)))
  val raw_def = new_definition(dest_var v |> fst,
    mk_eq(mk_comb(v,s_var),r1))
  val v = mk_var(name ^ "_raw_pre", type_of (mk_abs(s_var,r2)))
  val raw_pre_def = new_definition(dest_var v |> fst,
    mk_eq(mk_comb(v,s_var),r2))
  val corr = raw_thm |> REWRITE_RULE [GSYM raw_def,GSYM raw_pre_def]
*)
  (* -- *)
(* HOL4 ML code, not ported:
  val inp = def |> concl |> lhs |> rand
  val out = find_ret_tuple (def |> concl |> rhs)
  val is = helperLib.list_dest pairSyntax.dest_pair inp
  val os = helperLib.list_dest pairSyntax.dest_pair out
  fun add_pres [] tm = tm
    | add_pres (v::vs) tm = let
          val n = dest_reg v
          in add_pres vs (mk_conj(``^n IN FDOM ^(s_var).regs``,tm)) end
        handle HOL_ERR _ => add_pres vs tm
  val pre_tm = add_pres (rev is) (pre_def |> concl |> lhs)
  val pre_tm = if is_rec then mk_conj(pre_tm,``(^s_var).clock <> 0``)
    else pre_tm
  val del_pat = ``Seq (Delete vs) Skip:'a mini``
  val dels = find_term (can (match_term del_pat)) l |> rator |> rand |>
    rand
             handle HOL_ERR _ => ``[]:num list``
  val cont_del_pat = ``Seq (Delete vs) Continue:'a mini``
  val cont_dels = find_term (can (match_term cont_del_pat)) l |> rator
    |> rand |> rand
                  handle HOL_ERR _ => ``[]:num list``
  val num_pair_pat = ``(n:num,w:'a word)``
  val reg_write_pat = ``reg_write n (w:'a word option):α state -> α
    state``
  fun add_all_writes ws dels tm = let
    val vs = map (fn v => dest_reg v handle HOL_ERR _ => s_var) ws
    fun add_extra_writes tm = mk_comb(``(delete_vars ^dels):α state -> α
      state``,tm)
    fun add_writes [] tm = tm
      | add_writes (v::vs) tm = let
          val n = dest_reg v
          in add_writes vs (``reg_write ^n (SOME ^v) ^tm``) end
        handle HOL_ERR _ => let
          val _ = type_of v = ``:num`` orelse fail()
          in add_writes vs (``clock_write ^v ^tm``) end
        handle HOL_ERR _ => let
          val n = get_array_name v
          in add_writes vs (``array_write ^n ^v ^tm``) end
        handle HOL_ERR _ => failwith("add_writes should not break")
    in add_extra_writes (add_writes ws tm) end
  val new_state =
    pairSyntax.mk_anylet ([(out,def |> concl |> lhs)],
      add_all_writes (rev os) dels s_var)
  fun let_inp [] tm = tm
    | let_inp (v::vs) tm = let
          val n = dest_reg v
          val tm = ``let ^v = (^s_var).regs ' ^n in ^tm``
          in let_inp vs tm end
        handle HOL_ERR _ => let
          val n = get_array_name v
          val tm = ``let ^v = (^s_var).arrays ^n in ^tm``
          in let_inp vs tm end
        handle HOL_ERR _ => let
          val _ = type_of v = ``:num`` orelse fail()
          val tm = ``let ^v = (^s_var).clock in ^tm``
          in let_inp vs tm end
        handle HOL_ERR _ => failwith("let_inp should not fail")
  val ii = if is_rec then subst [``l:num``|->``l-1n``] else I
  val new_post = let_inp (rev is) (ii new_state)
  val new_pre = let_inp (rev is) (ii pre_tm)
  val th = MATCH_MP Corr_STRENGTHEN_TERM corr |> SPECL
    [new_post,new_pre]
  val goal = th |> concl |> dest_imp |> fst
*)

(*
  max_print_depth := 15
*)

(* HOL4 ML code, not ported:
  in
    if not is_rec then let
      val lemma = prove(``^goal``,
        CONV_TAC sort_writes_conv
        \\ full_simp_tac std_ss [def] \\ rw []
        \\ REV_FULL_SIMP_TAC std_ss [pre_def,LET_THM]
        \\ full_simp_tac std_ss [LET_THM]
        \\ REV_FULL_SIMP_TAC std_ss [pre_def,LET_THM]
        \\ rpt (pairarg_tac \\ FULL_SIMP_TAC std_ss [] \\
          every_case_tac)
        \\ full_simp_tac std_ss [LET_THM] \\ rveq
        \\ REV_FULL_SIMP_TAC std_ss []
        \\ rpt (pairarg_tac \\ FULL_SIMP_TAC std_ss [] \\
          every_case_tac)
        \\ asm_rewrite_tac
          [raw_def,INL_11,INR_11,delete_vars_def,raw_pre_def]
        \\ rpt (pop_assum mp_tac)
        \\ rpt (CHANGED_TAC
             (CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM
                    ,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss []
              \\ CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM
                    ,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss [Once LET_THM]))
        \\ fs [] \\ rw []
        \\ TRY (CHANGED_TAC (simp[oneline SND]) \\ TOP_CASE_TAC \\ fs[])
        \\ imp_res_tac single_add_word_imp_0_1
        \\ rw [] \\ TRY eq_tac \\ rw [] \\ fs [true_pres]
        \\ CONV_TAC sort_writes_conv \\ fs []
        \\ CONV_TAC sort_writes_conv \\ fs [true_pres])
      val raw_th = MP th lemma |> SIMP_RULE std_ss [LET_THM]
      val th = raw_th |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV
        THENC
                                    sort_writes_conv)
      val _ = save_thm(name ^ "_corr_thm", raw_th)
      val _ = (all_corrs := th::(!all_corrs))
      in (def,raw_th) end
    else let
*)

(* HOL4 ML code, not ported:
      val tm = add_all_writes (rev is) cont_dels ``s0:'a state``
      val r = pairSyntax.mk_pabs(inp,``\s. s = ^tm``)
      val tm = add_all_writes (rev os) dels ``s0:'a state``
      val p = pairSyntax.mk_pabs(out,``\s. s = ^tm``)
      val loop_app_tm = loop_app_def
        |> ISPEC (raw_def |> SPEC_ALL |> concl |> lhs)
        |> ISPEC (raw_pre_def |> SPEC_ALL |> concl |> lhs)
        |> SPEC_ALL |> concl |> lhs |> rator
      val th1 =
        SHORT_TAILREC_SIM
        |> ISPEC (def_tail |> concl |> rand |> rand)
        |> REWRITE_RULE [GSYM def_tail, GSYM pre_tail]
        |> ISPEC loop_app_tm |> SIMP_RULE std_ss
          [loop_app_EQ,PULL_EXISTS]
        |> SPEC r |> SPEC p
      val goal1 = th1 |> concl |> dest_imp |> fst
*)

(* HOL4 ML code, not ported:
      val lemma1 = prove(``^goal1``,
        CONV_TAC sort_writes_conv
        \\ strip_tac \\ TRY (PairCases_on `x`) \\ fs [loop_app_EQ]
        \\ rpt (pairarg_tac \\ full_simp_tac std_ss []) \\ rveq
        \\ rpt TOP_CASE_TAC \\ rveq
        \\ simp_tac std_ss []
        \\ rewrite_tac
          [raw_def,raw_pre_def,delete_vars_def,dec_clock_thm]
        \\ simp_tac std_ss
          [PULL_EXISTS,write_simps,FDOM_FUPDATE,IN_INSERT,
                DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM
                  ,true_pres]
        \\ rpt (CHANGED_TAC
             (CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM
                    ,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss []
              \\ CONV_TAC (first_let_if_conv
               (SIMP_CONV (srw_ss())
                  [DOMSUB_FAPPLY_THM,FAPPLY_FUPDATE_THM
                    ,APPLY_UPDATE_THM]))
              \\ simp_tac std_ss [Once LET_THM]))
        \\ simp_tac (srw_ss()) [DOMSUB_FAPPLY_THM,true_pres,
             FAPPLY_FUPDATE_THM,EXTENSION,APPLY_UPDATE_THM]
        \\ CONV_TAC sort_writes_conv \\ fs [true_pres]
        \\ CONV_TAC sort_writes_conv \\ fs [true_pres])
*)

(* HOL4 ML code, not ported:
      val th1 = MP th1 lemma1
      val lemma = prove(``^goal``,
        fs [LET_DEF] \\ rpt strip_tac \\ rw [] \\ fs []
        \\ drule (GEN_ALL th1) \\ fs []
        \\ pairarg_tac \\ fs []
        \\ disch_then (qspecl_then [`s`,`s`] strip_assume_tac) \\ fs []
        \\ rfs [dec_clock_thm])
      val raw_th = MP th lemma |> SIMP_RULE std_ss [LET_THM]
      val th = raw_th |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV
        THENC
                                    sort_writes_conv)
      val _ = save_thm(name ^ "_corr_thm", raw_th)
      val _ = (all_corrs := th::(!all_corrs))
      in (def,raw_th) end
  end;
*)

(* HOL4 ML code, not ported:
val const_def = time (first (not o time (can derive_corr_thm)))
                     (all_code_defs |> CONJUNCTS |> rev)
                handle HOL_ERR _ => TRUTH;
*)

(* HOL4 ML code, not ported:
val _ = (Teq (concl const_def)) orelse failwith
  "derive_corr_thm failed";
*)

(*

val mc_fac_init_corr = snd (derive_corr_thm mc_fac_init_code_def);
val mc_fac_final_corr = snd (derive_corr_thm mc_fac_final_code_def);

Theorem mc_fac_corr:
   Corr mc_fac_code s
     (INR
        (let (l,r1) = mc_fac (s.clock-1,s.regs ' 1) in
           delete_vars [3;0;2] (clock_write l (reg_write 1 (SOME r1)
             s))))
     (1 ∈ FDOM s.regs ∧ mc_fac_pre (s.clock-1,s.regs ' 1) ∧ s.clock <>
       0)
Proof
  all_tac
QED

val th = let
  val raw_th = mc_fac_corr |> SIMP_RULE std_ss [LET_THM]
  val th = raw_th |> CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV THENC
                                sort_writes_conv)
  val _ = (all_corrs := th::(!all_corrs))
  in th end

val mc_use_fac_corr = snd (derive_corr_thm mc_use_fac_code_def);

*)

(* connecting all the theormes *)

(* HOL4 ML code, not ported:
val iop_lemma =
  mc_multiwordTheory.mc_iop_thm
    |> SIMP_RULE std_ss [GSYM PULL_EXISTS] |> UNDISCH_ALL
*)

(* HOL4 ML code, not ported:
val lemma = METIS_PROVE [] ``b /\ c <=> b /\ (b ==> c)``
*)

(* HOL4 ML code, not ported:
val lemma2 = multiwordTheory.mwi_op_thm |> Q.SPECL [`iop`,`i1`,`i2`]
*)

(* HOL4 ML code, not ported:
val mc_iop_corr_thm = fetch "-" "mc_iop_corr_thm"
*)
