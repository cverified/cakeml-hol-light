(* ======================================================== *)
(*  stack_allocProof: ported from HOL4's
    compiler/backend/proofs/stack_allocProofScript.sml
    A proof theory about stack_alloc.ml, with 11 definitions and 116
    theorems.  Needed by stack_to_labProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for stack_alloc
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
(* for memcpy *)
needs "compiler/backend/semantics/labSem.ml";;
needs "compiler/backend/semantics/stackProps.ml";;
needs "compiler/backend/semantics/stackSem.ml";;
needs "compiler/backend/semantics/wordConvs.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/stack_alloc.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/multiword.ml";;
needs "lib/sptree.ml";;
needs "lib/toto.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;

let _ = do_list hide_constant ["not"; "shift"; "stack_alloc"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["data_buffer","data_buffer";
   "memory","memory"];;

(* HOL4 stack_allocProofScript.sml:16: ML code, not ported *)

(* HOL4 stack_allocProofScript.sml:18-21: ML code, not ported *)

(* HOL4 stack_allocProofScript.sml:23-24: the overload good_dimindex,
   which the port expands *)

(* TODO: move and join with stack_remove *)

let lsl_lsr = prove
 (`w2n ((n:'a word)) * 2 EXP a < dimword (:'a) ==> n << a >>> a = n`,
  CHEAT_TAC);;

(* bytes_in_word_word_shift *)
let stack_allocProof_bytes_in_word_word_shift = prove
 (`good_dimindex (:'a) /\ w2n (bytes_in_word:'a word) * w2n n < dimword
  (:'a) ==>
   ((bytes_in_word:'a word) * n) >>> backend_common_word_shift
     (:'a) = n`,
  CHEAT_TAC);;

(* ---- *)

(* [local] *)
let get_var_imm_case = prove
 (`get_var_imm ri s =
     (match ri with Reg n -> get_var n s | Imm w -> SOME
       (wordLang_Word w))`,
  CHEAT_TAC);;

(* [local] *)
let prog_comp_lemma = prove
 (`prog_comp = (\(n,p). (n,FST (comp n (next_lab p 2) p)))`,
  CHEAT_TAC);;

(* FST_prog_comp[simp] *)
let stack_allocProof_FST_prog_comp = prove
 (`FST (prog_comp pp) = FST pp`,
  CHEAT_TAC);;

(* [local] *)
let lookup_IMP_lookup_compile = prove
 (`lookup dest (stackSem_state_code s) = SOME x /\ ~(dest =
  gc_stub_location) ==>
    (?m1 n1. lookup dest (fromAList (compile c (toAList
      (stackSem_state_code s)))) =
            SOME (FST (comp m1 n1 x)))`,
  CHEAT_TAC);;

(* [local] *)
let map_bitmap_APPEND = prove
 (`!x q stack' p0 p1.
       filter_bitmap x stack' = SOME (p0,p1) /\
       LENGTH q = LENGTH p0 ==>
       map_bitmap x (q ++ q') stack' =
       (match map_bitmap x q stack' with NONE -> NONE | SOME
         (hd,ts,ws) -> SOME (hd,ts ++ q',ws))`,
  CHEAT_TAC);;

let filter_bitmap_map_bitmap = prove
 (`!x t q xs xs1 z ys ys1.
      filter_bitmap x t = SOME (xs,xs1) /\
      LENGTH q = LENGTH xs /\
      map_bitmap x q t = SOME (ys,z,ys1) ==>
      z = [] /\ ys1 = xs1`,
  CHEAT_TAC);;

let get_bits_def = cake_define
  `get_bits w = GENLIST (\i. FAPPLY w i) (bit_length w - 1)`;;

let bit_length_thm = prove
 (`!w. ((w >>> bit_length w) = (n2w 0)) /\ (!n. n < bit_length w ==>
  ~((w >>> n) = (n2w 0)))`,
  CHEAT_TAC);;

(* [local] *)
let word_lsr_dimindex = prove
 (`(w:'a word) >>> dimindex (:'a) = (n2w 0)`,
  CHEAT_TAC);;

let bit_length_LESS_EQ_dimindex = prove
 (`bit_length (w:'a word) <= dimindex (:'a)`,
  CHEAT_TAC);;

let shift_to_zero_word_msb = prove
 (`(w:'a word) >>> n = (n2w 0) /\ word_msb w ==> dimindex (:'a) <= n`,
  CHEAT_TAC);;

(* [local] *)
let word_msb_IMP_bit_length = prove
 (`!h. word_msb (h:'a word) ==> (bit_length h = dimindex (:'a))`,
  CHEAT_TAC);;

(* [local] *)
let get_bits_intro = prove
 (`word_msb (h:'a word) ==>
     GENLIST (\i. FAPPLY h i) (dimindex (:'a) - 1) = get_bits h`,
  CHEAT_TAC);;

(* [local] *)
let filter_bitmap_APPEND = prove
 (`!xs stack' ys.
       filter_bitmap (xs ++ ys) stack' =
       (match filter_bitmap xs stack' with NONE -> NONE | SOME
         (zs,rs) ->
         (match filter_bitmap ys rs with NONE -> NONE | SOME
           (zs2,rs) -> SOME (zs ++ zs2,rs)))`,
  CHEAT_TAC);;

let bit_length_minus_1 = prove
 (`~(w = (n2w 0)) ==> bit_length w - 1 = bit_length (w >>> 1)`,
  CHEAT_TAC);;

let bit_length_eq_1 = prove
 (`bit_length w = 1 <=> w = (n2w 1)`,
  CHEAT_TAC);;

(* word_and_one_eq_0_iff *)
let stack_allocProof_word_and_one_eq_0_iff = prove
 (`!w. ((w && (n2w 1)) = (n2w 0)) <=> ~(FAPPLY w 0)`,
  CHEAT_TAC);;

(* [local] *)
let split_num_forall_to_10 = prove
 (`((!) P) <=> P 0 /\ P 1 /\ P 2 /\ P 3 /\ P 4 /\ P 5 /\
                P 6 /\ P 7 /\ P 8 /\ P 9 /\ (!x. 9 < x ==> P
                  (x:num))`,
  CHEAT_TAC);;

(* HOL4 stack_allocProofScript.sml:264-266: ML code, not ported *)

let word_shift_not_0 = prove
 (`~(backend_common_word_shift (:'a) = 0)`,
  CHEAT_TAC);;

let select_lower_lemma = prove
 (`(word_bits n 0) w = ((w:'a word) << (dimindex (:'a) - n - 1)) >>>
  (dimindex (:'a) - n - 1)`,
  CHEAT_TAC);;

let select_eq_select_0 = prove
 (`k <= n ==> (word_bits n k) w = (word_bits (n - k) 0) (w >>> k)`,
  CHEAT_TAC);;

(* [local] *)
let is_fwd_ptr_iff = prove
 (`!w. is_fwd_ptr w <=> (?v. w = wordLang_Word v /\ (v && (n2w 3)) =
  (n2w 0))`,
  CHEAT_TAC);;

(* [local] *)
let isWord_thm = prove
 (`!w. isWord w = (?v. w = wordLang_Word v)`,
  CHEAT_TAC);;

(* [local] *)
let lower_2w_eq = prove
 (`!(w:'a word). good_dimindex (:'a) ==> (w <+ (n2w 2) <=> w = (n2w 0)
  \/ w = (n2w 1))`,
  CHEAT_TAC);;

(* [local] *)
let EL_LENGTH_ADD_LEMMA = prove
 (`EL (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) = x`,
  CHEAT_TAC);;

(* [local] *)
let LUPDATE_LENGTH_ADD_LEMMA = prove
 (`LUPDATE w (LENGTH init + LENGTH old) (init ++ old ++ [x] ++ st1) =
        init ++ old ++ [w] ++ st1`,
  CHEAT_TAC);;

let word_msb_IFF_lsr_EQ_0 = prove
 (`word_msb h <=> (~(h >>> (dimindex (:'a) - 1) = ((n2w 0):'a word)))`,
  CHEAT_TAC);;

let map_bitmap_IMP_LENGTH = prove
 (`!x wl stack' xs ys.
      map_bitmap x wl stack' = SOME (xs,ys) ==>
      LENGTH xs = LENGTH x`,
  CHEAT_TAC);;

let filter_bitmap_IMP_LENGTH = prove
 (`!x stack' q r.
      filter_bitmap x stack' = SOME (q,r) ==>
      LENGTH stack' = LENGTH x + LENGTH r`,
  CHEAT_TAC);;

(* EL_LENGTH_ADD_LEMMA[local] *)
let stack_allocProof_EL_LENGTH_ADD_LEMMA = prove
 (`!n xs y ys. LENGTH xs = n ==> EL n (xs ++ (y :: ys)) = y`,
  CHEAT_TAC);;

let bytes_in_word_word_shift_n2w = prove
 (`good_dimindex (:'a) /\ (dimindex (:'a) DIV 8) * n < dimword (:'a) ==>
    (bytes_in_word * n2w n) >>> backend_common_word_shift (:'a) =
      ((n2w n):'a word)`,
  CHEAT_TAC);;

(* lt_dimindex_MOD_dimword[local,simp] *)
let stack_allocProof_lt_dimindex_MOD_dimword = prove
 (`n < dimindex (:'a) ==> n MOD dimword (:'a) = n`,
  CHEAT_TAC);;

(* HOL4 stack_allocProofScript.sml:372-377: a proof *)

(* HOL4 stack_allocProofScript.sml:379-384: a proof *)

(* HOL4 stack_allocProofScript.sml:386-388: a proof *)

(* [local] *)
let memcpy_code_thm = prove
 (`!n a b m dm b1 m1 (s:('a,'c,'b)stackSem_state).
       memcpy ((n2w n):'a word) a b m dm = ((b1:'a word),m1,T) /\
       n < dimword (:'a) /\ stackSem_state_memory
       s = m /\ stackSem_state_mdomain s = dm /\
       get_var 0 s = SOME (wordLang_Word (n2w n)) /\
       1 IN FDOM (stackSem_state_regs s) /\
       get_var 2 s = SOME (wordLang_Word a) /\
       get_var 3 s = SOME (wordLang_Word b) ==>
       (?r1.
         evaluate (memcpy_code,stackSem_state_clock_fupd (K
           (stackSem_state_clock s + n)) s) =
           (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
             |++ [(0,wordLang_Word (n2w 0));
                              (1,r1);
                              (2,wordLang_Word (a + n2w n *
                                bytes_in_word));
                              (3,wordLang_Word b1)]))
                                (stackSem_state_memory_fupd (K m1)
                                s)))`,
  CHEAT_TAC);;

(* memcpy_code_thm *)
let stack_allocProof_memcpy_code_thm = prove
 (`!w a b m dm b1 m1 (s:('a,'c,'b)stackSem_state).
      memcpy (w:'a word) a b m dm = ((b1:'a word),m1,T) /\
        stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
      get_var 0 s = SOME (wordLang_Word w) /\
      1 IN FDOM (stackSem_state_regs s) /\
      get_var 2 s = SOME (wordLang_Word a) /\
      get_var 3 s = SOME (wordLang_Word b) ==>
      (?r1.
        evaluate (memcpy_code,stackSem_state_clock_fupd (K
          (stackSem_state_clock s + w2n w)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,wordLang_Word (n2w 0));
                              (1,r1);
                              (2,wordLang_Word (a + w *
                                bytes_in_word));
                              (3,wordLang_Word b1)]))
                                (stackSem_state_memory_fupd (K m1)
                                s)))`,
  CHEAT_TAC);;

(* gc_kind = Simple *)

(* HOL4 stack_allocProofScript.sml:469-479: ML code, not ported *)

(* [local] *)
let word_gc_fun_thm = prove
 (`data_to_word_config_gc_kind
     conf = Simple ==>
      word_gc_fun conf (roots,m,dm,s) =
         (let (w1,(i1:'a word),pa1,m1,c1) =
               word_gc_move conf
                 (FAPPLY s Globals,(n2w 0),theWord (FAPPLY s
                   OtherHeap),
                  theWord (FAPPLY s CurrHeap),m,dm) in
         let (ws2,i2,pa2,m2,c2) =
               word_gc_move_roots conf
                 (roots,i1,pa1,theWord (FAPPLY s CurrHeap),m1,dm) in
         let (i1,pa1,m1,c2) =
               word_gc_move_loop (dimword (:'a)) conf
                 (theWord (FAPPLY s OtherHeap),i2,pa2,
                  theWord (FAPPLY s CurrHeap),m2,dm,(c1 /\ c2)) in
         let s1 =
               s |++
               [(CurrHeap,wordLang_Word (theWord (FAPPLY s
                 OtherHeap)));
                (OtherHeap,wordLang_Word (theWord (FAPPLY s
                  CurrHeap)));
                (NextFree,wordLang_Word pa1);
                (TriggerGC,
                 wordLang_Word
                   (theWord (FAPPLY s OtherHeap) +
                    theWord (FAPPLY s HeapLength)));
                (EndOfHeap,
                 wordLang_Word
                   (theWord (FAPPLY s OtherHeap) +
                    theWord (FAPPLY s HeapLength)));
                (Globals,w1);
                (GlobReal,glob_real conf (theWord (FAPPLY s
                  OtherHeap)) w1)] in
           if word_gc_fun_assum conf s /\ c2 then SOME (ws2,m1,s1)
             else NONE)`,
  CHEAT_TAC);;

(* HOL4 stack_allocProofScript.sml:519-524: ML code, not ported *)

let word_gc_move_roots_bitmaps_def = cake_define
  `word_gc_move_roots_bitmaps conf (stack',bitmaps,i1,pa1,curr,m,dm) =
     (match enc_stack bitmaps stack' with NONE -> (ARB,ARB,ARB,ARB,F)
       | SOME wl_list ->
         (let (wl,i2,pa2,m2,c2) =
             word_gc_move_roots conf (wl_list,i1,pa1,curr,m,dm) in
           match dec_stack bitmaps wl stack' with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME stack' ->
             (stack',i2,pa2,m2,c2)))`;;

let word_gc_move_loop_F = prove
 (`!k conf pb i pa old m dm i1 pa1 m1 c1.
      word_gc_move_loop k conf (pb,i,pa,old,m,dm,F) =
        (i1,pa1,m1,c1) ==> ~c1`,
  CHEAT_TAC);;

let word_gc_move_loop_ok = prove
 (`word_gc_move_loop k conf (pb,i,pa,old,m,dm,c) = (i1,pa1,m1,c1) ==>
  c1 ==> c`,
  CHEAT_TAC);;

(* [local] *)
let gc_thm = prove
 (`stackSem_state_gc_fun
     s = word_gc_fun conf /\ data_to_word_config_gc_kind conf =
       Simple ==>
      gc (s:('a,'c,'b)stackSem_state) =
      (if LENGTH (stackSem_state_stack s) <
        stackSem_state_stack_space s then NONE else
        let unused = TAKE (stackSem_state_stack_space s)
          (stackSem_state_stack s) in
        let stack' = DROP (stackSem_state_stack_space s)
          (stackSem_state_stack s) in
        let (w1,i1,pa1,m1,c1) =
                 word_gc_move conf
                   (FAPPLY (stackSem_state_store s) Globals,(n2w 0),
                    theWord (FAPPLY (stackSem_state_store s)
                      OtherHeap),
                    theWord (FAPPLY (stackSem_state_store s)
                      CurrHeap),stackSem_state_memory
                      s,stackSem_state_mdomain s) in
        let (stack',i2,pa2,m2,c2) =
              word_gc_move_roots_bitmaps conf
                (stack',stackSem_state_bitmaps s,i1,pa1,
                 theWord (FAPPLY (stackSem_state_store s)
                   CurrHeap),m1,stackSem_state_mdomain s) in
        let (i1,pa1,m1,c2) =
              word_gc_move_loop (dimword (:'a)) conf
                (theWord (FAPPLY (stackSem_state_store s)
                  OtherHeap),i2,pa2,
                 theWord (FAPPLY (stackSem_state_store s)
                   CurrHeap),m2,stackSem_state_mdomain s,(
                 c1 /\ c2)) in
        let s1 = stackSem_state_store
              s |++
              [(CurrHeap,wordLang_Word (theWord (FAPPLY
                (stackSem_state_store s) OtherHeap)));
               (OtherHeap,wordLang_Word (theWord (FAPPLY
                 (stackSem_state_store s) CurrHeap)));
               (NextFree,wordLang_Word pa1);
               (TriggerGC,
                wordLang_Word
                  (theWord (FAPPLY (stackSem_state_store s)
                    OtherHeap) +
                   theWord (FAPPLY (stackSem_state_store s)
                     HeapLength)));
               (EndOfHeap,
                wordLang_Word
                  (theWord (FAPPLY (stackSem_state_store s)
                    OtherHeap) +
                   theWord (FAPPLY (stackSem_state_store s)
                     HeapLength)));
               (Globals,w1);
               (GlobReal,glob_real conf (theWord (FAPPLY
                 (stackSem_state_store s) OtherHeap)) w1)] in
          if word_gc_fun_assum conf (stackSem_state_store s) /\ c2
            then SOME (stackSem_state_memory_fupd (K m1)
            (stackSem_state_regs_fupd (K FEMPTY)
            (stackSem_state_store_fupd (K s1)
            (stackSem_state_stack_fupd (K (unused ++ stack')) s))))
            else NONE)`,
  CHEAT_TAC);;

let word_gc_move_bitmaps_def = cake_define
  `word_gc_move_bitmaps conf (w,stack',bitmaps,i1,pa1,curr,m,dm) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack' with NONE -> NONE | SOME
         (ts,ws) ->
         (let (wl,i2,pa2,m2,c2) =
                 word_gc_move_roots conf (ts,i1,pa1,curr,m,dm) in
           match map_bitmap bs wl stack' with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,m2,c2))))`;;

(* [local] *)
let word_gc_move_roots_APPEND = prove
 (`!xs ys i1 pa1 m.
       word_gc_move_roots conf (xs ++ ys,i1,pa1,curr,m,dm) =
         (let (ws1,i1,pa1,m1,c1) = word_gc_move_roots conf
           (xs,i1,pa1,curr,m,dm) in
         let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf
           (ys,i1,pa1,curr,m1,dm) in
           (ws1 ++ ws2,i2,pa2,m2,(c1 /\ c2)))`,
  CHEAT_TAC);;

let word_gc_move_roots_IMP_LENGTH = prove
 (`!xs r0 r1 curr r2 dm ys i2 pa2 m2 c conf.
      word_gc_move_roots conf (xs,r0,r1,curr,r2,dm) =
        (ys,i2,pa2,m2,c) ==>
      LENGTH ys = LENGTH xs`,
  CHEAT_TAC);;

(* [local] *)
let word_gc_move_roots_bitmaps = prove
 (`!stack' i1 pa1 m stack2 i2 pa2 m2.
       (word_gc_move_roots_bitmaps conf
         (stack',bitmaps,i1,pa1,curr,m,dm) =
         (stack2,i2,pa2,m2,T)) ==>
       word_gc_move_roots_bitmaps conf
         (stack',bitmaps,i1,pa1,curr,m,dm) =
       (match stack' with [] -> (ARB,ARB,ARB,ARB,F) | (w :: ws) ->
         (if w = wordLang_Word (n2w 0) then (stack',i1,pa1,m,(ws =
           [])) else
           match word_gc_move_bitmaps conf
             (w,ws,bitmaps,i1,pa1,curr,m,dm) with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME (new,stack',i2,pa2,m2,c2) ->
               (let (stack',i,pa,m,c3) =
                 word_gc_move_roots_bitmaps conf
                   (stack',bitmaps,i2,pa2,curr,m2,dm) in
                   ((w :: new) ++ stack',i,pa,m,(c2 /\ c3)))))`,
  CHEAT_TAC);;

let word_gc_move_bitmap_def = cake_define
  `word_gc_move_bitmap conf (w,stack',i1,pa1,curr,m,dm) =
     (let bs = get_bits w in
       match filter_bitmap bs stack' with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,m2,c2) = word_gc_move_roots conf
            (ts,i1,pa1,curr,m,dm) in
            match map_bitmap bs wl stack' with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 stack_allocProofScript.sml:718-740: a theorem that HOL4
   states as the value of an ML expression: map_bitmap_APPEND_APPEND *)

(* HOL4 stack_allocProofScript.sml:742-744: the ML values that the
   definitions below antiquote *)

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gc_move_bitmaps_unroll = prove
 (cake_as_vars (fun () ->
    `word_gc_move_bitmaps conf (wordLang_Word
  w,stack,bitmaps,i1,pa1,curr,m,dm) = SOME x /\
       LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a)
         ==>
       word_gc_move_bitmaps conf (wordLang_Word
         w,stack,bitmaps,i1,pa1,curr,m,dm) =
       (match DROP (w2n (w - ((n2w 1):'a word))) bitmaps with [] ->
         NONE | (y :: ys) ->
         (match word_gc_move_bitmap conf (y,stack,i1,pa1,curr,m,dm)
           with NONE -> NONE | SOME (hd,ws,i2,pa2,m2,c2) ->
             (if ~(word_msb y) then SOME (hd,ws,i2,pa2,m2,c2) else
               match word_gc_move_bitmaps conf (wordLang_Word (w +
                 (n2w 1)),ws,bitmaps,i2,pa2,curr,m2,dm) with NONE ->
                 NONE | SOME (hd3,ws3,i3,pa3,m3,c3) ->
                   SOME (hd ++ hd3,ws3,i3,pa3,m3,(c2 /\ c3)))))`),
  CHEAT_TAC);;

(* [local] *)
let word_gc_move_bitmap_unroll = prove
 (`word_gc_move_bitmap conf (w,stack',i1,pa1,curr,m,dm) =
     (if w = ((n2w 0):'a word) then SOME ([],stack',i1,pa1,m,T) else
     if w = (n2w 1) then SOME ([],stack',i1,pa1,m,T) else
       match stack' with [] -> NONE | (x :: xs) ->
         (if (w && (n2w 1)) = (n2w 0) then
           match word_gc_move_bitmap conf (w >>>
             1,xs,i1,pa1,curr,m,dm) with NONE -> NONE | SOME
             (new,stack',i1,pa1,m,c) -> SOME (x ::
             new,stack',i1,pa1,m,c) else
           let (x1,i1,pa1,m1,c1) = word_gc_move conf
             (x,i1,pa1,curr,m,dm) in
           match word_gc_move_bitmap conf (w >>>
             1,xs,i1,pa1,curr,m1,dm) with NONE -> NONE | SOME
             (new,stack',i1,pa1,m,c) -> SOME (x1 ::
             new,stack',i1,pa1,m,(c1 /\ c))))`,
  CHEAT_TAC);;

let word_gc_move_code_thm = prove
 (`word_gc_move conf (w,i,pa,old,m,dm) = (w1,i1,pa1,m1,T) /\
    shift_length conf < dimindex (:'a) /\ backend_common_word_shift
      (:'a) < dimindex (:'a) /\
    2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0) /\
    (!(w:'a word). w << backend_common_word_shift (:'a) = w *
      bytes_in_word) /\
    FLOOKUP (stackSem_state_store (s:('a,'c,'b)stackSem_state))
      CurrHeap = SOME (wordLang_Word old) /\ stackSem_state_use_store s
      /\ stackSem_state_memory
    s = m /\ stackSem_state_mdomain s = dm /\
    0 IN FDOM (stackSem_state_regs s) /\
    1 IN FDOM (stackSem_state_regs s) /\
    2 IN FDOM (stackSem_state_regs s) /\
    get_var 3 s = SOME (wordLang_Word pa) /\
    get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
    get_var 5 s = SOME w /\
    6 IN FDOM (stackSem_state_regs s) ==>
    (?ck r0 r1 r2 r6.
      evaluate (word_gc_move_code conf,stackSem_state_clock_fupd (K
        (stackSem_state_clock s + ck)) s) =
        (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s |++
          [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,w1);
                              (6,r6)])) (stackSem_state_memory_fupd
                                (K m1) s)))`,
  CHEAT_TAC);;

let word_gc_move_list_code_thm = prove
 (`!l a (s:('a,'c,'b)stackSem_state) pa1 pa old m1 m i1 i dm conf a1.
      word_gc_move_list conf ((a:'a word),l,i,pa,old,m,dm) =
        (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        old) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
       0 IN FDOM (stackSem_state_regs s) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) ==>
      6 IN FDOM (stackSem_state_regs s) ==>
      get_var 7 s = SOME (wordLang_Word l) /\
      get_var 8 s = SOME (wordLang_Word a) ==>
      (?ck r0 r1 r2 r5 r6.
        evaluate (word_gc_move_list_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,wordLang_Word (n2w 0));
                              (8,wordLang_Word a1)]))
                                (stackSem_state_memory_fupd (K m1)
                                s)))`,
  CHEAT_TAC);;

(* [local] *)
let word_gc_move_loop_code_thm = prove
 (`!k pb1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:('a,'c,'b)stackSem_state).
       word_gc_move_loop k conf (pb1,i1,pa1,old1,m1,dm1,c1) =
         (i2,pa2,m2,T) /\
       shift_length conf < dimindex (:'a) /\
         backend_common_word_shift (:'a) < dimindex (:'a) /\
       2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
         /\ data_to_word_config_len_size
       conf + 2 < dimindex (:'a) /\
       (!(w:'a word). w << backend_common_word_shift (:'a) = w *
         bytes_in_word) /\
       FLOOKUP (stackSem_state_store s) CurrHeap = SOME
         (wordLang_Word old1) /\ stackSem_state_use_store s /\
         stackSem_state_memory
       s = m1 /\ stackSem_state_mdomain s = dm1 /\
       0 IN FDOM (stackSem_state_regs s) /\
       1 IN FDOM (stackSem_state_regs s) /\
       2 IN FDOM (stackSem_state_regs s) /\
       get_var 3 s = SOME (wordLang_Word pa1) /\
       get_var 4 s = SOME (wordLang_Word (i1:'a word)) /\
       5 IN FDOM (stackSem_state_regs s) ==>
       6 IN FDOM (stackSem_state_regs s) ==>
       7 IN FDOM (stackSem_state_regs s) ==>
       get_var 8 s = SOME (wordLang_Word pb1) /\ c1 ==>
       (?ck r0 r1 r2 r5 r6 r7.
         evaluate (word_gc_move_loop_code
           conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
           ck)) s) =
           (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
             |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa2);
                              (4,wordLang_Word i2);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,wordLang_Word pa2)]))
                                (stackSem_state_memory_fupd (K m2)
                                s)))`,
  CHEAT_TAC);;

let word_gc_move_bitmap_code_thm = prove
 (`!w stack' (s:('a,'c,'b)stackSem_state) i pa curr m dm new stack1 a1
  i1 pa1 m1 old.
      word_gc_move_bitmap conf (w,stack',i,pa,curr,m,dm) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\ good_dimindex (:'a) /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        curr) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
        stackSem_state_use_stack s /\
      0 IN FDOM (stackSem_state_regs s) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) /\
      6 IN FDOM (stackSem_state_regs s) /\
      get_var 7 s = SOME (wordLang_Word w) /\
      get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w (LENGTH
        old))) /\ stackSem_state_stack
      s = init ++ old ++ stack' /\ stackSem_state_stack_space
      s = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
        dimword (:'a) ==>
      (?ck r0 r1 r2 r5 r6 r7.
        evaluate (word_gc_move_bitmap_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                      (8,wordLang_Word (bytes_in_word * n2w (LENGTH
                        (old ++ new))))])) (stackSem_state_stack_fupd
                        (K (init ++ old ++ new ++ stack1))
                        (stackSem_state_memory_fupd (K m1) s))))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gc_move_bitmaps_LENGTH = prove
 (cake_as_vars (fun () ->
    `word_gc_move_bitmaps conf (w,stack,bitmaps,i,pa,curr,m,dm) =
         SOME (xs,stack1,i1,pa1,m1,T) ==>
      LENGTH stack = LENGTH xs + LENGTH stack1`),
  CHEAT_TAC);;

let word_gc_move_bitmaps_code_thm = prove
 (`!w bitmaps z stack' (s:('a,'c,'b)stackSem_state) i pa curr m dm new
         stack1 a1 i1 pa1 m1 old.
      word_gc_move_bitmaps conf (wordLang_Word
        w,stack',bitmaps,i,pa,curr,m,dm) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\ good_dimindex (:'a) /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        curr) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
        stackSem_state_bitmaps s = bitmaps /\ stackSem_state_use_stack s
        /\
      get_var 0 s = SOME (wordLang_Word z) /\ ~(z = (n2w 0)) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) /\
      6 IN FDOM (stackSem_state_regs s) /\
      7 IN FDOM (stackSem_state_regs s) /\
      get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w (LENGTH
        old))) /\
      get_var 9 s = SOME (wordLang_Word (w - (n2w 1))) /\
        stackSem_state_stack
      s = init ++ old ++ stack' /\ stackSem_state_stack_space
      s = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
        dimword (:'a) ==>
      (?ck r0 r1 r2 r5 r6 r7 r9.
        evaluate (word_gc_move_bitmaps_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                      (8,wordLang_Word (bytes_in_word * n2w (LENGTH
                        (old ++ new))));
                              (9,r9)])) (stackSem_state_clock_fupd
                                (K (stackSem_state_clock s))
                                (stackSem_state_stack_fupd (K (init ++
                                old ++ new ++ stack1))
                                (stackSem_state_memory_fupd (K m1)
                                s)))))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gc_move_roots_bitmaps_code_thm = prove
 (cake_as_vars (fun () ->
    `!bitmaps (s:('a,'c,'b)stackSem_state) i pa curr m dm new
           stack1 a1 i1 pa1 m1 old.
        word_gc_move_roots_bitmaps conf
          (stack,bitmaps,i,pa,curr,m,dm) =
          (stack1,i1,pa1,m1,T) /\
        LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a)
          /\
        shift_length conf < dimindex (:'a) /\
          backend_common_word_shift (:'a) < dimindex (:'a) /\
        2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf =
          0) /\ good_dimindex (:'a) /\
        (!(w:'a word). w << backend_common_word_shift (:'a) = w *
          bytes_in_word) /\
        FLOOKUP (stackSem_state_store s) CurrHeap = SOME
          (wordLang_Word curr) /\ stackSem_state_use_store s /\
          stackSem_state_memory
        s = m /\ stackSem_state_mdomain s = dm /\
          stackSem_state_bitmaps s = bitmaps /\ stackSem_state_use_stack
          s /\
        0 IN FDOM (stackSem_state_regs s) /\
        1 IN FDOM (stackSem_state_regs s) /\
        2 IN FDOM (stackSem_state_regs s) /\
        get_var 3 s = SOME (wordLang_Word pa) /\
        get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
        5 IN FDOM (stackSem_state_regs s) /\
        6 IN FDOM (stackSem_state_regs s) /\
        7 IN FDOM (stackSem_state_regs s) /\
        get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w
          (LENGTH old))) /\
        get_var 9 s = SOME (HD stack) /\ stackSem_state_stack
        s = init ++ old ++ stack /\ stackSem_state_stack_space
        s = LENGTH init /\
        (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
          dimword (:'a) ==>
        (?ck r0 r1 r2 r5 r6 r7 r8 r9.
          evaluate (word_gc_move_roots_bitmaps_code
            conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
            ck))
              s) =
            (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs
              s |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,r8);
                              (9,wordLang_Word (n2w 0))]))
                                (stackSem_state_clock_fupd (K
                                (stackSem_state_clock s))
                                (stackSem_state_stack_fupd (K (init ++
                                old ++ stack1))
                                (stackSem_state_memory_fupd (K m1)
                                s)))))`),
  CHEAT_TAC);;


let alloc_correct_lemma_Simple = prove
 (`alloc w (s:('a,'c,'b)stackSem_state) = (r,t) /\ ~(r = SOME Error) /\
  stackSem_state_gc_fun
    s = word_gc_fun conf /\ data_to_word_config_gc_kind conf = Simple
      /\
    LENGTH (stackSem_state_bitmaps s) < dimword (:'a) - 1 /\
    LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
      dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (wordLang_Word w) ==>
    (?ck l2.
      evaluate
        (word_gc_code conf,stackSem_state_code_fupd (K (fromAList
          (compile c (toAList (stackSem_state_code s)))))
          (stackSem_state_gc_fun_fupd (K anything)
          (stackSem_state_regs_fupd (K l) (stackSem_state_clock_fupd (K
          (stackSem_state_clock s + ck)) (stackSem_state_use_alloc_fupd
          (K F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         s))))))) =
        (r,state_gc_fun_fupd (K anything) (stackSem_state_regs_fupd
          (K l2) (state_code_fupd (K (fromAList (compile c (toAList
          (stackSem_state_code s))))) (stackSem_state_use_alloc_fupd (K
          F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         t)))))) /\
       (~(r = NONE) ==> r = SOME (Halt (wordLang_Word (n2w 1)))) /\
         stackSem_state_regs
       t SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret))`,
  CHEAT_TAC);;

(* gc_kind = Generational *)

(* HOL4 stack_allocProofScript.sml:1717: the ML values that the
   definitions below antiquote *)

(* HOL4 stack_allocProofScript.sml:1719-1729: ML code, not ported *)

(* word_gc_fun_thm[local] *)
let stack_allocProof_word_gc_fun_thm = prove
 (`data_to_word_config_gc_kind
     conf = (data_to_word_Generational gen_sizes) ==>
      word_gc_fun conf (roots,m,dm,s) =
        (if ~(word_gc_fun_assum conf s) then NONE else
        if word_gen_gc_can_do_partial gen_sizes s then
          (\(roots1,i1,pa1,m1,c2).
             if c2 /\
                   theWord (FAPPLY s AllocSize) <=+ --(n2w 1) * pa1 +
                     theWord (FAPPLY s EndOfHeap) /\ theWord (FAPPLY s
                     AllocSize) <=+ new_trig
                        (theWord (FAPPLY s EndOfHeap) - pa1)
                        (theWord (FAPPLY s AllocSize)) gen_sizes then
               SOME
                 (TL roots1,m1,
                  s |++
                  [(CurrHeap,wordLang_Word (theWord (FAPPLY s
                    CurrHeap)));
                   (OtherHeap,wordLang_Word (theWord (FAPPLY s
                     OtherHeap)));
                   (NextFree,wordLang_Word pa1);
                   (GenStart,wordLang_Word (pa1 + --(n2w 1) * theWord
                     (FAPPLY s CurrHeap)));
                   (TriggerGC,wordLang_Word (pa1 + new_trig (theWord
                     (FAPPLY s EndOfHeap) - pa1)
                              (theWord (FAPPLY s AllocSize))
                                gen_sizes));
                   (Globals,HD roots1);
                   (GlobReal,glob_real conf (theWord (FAPPLY s
                     CurrHeap)) (HD roots1));
                   (Temp (n2w 0),wordLang_Word (n2w 0)); (Temp (n2w
                     1),wordLang_Word (n2w 0))]) else NONE)
            ((\(roots,i,pa,m,c1).
                (\(b1,m,c2). (roots,i,b1,m,(c1 /\ c2)))
                  (memcpy
                     ((pa + --(n2w 1) * theWord (FAPPLY s OtherHeap))
                       >>> backend_common_word_shift (:'a))
                     (theWord (FAPPLY s OtherHeap))
                     (theWord (FAPPLY s CurrHeap) + theWord (FAPPLY s
                       GenStart)) m
                     dm))
               ((\(roots,i,pa,m,c1).
                   (\(i,pa,m,c2).
                      (\(i,pa,m,c3). (roots,i,pa,m,(c2 /\ c3)))
                        (word_gen_gc_partial_move_data conf (dimword
                          (:'a))
                           (theWord (FAPPLY s OtherHeap),i,pa,
                            theWord (FAPPLY s CurrHeap),m,dm,
                            theWord (FAPPLY s GenStart),
                            --(n2w 1) * theWord (FAPPLY s CurrHeap) +
                            theWord (FAPPLY s EndOfHeap))))
                     (word_gen_gc_partial_move_ref_list (dimword
                       (:'a)) conf
                        (theWord (FAPPLY s EndOfHeap),i,pa,
                         theWord (FAPPLY s CurrHeap),m,dm,c1,
                         theWord (FAPPLY s GenStart),
                         --(n2w 1) * theWord (FAPPLY s CurrHeap) +
                         theWord (FAPPLY s EndOfHeap),
                         theWord (FAPPLY s CurrHeap) +
                         theWord (FAPPLY s HeapLength))))
                  (word_gen_gc_partial_move_roots conf
                     (FAPPLY s Globals :: roots,
                      theWord (FAPPLY s GenStart) >>>
                        backend_common_word_shift (:'a),
                      theWord (FAPPLY s OtherHeap),theWord (FAPPLY s
                        CurrHeap),m,dm,
                      theWord (FAPPLY s GenStart),
                      --(n2w 1) * theWord (FAPPLY s CurrHeap) +
                      theWord (FAPPLY s EndOfHeap))))) else
         (let new_end = theWord (FAPPLY s OtherHeap) + theWord
           (FAPPLY s HeapLength) in
          let len = theWord (FAPPLY s HeapLength) >>>
            backend_common_word_shift (:'a) in
          let (w1,i1,pa1,ib',pb',m1,c1) =
                 word_gen_gc_move conf
                   (FAPPLY s Globals,(n2w 0),theWord (FAPPLY s
                     OtherHeap),
                    len,new_end,theWord (FAPPLY s CurrHeap),m,dm) in
          let (ws2,i2,pa2,ib2,(pb2:'a word),m2,c2) =
                 word_gen_gc_move_roots conf
                   (roots,i1,pa1,ib',pb',
                    theWord (FAPPLY s CurrHeap),m1,dm) in
          let (i3,pa3,ib3,pb3,m3,c3) =
                word_gen_gc_move_loop conf (w2n len)
                  (theWord (FAPPLY s
                    OtherHeap),i2,pa2,ib2,pb2,new_end,
                   theWord (FAPPLY s CurrHeap),m2,dm) in
          let a = theWord (FAPPLY s AllocSize) in
          let s1 =
                s |++
                [(CurrHeap,wordLang_Word (theWord (FAPPLY s
                  OtherHeap)));
                 (OtherHeap,wordLang_Word (theWord (FAPPLY s
                   CurrHeap)));
                 (NextFree,wordLang_Word pa3);
                 (GenStart,wordLang_Word (pa3 - theWord (FAPPLY s
                   OtherHeap)));
                 (TriggerGC,wordLang_Word (pa3 + new_trig (pb3 - pa3)
                   a gen_sizes));
                 (EndOfHeap,wordLang_Word pb3); (Globals,w1);
                 (GlobReal,glob_real conf (theWord (FAPPLY s
                   OtherHeap)) w1);
                 (Temp (n2w 0),wordLang_Word (n2w 0));
                 (Temp (n2w 1),wordLang_Word (n2w 0));
                 (Temp (n2w 2),wordLang_Word (n2w 0));
                 (Temp (n2w 3),wordLang_Word (n2w 0));
                 (Temp (n2w 4),wordLang_Word (n2w 0));
                 (Temp (n2w 5),wordLang_Word (n2w 0));
                 (Temp (n2w 6),wordLang_Word (n2w 0))] in
            if word_gc_fun_assum conf s /\ c1 /\ c2 /\ c3 then SOME
              (ws2,m3,s1) else NONE))`,
  CHEAT_TAC);;

(* HOL4 stack_allocProofScript.sml:1835-1840: ML code, not ported *)

let word_gen_gc_move_roots_bitmaps_def = cake_define
  `word_gen_gc_move_roots_bitmaps conf
  (stack',bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
     (match enc_stack bitmaps stack' with NONE ->
       (ARB,ARB,ARB,ARB,ARB,ARB,F) | SOME wl_list ->
         (let (wl,i2,pa2,ib2,pb2,m2,c2) =
             word_gen_gc_move_roots conf
               (wl_list,i1,pa1,ib1,pb1,curr,m,dm) in
           match dec_stack bitmaps wl stack' with NONE ->
             (ARB,ARB,ARB,ARB,ARB,ARB,F) | SOME stack' ->
             (stack',i2,pa2,ib2,pb2,m2,c2)))`;;

let word_gen_gc_partial_move_roots_bitmaps_def = cake_define
  `word_gen_gc_partial_move_roots_bitmaps conf
  (stack',bitmaps,i1,pa1,curr,m,dm,gs,rs) =
     (match enc_stack bitmaps stack' with NONE -> (ARB,ARB,ARB,ARB,F)
       | SOME wl_list ->
         (let (wl,i2,pa2,m2,c2) =
             word_gen_gc_partial_move_roots conf
               (wl_list,i1,pa1,curr,m,dm,gs,rs) in
           match dec_stack bitmaps wl stack' with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME stack' ->
             (stack',i2,pa2,m2,c2)))`;;

(* [local] *)
let word_gen_gc_partial_move_ref_list_ok = prove
 (`!k rs re pb pa old m i gs dm conf c i1 pa1 m1.
     word_gen_gc_partial_move_ref_list k conf
      (pb,i,pa,old,m,dm,c,gs,rs,re) = (i1,pa1,m1,T) ==> c`,
  CHEAT_TAC);;

(* gc_thm[local] *)
let stack_allocProof_gc_thm = prove
 (`stackSem_state_gc_fun
     s = word_gc_fun conf /\ data_to_word_config_gc_kind conf =
       (data_to_word_Generational gen_sizes) ==>
      gc (s:('a,'c,'b)stackSem_state) =
      (if LENGTH (stackSem_state_stack s) <
        stackSem_state_stack_space s then NONE else
        if ~(word_gc_fun_assum conf (stackSem_state_store s)) then
          NONE else
        if word_gen_gc_can_do_partial gen_sizes (stackSem_state_store
          s) then
         (let unused = TAKE (stackSem_state_stack_space s)
           (stackSem_state_stack s) in
          let stack' = DROP (stackSem_state_stack_space s)
            (stackSem_state_stack s) in
          let gs = theWord (FAPPLY (stackSem_state_store s) GenStart)
            in
          let other = theWord (FAPPLY (stackSem_state_store s)
            OtherHeap) in
          let curr = theWord (FAPPLY (stackSem_state_store s)
            CurrHeap) in
          let endh = theWord (FAPPLY (stackSem_state_store s)
            EndOfHeap) in
          let (w1,i1,pa1,m1,c1) = word_gen_gc_partial_move conf
                 (FAPPLY (stackSem_state_store s) Globals,gs >>>
                   backend_common_word_shift
                   (:'a),other,curr,stackSem_state_memory
                  s,stackSem_state_mdomain s,gs,endh - curr) in
          let (ws2,i1,pa1,m1,c2) =
            word_gen_gc_partial_move_roots_bitmaps conf
                 (stack',stackSem_state_bitmaps
                   s,i1,pa1,curr,m1,stackSem_state_mdomain s,gs,endh -
                   curr) in
          let (i1,pa1,m1,c3) =
                 word_gen_gc_partial_move_ref_list (dimword (:'a))
                   conf
                  (endh,i1,pa1,curr,m1,stackSem_state_mdomain s,(c1
                    /\ c2),gs,
                   endh - curr,curr + theWord (FAPPLY
                     (stackSem_state_store s) HeapLength)) in
          let (i1,pa1,m1,c4) = word_gen_gc_partial_move_data conf
            (dimword (:'a))
                  (other,i1,pa1,curr,m1,stackSem_state_mdomain
                    s,gs,endh - curr) in
          let (b1,m1,c5) = memcpy ((pa1 - other) >>>
            backend_common_word_shift (:'a)) other (curr + gs) m1
            (stackSem_state_mdomain
                            s) in
          let s1 = stackSem_state_store s |++
                   [(CurrHeap,wordLang_Word curr);
                    (OtherHeap,wordLang_Word other);
                    (NextFree,wordLang_Word b1);
                    (GenStart,wordLang_Word (b1 - curr));
                    (TriggerGC,wordLang_Word (b1 + new_trig
                       (theWord (FAPPLY (stackSem_state_store s)
                         EndOfHeap) - b1)
                       (theWord (FAPPLY (stackSem_state_store s)
                         AllocSize)) gen_sizes));
                    (Globals,w1);
                    (GlobReal,glob_real conf (theWord (FAPPLY
                      (stackSem_state_store s) CurrHeap)) w1);
                    (Temp (n2w 0),wordLang_Word (n2w 0));
                    (Temp (n2w 1),wordLang_Word (n2w 0))] in
          let c6 = ((theWord (FAPPLY (stackSem_state_store s)
            AllocSize) <=+
                     theWord (FAPPLY (stackSem_state_store s)
                       EndOfHeap) - b1) /\
                    (theWord (FAPPLY (stackSem_state_store s)
                      AllocSize) <=+ new_trig
                       (theWord (FAPPLY (stackSem_state_store s)
                         EndOfHeap) - b1)
                       (theWord (FAPPLY (stackSem_state_store s)
                         AllocSize)) gen_sizes)) in
            if word_gc_fun_assum conf (stackSem_state_store s) /\ c3
              /\ c4 /\ c5 /\ c6 then SOME (stackSem_state_memory_fupd (K
              m1) (stackSem_state_regs_fupd (K FEMPTY)
              (stackSem_state_store_fupd (K s1)
              (stackSem_state_stack_fupd (K (unused ++ ws2)) s)))) else
              NONE) else
         (let unused = TAKE (stackSem_state_stack_space s)
           (stackSem_state_stack s) in
          let stack' = DROP (stackSem_state_stack_space s)
            (stackSem_state_stack s) in
          let new_end = theWord (FAPPLY (stackSem_state_store s)
            OtherHeap) + theWord (FAPPLY (stackSem_state_store s)
            HeapLength) in
          let len = theWord (FAPPLY (stackSem_state_store s)
            HeapLength) >>> backend_common_word_shift (:'a) in
          let (w1,i1,pa1,ib',pb',m1,c1) =
                   word_gen_gc_move conf
                     (FAPPLY (stackSem_state_store s) Globals,(n2w
                       0),theWord (FAPPLY (stackSem_state_store s)
                       OtherHeap),
                      len,new_end,theWord (FAPPLY
                        (stackSem_state_store s)
                        CurrHeap),stackSem_state_memory
                        s,stackSem_state_mdomain s) in
          let (ws2,i2,pa2,ib2,(pb2:'a word),m2,c2) =
                   word_gen_gc_move_roots_bitmaps conf
                     (stack',stackSem_state_bitmaps s,i1,pa1,ib',pb',
                      theWord (FAPPLY (stackSem_state_store s)
                        CurrHeap),m1,stackSem_state_mdomain s) in
          let (i3,pa3,ib3,pb3,m3,c3) =
                  word_gen_gc_move_loop conf (w2n len)
                    (theWord (FAPPLY (stackSem_state_store s)
                      OtherHeap),i2,pa2,ib2,pb2,new_end,
                     theWord (FAPPLY (stackSem_state_store s)
                       CurrHeap),m2,stackSem_state_mdomain s) in
          let s1 = stackSem_state_store
                  s |++
                  [(CurrHeap,wordLang_Word (theWord (FAPPLY
                    (stackSem_state_store s) OtherHeap)));
                   (OtherHeap,wordLang_Word (theWord (FAPPLY
                     (stackSem_state_store s) CurrHeap)));
                   (NextFree,wordLang_Word pa3);
                   (GenStart,wordLang_Word (pa3 + --(n2w 1) * theWord
                     (FAPPLY (stackSem_state_store s) OtherHeap)));
                   (TriggerGC,wordLang_Word (pa3 + new_trig
                      (pb3 - pa3) (theWord (FAPPLY
                        (stackSem_state_store s) AllocSize))
                        gen_sizes));
                   (EndOfHeap,wordLang_Word pb3);
                   (Globals,w1);
                   (GlobReal,glob_real conf (theWord (FAPPLY
                     (stackSem_state_store s) OtherHeap)) w1);
                   (Temp (n2w 0),wordLang_Word (n2w 0));
                   (Temp (n2w 1),wordLang_Word (n2w 0));
                   (Temp (n2w 2),wordLang_Word (n2w 0));
                   (Temp (n2w 3),wordLang_Word (n2w 0));
                   (Temp (n2w 4),wordLang_Word (n2w 0));
                   (Temp (n2w 5),wordLang_Word (n2w 0));
                   (Temp (n2w 6),wordLang_Word (n2w 0))] in
            if word_gc_fun_assum conf (stackSem_state_store s) /\
              c1 /\ c2 /\ c3 then SOME (stackSem_state_memory_fupd (K
              m3) (stackSem_state_regs_fupd (K FEMPTY)
              (stackSem_state_store_fupd (K s1)
              (stackSem_state_stack_fupd (K (unused ++ ws2)) s))))
              else NONE))`,
  CHEAT_TAC);;

let word_gen_gc_move_bitmaps_def = cake_define
  `word_gen_gc_move_bitmaps conf
  (w,stack',bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack' with NONE -> NONE | SOME
         (ts,ws) ->
         (let (wl,i2,pa2,ib2,pb2,m2,c2) =
                 word_gen_gc_move_roots conf
                   (ts,i1,pa1,ib1,pb1,curr,m,dm) in
           match map_bitmap bs wl stack' with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2))))`;;

let word_gen_gc_partial_move_bitmaps_def = cake_define
  `word_gen_gc_partial_move_bitmaps conf
  (w,stack',bitmaps,i1,pa1,curr,m,dm,gs,rs) =
     (match full_read_bitmap bitmaps w with NONE -> NONE | SOME bs ->
       (match filter_bitmap bs stack' with NONE -> NONE | SOME
         (ts,ws) ->
         (let (wl,i2,pa2,m2,c2) =
                 word_gen_gc_partial_move_roots conf
                   (ts,i1,pa1,curr,m,dm,gs,rs) in
           match map_bitmap bs wl stack' with NONE -> NONE | SOME
             (hd,ts1,ws') ->
               SOME (hd,ws,i2,pa2,m2,c2))))`;;

(* [local] *)
let word_gen_gc_move_roots_APPEND = prove
 (`!xs ys i1 pa1 ib1 pb1 m.
       word_gen_gc_move_roots conf (xs ++
         ys,i1,pa1,ib1,pb1,curr,m,dm) =
         (let (ws1,i1,pa1,ib1,pb1,m1,c1) =
           word_gen_gc_move_roots conf (xs,i1,pa1,ib1,pb1,curr,m,dm)
             in
         let (ws2,i2,pa2,ib2,pb2,m2,c2) =
           word_gen_gc_move_roots conf (ys,i1,pa1,ib1,pb1,curr,m1,dm)
             in
             (ws1 ++ ws2,i2,pa2,ib2,pb2,m2,(c1 /\ c2)))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_partial_move_roots_APPEND = prove
 (`!xs ys i1 pa1 ib1 pb1 m.
       word_gen_gc_partial_move_roots conf (xs ++
         ys,i1,pa1,curr,m,dm,gs,rs) =
         (let (ws1,i1,pa1,m1,c1) =
           word_gen_gc_partial_move_roots conf
             (xs,i1,pa1,curr,m,dm,gs,rs) in
         let (ws2,i2,pa2,m2,c2) =
           word_gen_gc_partial_move_roots conf
             (ys,i1,pa1,curr,m1,dm,gs,rs) in
             (ws1 ++ ws2,i2,pa2,m2,(c1 /\ c2)))`,
  CHEAT_TAC);;

let word_gen_gc_move_roots_IMP_LENGTH = prove
 (`!xs r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf ib2 pb2.
      word_gen_gc_move_roots conf (xs,r0,r1,r3,r4,curr,r2,dm) =
         (ys,i2,pa2,ib2,pb2,m2,c) ==>
      LENGTH ys = LENGTH xs`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_roots_IMP_LENGTH = prove
 (`!xs r0 r1 r3 r4 curr r2 dm ys i2 pa2 m2 c conf.
      word_gen_gc_partial_move_roots conf (xs,r0,r1,curr,r2,dm,r3,r4)
        =
         (ys,i2,pa2,m2,c) ==>
      LENGTH ys = LENGTH xs`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_move_roots_bitmaps = prove
 (`!stack' i1 pa1 m stack2 i2 pa2 m2.
       (word_gen_gc_move_roots_bitmaps conf
         (stack',bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
         (stack2,i2,pa2,ib2,pb2,m2,T)) ==>
       word_gen_gc_move_roots_bitmaps conf
         (stack',bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
       (match stack' with [] -> (ARB,ARB,ARB,ARB,ARB,ARB,F) | (w ::
         ws) ->
         (if w = wordLang_Word (n2w 0) then
           (stack',i1,pa1,ib1,pb1,m,(ws = [])) else
           match word_gen_gc_move_bitmaps conf
             (w,ws,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) with NONE ->
             (ARB,ARB,ARB,ARB,ARB,ARB,F) | SOME
             (new,stack',i2,pa2,ib2,pb2,m2,c2) ->
               (let (stack',i,pa,ib1,pb1,m,c3) =
                 word_gen_gc_move_roots_bitmaps conf
                   (stack',bitmaps,i2,pa2,ib2,pb2,curr,m2,dm) in
                     ((w :: new) ++ stack',i,pa,ib1,pb1,m,(c2 /\
                       c3)))))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_partial_move_roots_bitmaps = prove
 (`!stack' i1 pa1 m stack2 i2 pa2 m2.
       (word_gen_gc_partial_move_roots_bitmaps conf
         (stack',bitmaps,i1,pa1,curr,m,dm,gs,rs) =
           (stack2,i2,pa2,m2,T)) ==>
       word_gen_gc_partial_move_roots_bitmaps conf
         (stack',bitmaps,i1,pa1,curr,m,dm,gs,rs) =
       (match stack' with [] -> (ARB,ARB,ARB,ARB,F) | (w :: ws) ->
         (if w = wordLang_Word (n2w 0) then (stack',i1,pa1,m,(ws =
           [])) else
           match word_gen_gc_partial_move_bitmaps conf
             (w,ws,bitmaps,i1,pa1,curr,m,dm,gs,rs) with NONE ->
             (ARB,ARB,ARB,ARB,F) | SOME (new,stack',i2,pa2,m2,c2) ->
               (let (stack',i,pa,m,c3) =
                 word_gen_gc_partial_move_roots_bitmaps conf
                   (stack',bitmaps,i2,pa2,curr,m2,dm,gs,rs) in
                     ((w :: new) ++ stack',i,pa,m,(c2 /\ c3)))))`,
  CHEAT_TAC);;

let word_gen_gc_move_bitmap_def = cake_define
  `word_gen_gc_move_bitmap conf (w,stack',i1,pa1,ib1,pb1,curr,m,dm) =
     (let bs = get_bits w in
       match filter_bitmap bs stack' with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,ib2,pb2,m2,c2) =
            word_gen_gc_move_roots conf (ts,i1,pa1,ib1,pb1,curr,m,dm)
              in
            match map_bitmap bs wl stack' with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,ib2,pb2,m2,c2)))`;;

let word_gen_gc_partial_move_bitmap_def = cake_define
  `word_gen_gc_partial_move_bitmap conf
  (w,stack',i1,pa1,curr,m,dm,gs,rs) =
     (let bs = get_bits w in
       match filter_bitmap bs stack' with NONE -> NONE | SOME (ts,ws)
         ->
          (let (wl,i2,pa2,m2,c2) =
            word_gen_gc_partial_move_roots conf
              (ts,i1,pa1,curr,m,dm,gs,rs) in
            match map_bitmap bs wl stack' with NONE -> NONE | SOME
              (hd,v2) -> SOME (hd,ws,i2,pa2,m2,c2)))`;;

(* HOL4 stack_allocProofScript.sml:2225-2247: a theorem that HOL4
   states as the value of an ML expression: map_bitmap_APPEND_APPEND *)

(* HOL4 stack_allocProofScript.sml:2249-2251: the ML values that the
   definitions below antiquote *)

(* HOL4 stack_allocProofScript.sml:2253-2255: the ML values that the
   definitions below antiquote *)

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gen_gc_move_bitmaps_unroll = prove
 (cake_as_vars (fun () ->
    `word_gen_gc_move_bitmaps conf (wordLang_Word
  w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) = SOME x /\
       LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a)
         ==>
       word_gen_gc_move_bitmaps conf (wordLang_Word
         w,stack,bitmaps,i1,pa1,ib1,pb1,curr,m,dm) =
       (match DROP (w2n (w - ((n2w 1):'a word))) bitmaps with [] ->
         NONE | (y :: ys) ->
         (match word_gen_gc_move_bitmap conf
           (y,stack,i1,pa1,ib1,pb1,curr,m,dm) with NONE -> NONE | SOME
           (hd,ws,i2,pa2,ib2,pb2,m2,c2) ->
             (if ~(word_msb y) then SOME
               (hd,ws,i2,pa2,ib2,pb2,m2,c2) else
               match word_gen_gc_move_bitmaps conf (wordLang_Word
                 (w + (n2w 1)),ws,bitmaps,i2,pa2,ib2,pb2,curr,m2,dm)
                 with NONE -> NONE | SOME (hd3,ws3,i3,pa3,ib3,pb3,m3,c3)
                 ->
                   SOME (hd ++ hd3,ws3,i3,pa3,ib3,pb3,m3,(c2 /\
                     c3)))))`),
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gen_gc_partial_move_bitmaps_unroll = prove
 (cake_as_vars (fun () ->
    `word_gen_gc_partial_move_bitmaps conf
         (wordLang_Word w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
           SOME x /\
       LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a)
         ==>
       word_gen_gc_partial_move_bitmaps conf
         (wordLang_Word w,stack,bitmaps,i1,pa1,curr,m,dm,gs,rs) =
       (match DROP (w2n (w - ((n2w 1):'a word))) bitmaps with [] ->
         NONE | (y :: ys) ->
         (match word_gen_gc_partial_move_bitmap conf
           (y,stack,i1,pa1,curr,m,dm,gs,rs) with NONE -> NONE | SOME
           (hd,ws,i2,pa2,m2,c2) ->
             (if ~(word_msb y) then SOME (hd,ws,i2,pa2,m2,c2) else
               match word_gen_gc_partial_move_bitmaps conf
                      (wordLang_Word (w + (n2w
                        1)),ws,bitmaps,i2,pa2,curr,m2,dm,gs,rs) with
                        NONE -> NONE | SOME (hd3,ws3,i3,pa3,m3,c3) ->
                   SOME (hd ++ hd3,ws3,i3,pa3,m3,(c2 /\ c3)))))`),
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_move_bitmap_unroll = prove
 (`word_gen_gc_move_bitmap conf (w,stack',i1,pa1,ib1,pb1,curr,m,dm) =
     (if w = ((n2w 0):'a word) then SOME
       ([],stack',i1,pa1,ib1,pb1,m,T) else
     if w = (n2w 1) then SOME ([],stack',i1,pa1,ib1,pb1,m,T) else
       match stack' with [] -> NONE | (x :: xs) ->
         (if (w && (n2w 1)) = (n2w 0) then
           match word_gen_gc_move_bitmap conf (w >>>
             1,xs,i1,pa1,ib1,pb1,curr,m,dm) with NONE -> NONE | SOME
             (new,stack',i1,pa1,ib1,pb1,m,c) ->
               SOME (x :: new,stack',i1,pa1,ib1,pb1,m,c) else
           let (x1,i1,pa1,ib1,pb1,m1,c1) =
             word_gen_gc_move conf (x,i1,pa1,ib1,pb1,curr,m,dm) in
           match word_gen_gc_move_bitmap conf (w >>>
             1,xs,i1,pa1,ib1,pb1,curr,m1,dm) with NONE -> NONE | SOME
             (new,stack',i1,pa1,ib1,pb1,m,c) ->
               SOME (x1 :: new,stack',i1,pa1,ib1,pb1,m,(c1 /\ c))))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_partial_move_bitmap_unroll = prove
 (`word_gen_gc_partial_move_bitmap conf
  (w,stack',i1,pa1,curr,m,dm,gs,rs) =
     (if w = ((n2w 0):'a word) then SOME ([],stack',i1,pa1,m,T) else
     if w = (n2w 1) then SOME ([],stack',i1,pa1,m,T) else
       match stack' with [] -> NONE | (x :: xs) ->
         (if (w && (n2w 1)) = (n2w 0) then
           match word_gen_gc_partial_move_bitmap conf
                  (w >>> 1,xs,i1,pa1,curr,m,dm,gs,rs) with NONE ->
                    NONE | SOME (new,stack',i1,pa1,m,c) ->
               SOME (x :: new,stack',i1,pa1,m,c) else
           let (x1,i1,pa1,m1,c1) =
             word_gen_gc_partial_move conf (x,i1,pa1,curr,m,dm,gs,rs)
               in
           match word_gen_gc_partial_move_bitmap conf
                  (w >>> 1,xs,i1,pa1,curr,m1,dm,gs,rs) with NONE ->
                    NONE | SOME (new,stack',i1,pa1,m,c) ->
               SOME (x1 :: new,stack',i1,pa1,m,(c1 /\ c))))`,
  CHEAT_TAC);;

let word_gen_gc_move_code_thm = prove
 (`word_gen_gc_move conf (w,i,pa,ib,pb,old,m,dm) =
  (w1,i1,pa1,ib1,pb1,m1,T) /\
    shift_length conf < dimindex (:'a) /\ backend_common_word_shift
      (:'a) < dimindex (:'a) /\
    2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0) /\
    (!(w:'a word). w << backend_common_word_shift (:'a) = w *
      bytes_in_word) /\
    FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
      old) /\ stackSem_state_use_store s /\ stackSem_state_memory
    (s:('a,'c,'b)stackSem_state) = m /\ stackSem_state_mdomain s = dm
      /\
    0 IN FDOM (stackSem_state_regs s) /\
    1 IN FDOM (stackSem_state_regs s) /\
    2 IN FDOM (stackSem_state_regs s) /\
    get_var 3 s = SOME (wordLang_Word pa) /\
    get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
    get_var 5 s = SOME w /\
    (Temp (n2w 0)) IN FDOM (stackSem_state_store s) /\
    (Temp (n2w 1)) IN FDOM (stackSem_state_store s) /\
    FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
      (wordLang_Word pb) /\
    FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
      (wordLang_Word ib) /\
    1 IN FDOM (stackSem_state_regs s) /\
    2 IN FDOM (stackSem_state_regs s) /\
    6 IN FDOM (stackSem_state_regs s) ==>
    (?ck r0 r1 r2 r6 t0 t1.
      evaluate (word_gen_gc_move_code conf,stackSem_state_clock_fupd
        (K (stackSem_state_clock s + ck)) s) =
        (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s |++
          [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,w1);
                              (6,r6)])) (stackSem_state_store_fupd (K
                                (stackSem_state_store s |++ [(Temp (n2w
                                0),t0);
                              (Temp (n2w 1),t1);
                              (Temp (n2w 2),wordLang_Word pb1);
                              (Temp (n2w 3),wordLang_Word ib1)]))
                                (stackSem_state_memory_fupd (K m1)
                                s))))`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_code_thm = prove
 (`word_gen_gc_partial_move conf (w,i,pa,old,m,dm,gs,rs) =
  (w1,i1,pa1,m1,T) /\
    shift_length conf < dimindex (:'a) /\ backend_common_word_shift
      (:'a) < dimindex (:'a) /\
    2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0) /\
    (!(w:'a word). w << backend_common_word_shift (:'a) = w *
      bytes_in_word) /\
    FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
      old) /\ stackSem_state_use_store (s:('a,'c,'b)stackSem_state) /\
      stackSem_state_memory
    s = m /\ stackSem_state_mdomain s = dm /\ good_dimindex (:'a) /\
    0 IN FDOM (stackSem_state_regs s) /\
    1 IN FDOM (stackSem_state_regs s) /\
    2 IN FDOM (stackSem_state_regs s) /\
    get_var 3 s = SOME (wordLang_Word pa) /\
    get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
    get_var 5 s = SOME w /\
    FLOOKUP (stackSem_state_store s) (Temp (n2w 0)) = SOME
      (wordLang_Word gs) /\
    FLOOKUP (stackSem_state_store s) (Temp (n2w 1)) = SOME
      (wordLang_Word rs) /\
    1 IN FDOM (stackSem_state_regs s) /\
    2 IN FDOM (stackSem_state_regs s) /\
    6 IN FDOM (stackSem_state_regs s) ==>
    (?ck r0 r1 r2 r6.
      evaluate (word_gen_gc_partial_move_code
        conf,stackSem_state_clock_fupd (K (stackSem_state_clock s + ck))
        s) =
        (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s |++
          [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,w1);
                              (6,r6)])) (stackSem_state_memory_fupd
                                (K m1) s)))`,
  CHEAT_TAC);;

let word_gen_gc_move_bitmap_code_thm = prove
 (`!w stack' (s:('a,'c,'b)stackSem_state) i pa ib pb curr m dm new
  stack1
    a1 i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_move_bitmap conf (w,stack',i,pa,ib,pb,curr,m,dm) =
        SOME (new,stack1,i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\ good_dimindex (:'a) /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        curr) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
        stackSem_state_use_stack s /\
      0 IN FDOM (stackSem_state_regs s) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) /\
      6 IN FDOM (stackSem_state_regs s) /\
      get_var 7 s = SOME (wordLang_Word w) /\
      get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w (LENGTH
        old))) /\
      Temp (n2w 0) IN FDOM (stackSem_state_store s) /\
      Temp (n2w 1) IN FDOM (stackSem_state_store s) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
        (wordLang_Word pb) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
        (wordLang_Word ib) /\ stackSem_state_stack
      s = init ++ old ++ stack' /\ stackSem_state_stack_space
      s = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
        dimword (:'a) ==>
      (?ck r0 r1 r2 r5 r6 r7 t0 t1.
        evaluate (word_gen_gc_move_bitmap_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                      (8,wordLang_Word (bytes_in_word * n2w (LENGTH
                        (old ++ new))))])) (stackSem_state_store_fupd (K
                        (stackSem_state_store
                            s |++
                            [(Temp (n2w 0),t0); (Temp (n2w 1),t1);
                              (Temp (n2w 2),wordLang_Word pb1);
                             (Temp (n2w 3),wordLang_Word ib1)]))
                               (stackSem_state_stack_fupd (K (init ++
                               old ++ new ++ stack1))
                               (stackSem_state_memory_fupd (K m1)
                               s)))))`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_bitmap_code_thm = prove
 (`!w stack' (s:('a,'c,'b)stackSem_state) i pa curr m dm new stack1 a1
  i1 pa1 m1 old.
      word_gen_gc_partial_move_bitmap conf
        (w,stack',i,pa,curr,m,dm,gs,rs) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\ good_dimindex (:'a) /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        curr) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
        stackSem_state_use_stack s /\
      0 IN FDOM (stackSem_state_regs s) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) /\
      6 IN FDOM (stackSem_state_regs s) /\
      get_var 7 s = SOME (wordLang_Word w) /\
      get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w (LENGTH
        old))) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 0)) = SOME
        (wordLang_Word gs) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 1)) = SOME
        (wordLang_Word rs) /\ stackSem_state_stack
      s = init ++ old ++ stack' /\ stackSem_state_stack_space
      s = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
        dimword (:'a) ==>
      (?ck r0 r1 r2 r5 r6 r7.
        evaluate (word_gen_gc_partial_move_bitmap_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck))
          s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                      (8,wordLang_Word (bytes_in_word * n2w (LENGTH
                        (old ++ new))))])) (stackSem_state_stack_fupd
                        (K (init ++ old ++ new ++ stack1))
                        (stackSem_state_memory_fupd (K m1) s))))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gen_gc_move_bitmaps_LENGTH = prove
 (cake_as_vars (fun () ->
    `word_gen_gc_move_bitmaps conf
  (w,stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
         SOME (xs,stack1,i1,pa1,ib1,pb1,m1,T) ==>
      LENGTH stack = LENGTH xs + LENGTH stack1`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gen_gc_partial_move_bitmaps_LENGTH = prove
 (cake_as_vars (fun () ->
    `word_gen_gc_partial_move_bitmaps conf
  (w,stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
         SOME (xs,stack1,i1,pa1,m1,T) ==>
      LENGTH stack = LENGTH xs + LENGTH stack1`),
  CHEAT_TAC);;

let word_gen_gc_move_bitmaps_code_thm = prove
 (`!w bitmaps z stack' (s:('a,'c,'b)stackSem_state) i pa ib pb curr m dm
  new
         stack1 a1 i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_move_bitmaps conf (wordLang_Word
        w,stack',bitmaps,i,pa,ib,pb,curr,m,dm) =
        SOME (new,stack1,i1,pa1,ib1,pb1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\ good_dimindex (:'a) /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        curr) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
        stackSem_state_bitmaps s = bitmaps /\ stackSem_state_use_stack s
        /\
      get_var 0 s = SOME (wordLang_Word z) /\ ~(z = (n2w 0)) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) /\
      6 IN FDOM (stackSem_state_regs s) /\
      7 IN FDOM (stackSem_state_regs s) /\
      get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w (LENGTH
        old))) /\
      get_var 9 s = SOME (wordLang_Word (w - (n2w 1))) /\
      Temp (n2w 0) IN FDOM (stackSem_state_store s) /\
      Temp (n2w 1) IN FDOM (stackSem_state_store s) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
        (wordLang_Word pb) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
        (wordLang_Word ib) /\ stackSem_state_stack
      s = init ++ old ++ stack' /\ stackSem_state_stack_space
      s = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
        dimword (:'a) ==>
      (?ck r0 r1 r2 r5 r6 r7 r9 t0 t1.
        evaluate (word_gen_gc_move_bitmaps_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                      (8,wordLang_Word (bytes_in_word * n2w (LENGTH
                        (old ++ new))));
                              (9,r9)])) (stackSem_state_store_fupd (K
                                (stackSem_state_store
                            s |++
                            [(Temp (n2w 0),t0); (Temp (n2w 1),t1);
                              (Temp (n2w 2),wordLang_Word pb1);
                             (Temp (n2w 3),wordLang_Word ib1)]))
                               (stackSem_state_clock_fupd (K
                               (stackSem_state_clock s))
                               (stackSem_state_stack_fupd (K (init ++
                               old ++ new ++ stack1))
                               (stackSem_state_memory_fupd (K m1)
                               s))))))`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_bitmaps_code_thm = prove
 (`!w bitmaps z stack' (s:('a,'c,'b)stackSem_state) i pa ib pb curr m dm
  new
         stack1 a1 i1 pa1 ib1 pb1 m1 old.
      word_gen_gc_partial_move_bitmaps conf
          (wordLang_Word w,stack',bitmaps,i,pa,curr,m,dm,gs,rs) =
        SOME (new,stack1,i1,pa1,m1,T) /\
      LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\ good_dimindex (:'a) /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        curr) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
        stackSem_state_bitmaps s = bitmaps /\ stackSem_state_use_stack s
        /\
      get_var 0 s = SOME (wordLang_Word z) /\ ~(z = (n2w 0)) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) /\
      6 IN FDOM (stackSem_state_regs s) /\
      7 IN FDOM (stackSem_state_regs s) /\
      get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w (LENGTH
        old))) /\
      get_var 9 s = SOME (wordLang_Word (w - (n2w 1))) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 0)) = SOME
        (wordLang_Word gs) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 1)) = SOME
        (wordLang_Word rs) /\ stackSem_state_stack
      s = init ++ old ++ stack' /\ stackSem_state_stack_space
      s = LENGTH init /\
      (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
        dimword (:'a) ==>
      (?ck r0 r1 r2 r5 r6 r7 r9 t0 t1.
        evaluate (word_gen_gc_partial_move_bitmaps_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                      (8,wordLang_Word (bytes_in_word * n2w (LENGTH
                        (old ++ new))));
                              (9,r9)])) (stackSem_state_clock_fupd
                                (K (stackSem_state_clock s))
                                (stackSem_state_stack_fupd (K (init ++
                                old ++ new ++ stack1))
                                (stackSem_state_memory_fupd (K m1)
                                s)))))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gen_gc_move_roots_bitmaps_code_thm = prove
 (cake_as_vars (fun () ->
    `!bitmaps (s:('a,'c,'b)stackSem_state) i pa ib pb curr m dm new
           stack1 a1 i1 pa1 ib1 pb1 m1 old.
        word_gen_gc_move_roots_bitmaps conf
          (stack,bitmaps,i,pa,ib,pb,curr,m,dm) =
          (stack1,i1,pa1,ib1,pb1,m1,T) /\
        LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a)
          /\
        shift_length conf < dimindex (:'a) /\
          backend_common_word_shift (:'a) < dimindex (:'a) /\
        2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf =
          0) /\ good_dimindex (:'a) /\
        (!(w:'a word). w << backend_common_word_shift (:'a) = w *
          bytes_in_word) /\
        FLOOKUP (stackSem_state_store s) CurrHeap = SOME
          (wordLang_Word curr) /\ stackSem_state_use_store s /\
          stackSem_state_memory
        s = m /\ stackSem_state_mdomain s = dm /\
          stackSem_state_bitmaps s = bitmaps /\ stackSem_state_use_stack
          s /\
        0 IN FDOM (stackSem_state_regs s) /\
        1 IN FDOM (stackSem_state_regs s) /\
        2 IN FDOM (stackSem_state_regs s) /\
        get_var 3 s = SOME (wordLang_Word pa) /\
        get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
        5 IN FDOM (stackSem_state_regs s) /\
        6 IN FDOM (stackSem_state_regs s) /\
        7 IN FDOM (stackSem_state_regs s) /\
        get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w
          (LENGTH old))) /\
        get_var 9 s = SOME (HD stack) /\
        Temp (n2w 0) IN FDOM (stackSem_state_store s) /\
        Temp (n2w 1) IN FDOM (stackSem_state_store s) /\
        FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
          (wordLang_Word pb) /\
        FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
          (wordLang_Word ib) /\ stackSem_state_stack
        s = init ++ old ++ stack /\ stackSem_state_stack_space
        s = LENGTH init /\
        (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
          dimword (:'a) ==>
        (?ck r0 r1 r2 r5 r6 r7 r8 r9 t0 t1.
          evaluate (word_gen_gc_move_roots_bitmaps_code
            conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
            ck))
              s) =
            (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs
              s |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,r8);
                              (9,wordLang_Word (n2w 0))]))
                                (stackSem_state_store_fupd (K
                                (stackSem_state_store
                              s |++
                              [(Temp (n2w 0),t0); (Temp (n2w
                                1),t1); (Temp (n2w 2),wordLang_Word
                                pb1);
                              (Temp (n2w 3),wordLang_Word ib1)]))
                                (stackSem_state_clock_fupd (K
                                (stackSem_state_clock s))
                                (stackSem_state_stack_fupd (K (init ++
                                old ++ stack1))
                                (stackSem_state_memory_fupd (K m1)
                                s))))))`),
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let word_gen_gc_partial_move_roots_bitmaps_code_thm = prove
 (cake_as_vars (fun () ->
    `!bitmaps (s:('a,'c,'b)stackSem_state) i pa curr m dm new
           stack1 a1 i1 pa1 m1 old.
        word_gen_gc_partial_move_roots_bitmaps conf
          (stack,bitmaps,i,pa,curr,m,dm,gs,rs) =
          (stack1,i1,pa1,m1,T) /\
        LENGTH bitmaps < dimword (:'a) - 1 /\ good_dimindex (:'a)
          /\
        shift_length conf < dimindex (:'a) /\
          backend_common_word_shift (:'a) < dimindex (:'a) /\
        2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf =
          0) /\ good_dimindex (:'a) /\
        (!(w:'a word). w << backend_common_word_shift (:'a) = w *
          bytes_in_word) /\
        FLOOKUP (stackSem_state_store s) CurrHeap = SOME
          (wordLang_Word curr) /\ stackSem_state_use_store s /\
          stackSem_state_memory
        s = m /\ stackSem_state_mdomain s = dm /\
          stackSem_state_bitmaps s = bitmaps /\ stackSem_state_use_stack
          s /\
        0 IN FDOM (stackSem_state_regs s) /\
        1 IN FDOM (stackSem_state_regs s) /\
        2 IN FDOM (stackSem_state_regs s) /\
        get_var 3 s = SOME (wordLang_Word pa) /\
        get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
        5 IN FDOM (stackSem_state_regs s) /\
        6 IN FDOM (stackSem_state_regs s) /\
        7 IN FDOM (stackSem_state_regs s) /\
        get_var 8 s = SOME (wordLang_Word (bytes_in_word * n2w
          (LENGTH old))) /\
        get_var 9 s = SOME (HD stack) /\
        FLOOKUP (stackSem_state_store s) (Temp (n2w 0)) = SOME
          (wordLang_Word gs) /\
        FLOOKUP (stackSem_state_store s) (Temp (n2w 1)) = SOME
          (wordLang_Word rs) /\ stackSem_state_stack
        s = init ++ old ++ stack /\ stackSem_state_stack_space
        s = LENGTH init /\
        (dimindex (:'a) DIV 8) * LENGTH (stackSem_state_stack s) <
          dimword (:'a) ==>
        (?ck r0 r1 r2 r5 r6 r7 r8 r9.
          evaluate (word_gen_gc_partial_move_roots_bitmaps_code
            conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
            ck))
              s) =
            (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs
              s |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,r8);
                              (9,wordLang_Word (n2w 0))]))
                                (stackSem_state_clock_fupd (K
                                (stackSem_state_clock s))
                                (stackSem_state_stack_fupd (K (init ++
                                old ++ stack1))
                                (stackSem_state_memory_fupd (K m1)
                                s)))))`),
  CHEAT_TAC);;

let word_gen_gc_move_list_code_thm = prove
 (`!l a (s:('a,'c,'b)stackSem_state) pa1 pa old m1 m i1 i dm conf a1 ib
  ib1 pb pb1.
      word_gen_gc_move_list conf ((a:'a word),l,i,pa,ib,pb,old,m,dm)
        =
         (a1,i1,pa1,ib1,pb1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        old) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\
      Temp (n2w 0) IN FDOM (stackSem_state_store s) /\
      Temp (n2w 1) IN FDOM (stackSem_state_store s) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
        (wordLang_Word pb) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
        (wordLang_Word ib) /\
      0 IN FDOM (stackSem_state_regs s) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) ==>
      6 IN FDOM (stackSem_state_regs s) ==>
      get_var 7 s = SOME (wordLang_Word l) /\
      get_var 8 s = SOME (wordLang_Word a) ==>
      (?ck r0 r1 r2 r5 r6 t0 t1.
        evaluate (word_gen_gc_move_list_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,wordLang_Word (n2w 0));
                              (8,wordLang_Word a1)]))
                                (stackSem_state_store_fupd (K
                                (stackSem_state_store
                            s |++
                            [(Temp (n2w 0),t0); (Temp (n2w 1),t1);
                              (Temp (n2w 2),wordLang_Word pb1);
                             (Temp (n2w 3),wordLang_Word ib1)]))
                               (stackSem_state_memory_fupd (K m1)
                               s))))`,
  CHEAT_TAC);;

let word_gen_gc_partial_move_list_code_thm = prove
 (`!l a (s:('a,'c,'b)stackSem_state) pa1 pa old m1 m i1 i dm conf a1 gs
  rs.
      word_gen_gc_partial_move_list conf ((a:'a
        word),l,i,pa,old,m,dm,gs,rs) =
         (a1,i1,pa1,m1,T) /\
      shift_length conf < dimindex (:'a) /\ backend_common_word_shift
        (:'a) < dimindex (:'a) /\
      2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
        /\
      (!(w:'a word). w << backend_common_word_shift (:'a) = w *
        bytes_in_word) /\
      FLOOKUP (stackSem_state_store s) CurrHeap = SOME (wordLang_Word
        old) /\ stackSem_state_use_store s /\ stackSem_state_memory
      s = m /\ stackSem_state_mdomain s = dm /\ good_dimindex (:'a)
        /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 0)) = SOME
        (wordLang_Word gs) /\
      FLOOKUP (stackSem_state_store s) (Temp (n2w 1)) = SOME
        (wordLang_Word rs) /\
      0 IN FDOM (stackSem_state_regs s) /\
      1 IN FDOM (stackSem_state_regs s) /\
      2 IN FDOM (stackSem_state_regs s) /\
      get_var 3 s = SOME (wordLang_Word pa) /\
      get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
      5 IN FDOM (stackSem_state_regs s) ==>
      6 IN FDOM (stackSem_state_regs s) ==>
      get_var 7 s = SOME (wordLang_Word l) /\
      get_var 8 s = SOME (wordLang_Word a) ==>
      (?ck r0 r1 r2 r5 r6.
        evaluate (word_gen_gc_partial_move_list_code
          conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
          ck)) s) =
          (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
            |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,wordLang_Word (n2w 0));
                              (8,wordLang_Word a1)]))
                                (stackSem_state_memory_fupd (K m1)
                                s)))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_partial_move_ref_list_code_thm = prove
 (`!k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2
  (s:('a,'c,'b)stackSem_state).
       word_gen_gc_partial_move_ref_list k conf
         (r1a1,i1,pa1,old1,m1,dm1,T,gs,rs,r2a1) =
         (i2,pa2,m2,T) /\
       shift_length conf < dimindex (:'a) /\
         backend_common_word_shift (:'a) < dimindex (:'a) /\
       2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
         /\ data_to_word_config_len_size
       conf + 2 < dimindex (:'a) /\ good_dimindex (:'a) /\
       (!(w:'a word). w << backend_common_word_shift (:'a) = w *
         bytes_in_word) /\
       FLOOKUP (stackSem_state_store s) CurrHeap = SOME
         (wordLang_Word old1) /\ stackSem_state_use_store s /\
         stackSem_state_memory
       s = m1 /\ stackSem_state_mdomain s = dm1 /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 0)) = SOME
         (wordLang_Word gs) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 1)) = SOME
         (wordLang_Word rs) /\
       0 IN FDOM (stackSem_state_regs s) /\
       1 IN FDOM (stackSem_state_regs s) /\
       2 IN FDOM (stackSem_state_regs s) /\
       get_var 3 s = SOME (wordLang_Word pa1) /\
       get_var 4 s = SOME (wordLang_Word (i1:'a word)) /\
       5 IN FDOM (stackSem_state_regs s) /\
       6 IN FDOM (stackSem_state_regs s) /\
       7 IN FDOM (stackSem_state_regs s) /\
       get_var 8 s = SOME (wordLang_Word r1a1) /\
       get_var 9 s = SOME (wordLang_Word r2a1) ==>
       (?ck r0 r1 r2 r5 r6 r7 r8 r9.
         evaluate (word_gen_gc_partial_move_ref_list_code
           conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
           ck)) s) =
           (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
             |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa2);
                              (4,wordLang_Word i2);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,r8);
                              (9,r9)])) (stackSem_state_memory_fupd
                                (K m2) s)))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_move_data_code_thm = prove
 (`!k ha1 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2
  (s:('a,'c,'b)stackSem_state).
       word_gen_gc_move_data conf k (ha1,i1,pa1,ib1,pb1,old1,m1,dm1)
         =
         (i2,pa2,ib2,pb2,m2,T) /\
       shift_length conf < dimindex (:'a) /\
         backend_common_word_shift (:'a) < dimindex (:'a) /\
       2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
         /\ data_to_word_config_len_size
       conf + 2 < dimindex (:'a) /\
       (!(w:'a word). w << backend_common_word_shift (:'a) = w *
         bytes_in_word) /\
       FLOOKUP (stackSem_state_store s) CurrHeap = SOME
         (wordLang_Word old1) /\ stackSem_state_use_store s /\
         stackSem_state_memory
       s = m1 /\ stackSem_state_mdomain s = dm1 /\
       Temp (n2w 0) IN FDOM (stackSem_state_store s) /\
       Temp (n2w 1) IN FDOM (stackSem_state_store s) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
         (wordLang_Word pb1) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
         (wordLang_Word ib1) /\
       0 IN FDOM (stackSem_state_regs s) /\
       1 IN FDOM (stackSem_state_regs s) /\
       2 IN FDOM (stackSem_state_regs s) /\
       get_var 3 s = SOME (wordLang_Word pa1) /\
       get_var 4 s = SOME (wordLang_Word (i1:'a word)) /\
       5 IN FDOM (stackSem_state_regs s) ==>
       6 IN FDOM (stackSem_state_regs s) ==>
       7 IN FDOM (stackSem_state_regs s) ==>
       get_var 8 s = SOME (wordLang_Word ha1) /\ c1 ==>
       (?ck r0 r1 r2 r5 r6 r7 t0 t1.
         evaluate (word_gen_gc_move_data_code
           conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
           ck)) s) =
           (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
             |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa2);
                              (4,wordLang_Word i2);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,wordLang_Word pa2)]))
                                (stackSem_state_store_fupd (K
                                (stackSem_state_store
                             s |++
                             [(Temp (n2w 0),t0); (Temp (n2w 1),t1);
                               (Temp (n2w 2),wordLang_Word pb2);
                              (Temp (n2w 3),wordLang_Word ib2)]))
                                (stackSem_state_memory_fupd (K m2)
                                s))))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_partial_move_data_code_thm = prove
 (`!k ha1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 (s:('a,'c,'b)stackSem_state).
       word_gen_gc_partial_move_data conf k
         (ha1,i1,pa1,old1,m1,dm1,gs,rs) =
         (i2,pa2,m2,T) /\
       shift_length conf < dimindex (:'a) /\
         backend_common_word_shift (:'a) < dimindex (:'a) /\
       2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
         /\ data_to_word_config_len_size
       conf + 2 < dimindex (:'a) /\
       (!(w:'a word). w << backend_common_word_shift (:'a) = w *
         bytes_in_word) /\
       FLOOKUP (stackSem_state_store s) CurrHeap = SOME
         (wordLang_Word old1) /\ stackSem_state_use_store s /\
         stackSem_state_memory
       s = m1 /\ stackSem_state_mdomain s = dm1 /\ good_dimindex
         (:'a) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 0)) = SOME
         (wordLang_Word gs) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 1)) = SOME
         (wordLang_Word rs) /\
       0 IN FDOM (stackSem_state_regs s) /\
       1 IN FDOM (stackSem_state_regs s) /\
       2 IN FDOM (stackSem_state_regs s) /\
       get_var 3 s = SOME (wordLang_Word pa1) /\
       get_var 4 s = SOME (wordLang_Word (i1:'a word)) /\
       5 IN FDOM (stackSem_state_regs s) ==>
       6 IN FDOM (stackSem_state_regs s) ==>
       7 IN FDOM (stackSem_state_regs s) ==>
       get_var 8 s = SOME (wordLang_Word ha1) /\ c1 ==>
       (?ck r0 r1 r2 r5 r6 r7 t0 t1.
         evaluate (word_gen_gc_partial_move_data_code
           conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
           ck)) s) =
           (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
             |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa2);
                              (4,wordLang_Word i2);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,wordLang_Word pa2)]))
                                (stackSem_state_memory_fupd (K m2)
                                s)))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_move_refs_code_thm = prove
 (`!k r2a1 r1a1 r2a2 i1 pa1 ib1 pb1 old1 m1 dm1 c1 i2 pa2 ib2 pb2 m2
  (s:('a,'c,'b)stackSem_state).
       word_gen_gc_move_refs conf k
         (r2a1,r1a1,i1,pa1,ib1,pb1,old1,m1,dm1) =
         (r2a2,i2,pa2,ib2,pb2,m2,T) /\
       shift_length conf < dimindex (:'a) /\
         backend_common_word_shift (:'a) < dimindex (:'a) /\
       2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
         /\ data_to_word_config_len_size
       conf + 2 < dimindex (:'a) /\
       (!(w:'a word). w << backend_common_word_shift (:'a) = w *
         bytes_in_word) /\
       FLOOKUP (stackSem_state_store s) CurrHeap = SOME
         (wordLang_Word old1) /\ stackSem_state_use_store s /\
         stackSem_state_memory
       s = m1 /\ stackSem_state_mdomain s = dm1 /\
       Temp (n2w 0) IN FDOM (stackSem_state_store s) /\
       Temp (n2w 1) IN FDOM (stackSem_state_store s) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
         (wordLang_Word pb1) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
         (wordLang_Word ib1) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 4)) = SOME
         (wordLang_Word r1a1) /\
       get_var 0 s = SOME (wordLang_Word r1a1) /\
       1 IN FDOM (stackSem_state_regs s) /\
       2 IN FDOM (stackSem_state_regs s) /\
       get_var 3 s = SOME (wordLang_Word pa1) /\
       get_var 4 s = SOME (wordLang_Word (i1:'a word)) /\
       5 IN FDOM (stackSem_state_regs s) ==>
       6 IN FDOM (stackSem_state_regs s) ==>
       7 IN FDOM (stackSem_state_regs s) ==>
       get_var 8 s = SOME (wordLang_Word r2a1) /\ c1 ==>
       (?ck r1 r2 r5 r6 r7 t0 t1.
         evaluate (word_gen_gc_move_refs_code
           conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
           ck)) s) =
           (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
             |++ [(0,wordLang_Word r1a1);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa2);
                              (4,wordLang_Word i2);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,wordLang_Word r2a2)]))
                                (stackSem_state_store_fupd (K
                                (stackSem_state_store
                             s |++
                             [(Temp (n2w 0),t0); (Temp (n2w 1),t1);
                               (Temp (n2w 2),wordLang_Word pb2);
                              (Temp (n2w 3),wordLang_Word ib2)]))
                                (stackSem_state_memory_fupd (K m2)
                                s))))`,
  CHEAT_TAC);;

(* [local] *)
let word_gen_gc_move_loop_code_thm = prove
 (`!k pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt
  (s:('a,'c,'b)stackSem_state).
       word_gen_gc_move_loop conf k (pax,i,pa,ib,pb,pbx,old,m,dm) =
           (i1,pa1,ib1,pb1,m1,T) /\
       shift_length conf < dimindex (:'a) /\
         backend_common_word_shift (:'a) < dimindex (:'a) /\
       2 < dimindex (:'a) /\ ~(data_to_word_config_len_size conf = 0)
         /\ data_to_word_config_len_size
       conf + 2 < dimindex (:'a) /\
       (!(w:'a word). w << backend_common_word_shift (:'a) = w *
         bytes_in_word) /\
       FLOOKUP (stackSem_state_store s) CurrHeap = SOME
         (wordLang_Word old) /\ stackSem_state_use_store s /\
         stackSem_state_memory
       s = m /\ stackSem_state_mdomain s = dm /\
       (tt = (n2w 0) <=> pbx = pb /\ pax = pa) /\
       Temp (n2w 0) IN FDOM (stackSem_state_store s) /\
       Temp (n2w 1) IN FDOM (stackSem_state_store s) /\
       Temp (n2w 5) IN FDOM (stackSem_state_store s) /\
       Temp (n2w 6) IN FDOM (stackSem_state_store s) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 2)) = SOME
         (wordLang_Word pb) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 3)) = SOME
         (wordLang_Word ib) /\
       FLOOKUP (stackSem_state_store s) (Temp (n2w 4)) = SOME
         (wordLang_Word pbx) /\
       0 IN FDOM (stackSem_state_regs s) /\
       get_var 1 s = SOME (wordLang_Word pbx) /\
       get_var 2 s = SOME (wordLang_Word pb) /\
       get_var 3 s = SOME (wordLang_Word pa) /\
       get_var 4 s = SOME (wordLang_Word (i:'a word)) /\
       get_var 7 s = SOME (wordLang_Word tt) /\
       get_var 8 s = SOME (wordLang_Word pax) /\
       5 IN FDOM (stackSem_state_regs s) /\
       6 IN FDOM (stackSem_state_regs s) /\ c1 ==>
       (?ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6.
         evaluate (word_gen_gc_move_loop_code
           conf,stackSem_state_clock_fupd (K (stackSem_state_clock s +
           ck)) s) =
           (NONE,stackSem_state_regs_fupd (K (stackSem_state_regs s
             |++ [(0,r0);
                              (1,r1);
                              (2,r2);
                              (3,wordLang_Word pa1);
                              (4,wordLang_Word i1);
                              (5,r5);
                              (6,r6);
                              (7,r7);
                              (8,r8)])) (stackSem_state_store_fupd (K
                                (stackSem_state_store
                             s |++
                             [(Temp (n2w 0),t0); (Temp (n2w 1),t1);
                               (Temp (n2w 2),wordLang_Word pb1);
                              (Temp (n2w 3),wordLang_Word ib1);
                              (Temp (n2w 4),t4); (Temp (n2w 5),t5);
                                (Temp (n2w 6),t6)]))
                                (stackSem_state_memory_fupd (K m1)
                                s))))`,
  CHEAT_TAC);;

(* [local] *)
let word_sub_0_eq = prove
 (`((--(n2w 1) * w + v = (n2w 0)) <=> w = v) /\
   ((v + --(n2w 1) * w = (n2w 0)) <=> w = v)`,
  CHEAT_TAC);;

let good_dimindex_byte_aligned_eq = prove
 (`good_dimindex (:'a) ==>
    (byte_aligned (w:'a word) <=>
     ((w && (if dimindex (:'a) = 32 then (n2w 3) else (n2w 7))) =
       (n2w 0)))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_SetNewTrigger = prove
 (`evaluate (SetNewTrigger endh_reg ib_reg gen_sizes,s5) = (res,new_s)
  ==>
   (!ib endh w.
     good_dimindex (:'a) /\ stackSem_state_use_store s5 /\
     ALL_DISTINCT [1; 4; 7; ib_reg; endh_reg] /\
     FLOOKUP (stackSem_state_regs s5) ib_reg = SOME (wordLang_Word
       ib) /\
     FLOOKUP (stackSem_state_regs s5) endh_reg = SOME (wordLang_Word
       endh) /\
     FLOOKUP (state_store s5) AllocSize = SOME (wordLang_Word (w:'a
       word)) ==>
     (?r7 r1 r4.
       res = NONE /\
       new_s = state_store_fupd (K (state_store s5 |+ (TriggerGC,
                            wordLang_Word ((ib + new_trig (endh -
                              ib) w gen_sizes)))))
                              (stackSem_state_regs_fupd (K
                              (stackSem_state_regs s5 |+ (1,r1) |+
                              (7,r7) |+ (4,r4))) s5)))`,
  CHEAT_TAC);;

let alloc_correct_lemma_Generational = prove
 (`alloc w (s:('a,'c,'b)stackSem_state) = (r,t) /\ ~(r = SOME Error) /\
  stackSem_state_gc_fun
    s = word_gc_fun conf /\ data_to_word_config_gc_kind conf =
      (data_to_word_Generational gen_sizes) /\
    LENGTH (stackSem_state_bitmaps s) < dimword (:'a) - 1 /\
    LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
      dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (wordLang_Word w) ==>
    (?ck l2.
      evaluate
        (word_gc_code conf,stackSem_state_code_fupd (K (fromAList
          (compile c (toAList (stackSem_state_code s)))))
          (stackSem_state_gc_fun_fupd (K anything)
          (stackSem_state_regs_fupd (K l) (stackSem_state_clock_fupd (K
          (stackSem_state_clock s + ck)) (stackSem_state_use_alloc_fupd
          (K F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         s))))))) =
        (r,state_gc_fun_fupd (K anything) (stackSem_state_regs_fupd
          (K l2) (state_code_fupd (K (fromAList (compile c (toAList
          (stackSem_state_code s))))) (stackSem_state_use_alloc_fupd (K
          F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         t)))))) /\
       (~(r = NONE) ==> r = SOME (Halt (wordLang_Word (n2w 1)))) /\
         stackSem_state_regs
       t SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret))`,
  CHEAT_TAC);;

(* gc_kind = None *)

(* [local] *)
let filter_bitmap_map_bitmap_IMP = prove
 (`!x ws q r x' q' q'' r''.
     filter_bitmap x ws = SOME (q,r) /\
     map_bitmap x (q ++ x') ws = SOME (q',q'',r'') ==>
     q'' = x' /\ r = r'' /\ ws = q' ++ r`,
  CHEAT_TAC);;

(* [local] *)
let enc_dec_stack = prove
 (`!bs ys2 x1 x2.
     enc_stack bs ys2 = SOME x1 /\
     dec_stack bs x1 ys2 = SOME x2 ==>
     (ys2 = x2)`,
  CHEAT_TAC);;

let alloc_correct_lemma_None = prove
 (`alloc w (s:('a,'c,'b)stackSem_state) = (r,t) /\ ~(r = SOME Error) /\
  stackSem_state_gc_fun
    s = word_gc_fun conf /\ data_to_word_config_gc_kind conf = None
      /\
    LENGTH (stackSem_state_bitmaps s) < dimword (:'a) - 1 /\
    LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
      dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (wordLang_Word w) ==>
    (?ck l2.
      evaluate
        (word_gc_code conf,stackSem_state_code_fupd (K (fromAList
          (compile c (toAList (stackSem_state_code s)))))
          (stackSem_state_gc_fun_fupd (K anything)
          (stackSem_state_regs_fupd (K l) (stackSem_state_clock_fupd (K
          (stackSem_state_clock s + ck)) (stackSem_state_use_alloc_fupd
          (K F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         s))))))) =
        (r,state_gc_fun_fupd (K anything) (stackSem_state_regs_fupd
          (K l2) (state_code_fupd (K (fromAList (compile c (toAList
          (stackSem_state_code s))))) (stackSem_state_use_alloc_fupd (K
          F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         t)))))) /\
       (~(r = NONE) ==> r = SOME (Halt (wordLang_Word (n2w 1)))) /\
         stackSem_state_regs
       t SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret))`,
  CHEAT_TAC);;

(* --- *)

let alloc_correct_lemma = prove
 (`alloc w (s:('a,'c,'b)stackSem_state) = (r,t) /\ ~(r = SOME Error) /\
  stackSem_state_gc_fun
    s = word_gc_fun conf /\
    LENGTH (stackSem_state_bitmaps s) < dimword (:'a) - 1 /\
    LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
      dimword (:'a) /\
    FLOOKUP l 0 = SOME ret /\
    FLOOKUP l 1 = SOME (wordLang_Word w) ==>
    (?ck l2.
      evaluate
        (word_gc_code conf,stackSem_state_code_fupd (K (fromAList
          (compile c (toAList (stackSem_state_code s)))))
          (stackSem_state_gc_fun_fupd (K anything)
          (stackSem_state_regs_fupd (K l) (stackSem_state_clock_fupd (K
          (stackSem_state_clock s + ck)) (stackSem_state_use_alloc_fupd
          (K F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         s))))))) =
        (r,state_gc_fun_fupd (K anything) (stackSem_state_regs_fupd
          (K l2) (state_code_fupd (K (fromAList (compile c (toAList
          (stackSem_state_code s))))) (stackSem_state_use_alloc_fupd (K
          F) (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_use_store_fupd (K T)
         t)))))) /\
       (~(r = NONE) ==> r = SOME (Halt (wordLang_Word (n2w 1)))) /\
         stackSem_state_regs
       t SUBMAP l2 /\
       (r = NONE ==> FLOOKUP l2 0 = SOME ret))`,
  CHEAT_TAC);;

(* [local] *)
let alloc_correct = prove
 (`alloc w (s:('a,'c,'b)stackSem_state) = (r,t) /\ ~(r = SOME Error) /\
  stackSem_state_gc_fun
     s = word_gc_fun c /\
     LENGTH (stackSem_state_bitmaps s) < dimword (:'a) - 1 /\
     LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
       dimword (:'a) /\
     FLOOKUP l 1 = SOME (wordLang_Word w) ==>
     (?ck l2.
        evaluate
           (Call (SOME (Skip,0,n',m)) (INL gc_stub_location)
             NONE,stackSem_state_code_fupd (K (fromAList (compile c
             (toAList (stackSem_state_code s)))))
             (stackSem_state_gc_fun_fupd (K anything)
             (stackSem_state_regs_fupd (K l) (stackSem_state_clock_fupd
             (K (stackSem_state_clock s + ck))
             (stackSem_state_use_alloc_fupd (K F)
             (stackSem_state_use_alloc_fupd (K F)
             (stackSem_state_use_stack_fupd (K T)
             (stackSem_state_use_store_fupd (K T)
            s)))))))) =
          (r,state_gc_fun_fupd (K anything) (stackSem_state_regs_fupd
            (K l2) (state_code_fupd (K (fromAList (compile c (toAList
            (stackSem_state_code s))))) (stackSem_state_use_alloc_fupd
            (K F) (stackSem_state_use_alloc_fupd (K F)
            (stackSem_state_use_stack_fupd (K T)
            (stackSem_state_use_store_fupd (K T)
           t))))))) /\ stackSem_state_regs t SUBMAP l2)`,
  CHEAT_TAC);;

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let find_code_IMP_lookup = prove
 (cake_as_vars (fun () ->
    `find_code dest regs (s:'a spt) = SOME x ==>
       (?k. sptree_lookup k s = SOME x /\
           (find_code dest regs = ((lookup k):'a spt->'a
             option)))`),
  CHEAT_TAC);;

let alloc_length_stack = prove
 (`alloc c s = (r,t) /\ stackSem_state_gc_fun s = word_gc_fun conf /\
   (!w. ~(r = SOME (Halt w))) ==>
   LENGTH (stack t) = LENGTH (stackSem_state_stack s)`,
  CHEAT_TAC);;

let find_code_regs_SUBMAP = prove
 (`r1 SUBMAP r2 /\
   find_code dest r1 c = SOME x ==>
   find_code dest r2 c = SOME x`,
  CHEAT_TAC);;

(* get_labels_comp *)
let stack_allocProof_get_labels_comp = prove
 (`!n p e. stackSem_get_labels e SUBSET stackSem_get_labels (FST (comp
  n p e))`,
  CHEAT_TAC);;

let loc_check_compile = prove
 (`loc_check (stackSem_state_code s) (l1,l2) /\
    (!k prog. lookup k (stackSem_state_code s) = SOME prog ==> ~(k =
      gc_stub_location)) ==>
    loc_check (fromAList (compile c (toAList (stackSem_state_code
      s)))) (l1,l2)`,
  CHEAT_TAC);;

(* [local] *)
let SUBMAP_DOMSUB_both = prove
 (`A SUBMAP B ==>
   A \\ c SUBMAP B \\ c`,
  CHEAT_TAC);;

(* [local] *)
let SUBMAP_FUPDATE_both = prove
 (`A SUBMAP B ==>
   A |+ (n,v) SUBMAP B |+ (n,v)`,
  CHEAT_TAC);;

(* This proof is very slow! *)
(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let inst_correct = prove
 (cake_as_vars (fun () ->
    `inst (i:'a asm_inst) (s:('a,'c,'b)stackSem_state) = SOME t /\
     LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
       dimword (:'a) /\
     LENGTH (buffer_buffer (stackSem_state_data_buffer s)) +
       (LENGTH (stackSem_state_bitmaps s) + buffer_space_left
       (stackSem_state_data_buffer s)) < dimword (:'a) - 1 /\
       stackSem_state_regs
     s SUBMAP regs ==>
     (?regs1.
     inst i (stackSem_state_code_fupd (K (fromAList (compile c
       (toAList (stackSem_state_code s)))))
       (stackSem_state_use_alloc_fupd (K F)
       (stackSem_state_use_store_fupd (K T)
       (stackSem_state_use_stack_fupd (K T) (stackSem_state_gc_fun_fupd
       (K anything) (stackSem_state_compile_oracle_fupd (K ((I ## MAP
       prog_comp ## I) o stackSem_state_compile_oracle s))
       (stackSem_state_compile_fupd (K compile_rest)
       (stackSem_state_regs_fupd (K regs) s)))))))) =
       SOME (state_code_fupd (K (fromAList (compile c (toAList
         (state_code t))))) (stackSem_state_use_alloc_fupd (K F)
         (stackSem_state_use_store_fupd (K T)
         (stackSem_state_use_stack_fupd (K T) (state_gc_fun_fupd (K
         anything) (stackSem_state_compile_oracle_fupd (K ((I ## MAP
         prog_comp ## I) o stackSem_state_compile_oracle t))
         (compile_fupd (K compile_rest) (stackSem_state_regs_fupd (K
         regs1) t)))))))) /\ stackSem_state_regs
       t SUBMAP regs1 /\
       LENGTH (stackSem_state_stack t) * (dimindex (:'a) DIV 8) <
         dimword (:'a) /\
       LENGTH (buffer_buffer (state_data_buffer t)) + (LENGTH
         (stackSem_state_bitmaps t) + buffer_space_left
         (state_data_buffer t)) < dimword (:'a) - 1)`),
  CHEAT_TAC);;

let ALOOKUP_prog_comp = prove
 (`!xs a y.
     ALOOKUP xs a = SOME y ==>
     ALOOKUP (MAP prog_comp xs) a = SOME (FST (comp a (next_lab y
       2) y))`,
  CHEAT_TAC);;

let lookup_fromAList_prog_comp = prove
 (`lookup x (stackSem_state_code s) = SOME p ==>
   lookup x (fromAList (MAP prog_comp (toAList (stackSem_state_code
     s)))) =
     SOME (FST (comp x (next_lab p 2) p))`,
  CHEAT_TAC);;

(* comp_correct *)
let stack_allocProof_comp_correct = prove
 (`!p (s:('a,'c,'b)stackSem_state) r t m n c regs'.
     evaluate (p,s) = (r,t) /\ ~(r = SOME Error) /\ alloc_arg p /\
     (!k prog. lookup k (stackSem_state_code s) = SOME prog ==> ~(k =
       gc_stub_location) /\
               alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (stackSem_state_compile_oracle s
       n))) ==> ~(k = gc_stub_location) /\ alloc_arg p) /\
       stackSem_state_gc_fun
     s = word_gc_fun c /\ stackSem_state_use_alloc s /\
     LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
       dimword (:'a) /\ stackSem_state_regs
     s SUBMAP regs' /\ stackSem_state_use_stack
     s /\
     // Necessary for the data buffer oracle
     // Data buffer does not wrap around
     LENGTH (stackSem_state_bitmaps s) + LENGTH (buffer_buffer
       (stackSem_state_data_buffer s)) + buffer_space_left
       (stackSem_state_data_buffer s) < dimword (:'a) - 1 /\
       stackSem_state_compile
     s = (\c. compile_rest c o (MAP prog_comp)) ==>
     (?ck regs1.
       evaluate (FST (comp n m p),stackSem_state_code_fupd (K
         (fromAList (stack_alloc_compile c (toAList (stackSem_state_code
         s))))) (stackSem_state_compile_fupd (K compile_rest)
         (stackSem_state_compile_oracle_fupd (K ((I ## MAP prog_comp ##
         I) o stackSem_state_compile_oracle s))
         (stackSem_state_gc_fun_fupd (K anything)
         (stackSem_state_regs_fupd (K regs') (stackSem_state_clock_fupd
         (K (stackSem_state_clock s + ck))
         (stackSem_state_use_alloc_fupd (K F)
         (stackSem_state_use_stack_fupd (K T)
         (stackSem_state_use_store_fupd (K T)
          s))))))))) =
         (r,state_code_fupd (K (fromAList (stack_alloc_compile c
           (toAList (state_code t))))) (compile_fupd (K compile_rest)
           (compile_oracle_fupd (K ((I ## MAP prog_comp ## I) o
           compile_oracle t)) (state_gc_fun_fupd (K anything)
           (stackSem_state_regs_fupd (K regs1)
           (stackSem_state_use_alloc_fupd (K F)
           (stackSem_state_use_stack_fupd (K T)
           (stackSem_state_use_store_fupd (K T) t)))))))) /\
           stackSem_state_regs
       t SUBMAP regs1 /\
       LENGTH (stackSem_state_bitmaps t) + LENGTH (buffer_buffer
         (state_data_buffer t)) + buffer_space_left (state_data_buffer
         t) < dimword (:'a) - 1 /\
       ((!w. ~(r = SOME (Halt w))) ==> LENGTH (stack t) * (dimindex
         (:'a) DIV 8) < dimword (:'a)))`,
  CHEAT_TAC);;

(* HOL4 stack_allocProofScript.sml:5896-5899: ML code, not ported *)

(* [local] *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let with_same_regs_lemma = prove
 (cake_as_vars (fun () ->
    `stackSem_state_code_fupd (K c) (stackSem_state_clock_fupd (K k)
  (stackSem_state_use_alloc_fupd (K F) (stackSem_state_use_store_fupd (K
  T) (stackSem_state_use_stack_fupd (K T) (stackSem_state_gc_fun_fupd (K
  anything) (stackSem_state_compile_oracle_fupd (K oracle)
  (stackSem_state_compile_fupd (K cc) (stackSem_state_regs_fupd (K
  (stackSem_state_regs s))
        s)))))))) = stackSem_state_code_fupd (K c)
          (stackSem_state_clock_fupd (K k)
          (stackSem_state_use_alloc_fupd (K F)
          (stackSem_state_use_store_fupd (K T)
          (stackSem_state_use_stack_fupd (K T)
          (stackSem_state_gc_fun_fupd (K anything)
          (stackSem_state_compile_oracle_fupd (K oracle)
          (stackSem_state_compile_fupd (K cc)
        s)))))))`),
  CHEAT_TAC);;
(* HOL4 stack_allocProofScript.sml:5907: ML code, not ported *)

(* compile_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stack_allocProof_compile_semantics = prove
 (cake_as_vars (fun () ->
    `(!k prog. lookup k (stackSem_state_code s) = SOME prog ==> ~(k =
  gc_stub_location) /\ alloc_arg prog) /\
      (!n k p. MEM (k,p) (FST (SND (stackSem_state_compile_oracle s
        n))) ==> ~(k = gc_stub_location) /\ alloc_arg p) /\
        stackSem_state_gc_fun
     (s:('a,'c,'b)stackSem_state) = (word_gc_fun c:('a word_loc)
       list#('a word->'a word_loc)#('a word->bool)#(store_name,'a
       word_loc)fmap->(('a word_loc) list#('a word->'a
       word_loc)#(store_name,'a word_loc)fmap) option) /\
     LENGTH (stackSem_state_bitmaps s) + LENGTH (buffer_buffer
       (stackSem_state_data_buffer s)) + buffer_space_left
       (stackSem_state_data_buffer s) < dimword (:'a) - 1 /\
     LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
       dimword (:'a) /\ stackSem_state_use_stack
     s /\ stackSem_state_use_alloc s /\ stackSem_state_compile
     s = (\c. compile_rest c o (MAP prog_comp)) /\ ~(semantics
       start s = Fail) ==>
     semantics start (stackSem_state_use_alloc_fupd (K F)
       (stackSem_state_use_stack_fupd (K T)
       (stackSem_state_use_store_fupd (K T)
       (stackSem_state_compile_oracle_fupd (K ((I ## MAP prog_comp ## I)
       o stackSem_state_compile_oracle s)) (stackSem_state_compile_fupd
       (K compile_rest) (stackSem_state_gc_fun_fupd (K anything)
       (stackSem_state_code_fupd (K (fromAList (stack_alloc_compile c
       (toAList (stackSem_state_code s))))) s))))))) =
     semantics start s`),
  CHEAT_TAC);;

(* TODO: does this have to initialize the data_buffer to empty? *)
let stack_allocProof_make_init_def = cake_define
  `stack_allocProof_make_init c code oracle'
  (s:('a,'c,'ffi)stackSem_state) = stackSem_state_compile_oracle_fupd (K
  oracle') (stackSem_state_compile_fupd (K (\c. stackSem_state_compile s
  c o (MAP stack_alloc_prog_comp))) (stackSem_state_gc_fun_fupd (K
  (word_gc_fun c)) (stackSem_state_use_stack_fupd (K T)
  (stackSem_state_use_alloc_fupd (K T) (stackSem_state_code_fupd (K
  code)
     s)))))`;;
hol4_overload "make_init" "stack_allocProof_make_init";;

(* HOL4 stack_allocProofScript.sml:6075-6079: a theorem whose
   statement the port cannot state yet: prog_comp_lambda *)

(* make_init_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let stack_allocProof_make_init_semantics = prove
 (cake_as_vars (fun () ->
    `(!k prog. ALOOKUP code k = SOME prog ==> ~(k = gc_stub_location) /\
  alloc_arg prog) /\
     (!n k p. MEM (k,p) (FST (SND (oracle n))) ==> ~(k =
       gc_stub_location) /\ alloc_arg p) /\ stackSem_state_use_stack
     s /\ stackSem_state_use_store s /\ ~(stackSem_state_use_alloc
       s) /\ stackSem_state_code s = fromAList (compile c code) /\
       stackSem_state_compile_oracle
     s = (I ## MAP prog_comp ## I) o oracle /\
     LENGTH (stackSem_state_bitmaps s) + LENGTH (buffer_buffer
       (stackSem_state_data_buffer s)) + buffer_space_left
       (stackSem_state_data_buffer s) < dimword (:'a) - 1 /\
     LENGTH (stackSem_state_stack s) * (dimindex (:'a) DIV 8) <
       dimword (:'a) /\
     ALL_DISTINCT (MAP FST code) /\ ~(semantics start
       (stack_allocProof_make_init c (fromAList code) oracle s) = Fail)
       ==>
     semantics start (s:('a,'c,'ffi)stackSem_state) =
     semantics start (stack_allocProof_make_init c (fromAList
       code) oracle s)`),
  CHEAT_TAC);;

(* HOL4 stack_allocProofScript.sml:6111-6121: a theorem that HOL4
   states as the value of an ML expression: next_lab_EQ_MAX *)

(* [local] *)
let MAX_SIMP = prove
 (`MAX n (MAX n m) = MAX n m`,
  CHEAT_TAC);;

let next_lab_thm = prove
 (`!p.
      next_lab (p:'a stackLang_prog) 2 =
      (match p with Seq p1 p2 -> MAX (next_lab p1 2) (next_lab p2 2)
        | If _1 _2 _3 p1 p2 -> MAX (next_lab p1 2) (next_lab p2 2) |
        Loop p -> next_lab p 2 | Call NONE _4 NONE -> 2 | Call NONE _5
        (SOME (_6,_7,l2)) -> MAX (l2 + 2) 2 | Call (SOME (p,_8,_9,l2))
        _10 NONE -> MAX (next_lab p 2) (l2 + 2) | Call (SOME
        (p,_11,_12,l2)) _13 (SOME (p',_14,l3)) ->
           MAX (MAX (next_lab p 2) (next_lab p' 2)) (MAX l2 l3 + 2)
             | _15 -> 2)`,
  CHEAT_TAC);;

let extract_labels_next_lab = prove
 (`!p (aux:num) e.
   MEM e (extract_labels p) ==>
   SND e < next_lab p 2`,
  CHEAT_TAC);;

let stack_alloc_lab_pres = prove
 (`!n nl p aux.
   EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (extract_labels
     p) /\
   ALL_DISTINCT (extract_labels p) /\
   next_lab p 2 <= nl ==>
   (let (cp,nl') = comp n nl p in
   EVERY (\(l1,l2). l1 = n /\ ~(l2 = 0) /\ ~(l2 = 1)) (extract_labels
     cp) /\
   ALL_DISTINCT (extract_labels cp) /\
   (!lab. MEM lab (extract_labels cp) ==> MEM lab (extract_labels p)
     \/ (nl <= SND lab /\ SND lab < nl')) /\
   nl <= nl')`,
  CHEAT_TAC);;

let stack_alloc_comp_stack_asm_name = prove
 (`!n m p.
   stack_asm_name c p /\ stack_asm_remove (c:'a asm_config) p ==>
   (let (p',m') = comp n m p in
   stack_asm_name c p' /\ stack_asm_remove (c:'a asm_config) p')`,
  CHEAT_TAC);;

let stack_alloc_stack_asm_convs = prove
 (`EVERY (\(n,p). stack_asm_name c p) prog /\
   EVERY (\(n,p). (stack_asm_remove (c:'a asm_config) p)) prog /\
   // conf_ok is too strong, but we already have it anyway
   conf_ok (:'a) conf /\
   asm_offset_ok 0 (asm_config_addr_offset c) (n2w 0) /\
   reg_name 10 c /\ good_dimindex (:'a) /\ asm_config_valid_imm
   c (INL Add) (n2w 8) /\ asm_config_valid_imm
   c (INL Add) (n2w 4) /\ asm_config_valid_imm
   c (INL Add) (n2w 1) /\ asm_config_valid_imm
   c (INL Sub) (n2w 1) ==>
   EVERY (\(n,p). stack_asm_name c p) (compile conf prog) /\
   EVERY (\(n,p). stack_asm_remove c p) (compile conf prog)`,
  CHEAT_TAC);;

let stack_alloc_reg_bound = prove
 (`10 <= sp /\
    EVERY (\p. reg_bound p sp)
       (MAP SND prog1) ==>
    EVERY (\p. reg_bound p sp)
       (MAP SND (compile dc prog1))`,
  CHEAT_TAC);;

let stack_alloc_call_args = prove
 (`EVERY (\p. call_args p 1 2 3 4 0) (MAP SND prog1) ==>
   EVERY (\p. call_args p 1 2 3 4 0) (MAP SND (compile dc prog1))`,
  CHEAT_TAC);;

(* [simp] *)
let compile_has_fp_ops = prove
 (`compile (data_to_word_config_has_fp_tern_fupd (K b2)
  (data_to_word_config_has_fp_ops_fupd (K b1) dconf)) code =
   compile dconf code`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["not";
   "shift";
   "stack_alloc"];;

(* and the accessors of those fields are overloaded again *)
let _ = unhide_overloads ();;
