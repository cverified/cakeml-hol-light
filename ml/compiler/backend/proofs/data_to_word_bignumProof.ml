(* ======================================================== *)
(*  data_to_word_bignumProof: ported from HOL4's
    compiler/backend/proofs/data_to_word_bignumProofScript.sml
    A proof theory, with 4 definitions and 52 theorems.  Needed by
    data_to_wordProof.ml and data_to_word_assignProof.ml.  *)
(* ======================================================== *)

(*
  Part of the correctness proof for data_to_word
*)

needs "basis/pure/mllist.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/gc/copying_gc.ml";;
needs "compiler/backend/gc/gc_shared.ml";;
needs "compiler/backend/gc/gen_gc.ml";;
needs "compiler/backend/gc/gen_gc_partial.ml";;
needs "compiler/backend/proofs/data_to_word_gcProof.ml";;
needs "compiler/backend/proofs/data_to_word_memoryProof.ml";;
needs "compiler/backend/proofs/word_bignumProof.ml";;
needs "compiler/backend/proofs/word_depthProof.ml";;
needs "compiler/backend/proofs/word_gcFunctions.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_depth.ml";;
needs "lib/alignment.ml";;
needs "lib/byte.ml";;
needs "lib/mc_multiword.ml";;
needs "lib/multiword.ml";;
needs "lib/pegexec.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticsProps.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "data_to_word_bignumProof"
  ["backend_common"; "copying_gc"; "dataProps"; "dataSem"; "data_to_word";
   "data_to_word_gcProof"; "data_to_word_memoryProof"; "gc_shared"; "gen_gc";
   "gen_gc_partial"; "mllist"; "semanticsProps"; "wordLang"; "wordProps";
   "wordSem"; "word_bignum"; "word_bignumProof"; "word_depthProof";
   "word_gcFunctions"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["failed","pegexec_failed"];;
(* HOL4 ancestors outside the port: int_bitwise finite_map *)

(* HOL4 data_to_word_bignumProofScript.sml:22: an overload that the source
   brings to the front: cut_env, written out as wordSem_cut_env *)

(* HOL4 data_to_word_bignumProofScript.sml:26-27: a proof *)

(* HOL4 data_to_word_bignumProofScript.sml:29-30: ML code, not ported *)

(* HOL4 data_to_word_bignumProofScript.sml:32-36: a proof *)

let eq_eval =
  end_itlist CONJ [wordSem_evaluate_def; wordSem_get_var_def; lookup_insert;
  get_var_imm_def; word_cmp_def; word_exp_def; wordSem_set_var_def;
  wordSem_call_env_def; fromList2_def; wordSem_mem_load_def;
  bad_dest_args_def; wordSem_get_vars_def; wordSem_find_code_def;
  add_ret_loc_def; list_insert_def; wordSem_dec_clock_def; the_words_def;
  word_op_def];;

let word_list_IMP_store_list = prove
 (`!xs a frame m dm.
      (misc_word_list a xs * frame) (fun2set (m,dm)) ==>
      data_to_word_memoryProof_store_list a xs m dm = SOME m`,
  CHEAT_TAC);;

let word_exp_set_var_ShiftVar_lemma = prove
 (`wordSem_word_exp t (ShiftVar sow v n) =
    match sptree_lookup v (wordSem_state_locals t) with SOME (word_Word w)
      ->
        OPTION_MAP word_Word
          (match sow with Lsl -> SOME (w << n)
                     | Lsr -> SOME (w >>> n)
                     | Asr -> SOME (w >> n)
                     | Ror -> SOME (word_ror w n))
    | _ -> FAIL (wordSem_word_exp t (ShiftVar sow v n)) "lookup failed"`,
  CHEAT_TAC);;

let i2mw_small_int_IMP_0 = prove
 (`(!v1. ~(i2mw v = (F,[v1:'a word]))) /\ (!v1. ~(i2mw v = (T,[v1:'a word])))
  /\
    small_int (:'a) v /\ good_dimindex (:'a) ==> v = (&0)`,
  CHEAT_TAC);;

let state_rel_Number_small_int = prove
 (`data_to_word_gcProof_state_rel c r1 r2 s t (SOME [x]) locs /\ small_int
  (:'a) i ==>
    data_to_word_gcProof_state_rel c r1 r2 s t (SOME [(dataSem_Number
      i,word_Word (Smallnum i:'a word))]) locs`,
  CHEAT_TAC);;

let heap_lookup_Unused_Bignum = prove
 (`heap_lookup a (CONS (Unused k) hb) = SOME (Bignum j) <=>
    k + 1 <= a /\
    heap_lookup (a - (k + 1)) hb = SOME (Bignum j)`,
  CHEAT_TAC);;

let push_env_insert_0 = prove
 (`wordSem_push_env (sptree_insert 0 x LN,LN) NONE t =
  wordSem_state_permute_fupd (K (\n. wordSem_state_permute t (n + 1)))
  (wordSem_state_stack_max_fupd (K
                (OPTION_MAP2 MAX (wordSem_state_stack_max t)
                  (stack_size (CONS (StackFrame (wordSem_state_locals_size
                    t) [(0,x)] [] NONE) (wordSem_state_stack t)))))
                    (wordSem_state_stack_fupd (K (CONS (StackFrame
                    (wordSem_state_locals_size t) [(0,x)] [] NONE)
                    (wordSem_state_stack t)))
    t))`,
  CHEAT_TAC);;

let mc_header_i2mw_eq_0w = prove
 (`2 * LENGTH (SND (i2mw i):('a word) list) + 1 < dimword (:'a) ==>
    (mc_header (i2mw i:bool#('a word) list) = ((n2w 0):'a word) <=> i =
      (&0))`,
  CHEAT_TAC);;

let MustTerminate_limit_eq = prove
 (`good_dimindex (:'a) ==>
    (?k. MustTerminate_limit (:'a) =
        10 * dimword (:'a) * dimword (:'a) +
        10 * dimword (:'a) + 100 + k)`,
  CHEAT_TAC);;

let SND_i2mw_NIL = prove
 (`SND (i2mw i) = [] <=> i = (&0)`,
  CHEAT_TAC);;

let word_cmp_Test_1 = prove
 (`asm_word_cmp asm_Test w (n2w 1) <=> ~(word_bit 0 w)`,
  CHEAT_TAC);;

let word_bit_if_1_0 = prove
 (`word_bit 0 (if b then (n2w 1) else (n2w 0)) <=> b`,
  CHEAT_TAC);;

let get_iop_def = new_definition
  `get_iop (n:num) =
     if n = 0 then multiword_Add else if n = 1 then multiword_Sub else if
       n = 4 then multiword_Mul else if n = 5 then multiword_Div else
       multiword_Mod`;;

let data_to_word_bignumProof_int_op_def = new_definition
  `data_to_word_bignumProof_int_op op_index (i:int) (j:int) =
     if op_index = 0 then SOME (i + j) else if op_index = 1 then SOME (i
       - j) else if op_index = 4 then SOME (i * j) else if op_index = 5
       /\ ~(j = (&0)) then SOME (i / j) else if op_index = 6 /\ ~(j = (&0))
       then SOME (i % j) else NONE`;;

let get_sign_word_lemma = prove
 (`good_dimindex (:'a) ==> ((n2w 1) && x >>> 4) = (if word_bit 4 x then (n2w
  1) else (n2w 0):'a word)`,
  CHEAT_TAC);;

(* [local] *)
let if_eq_b2w = prove
 (`(if b then (n2w 1) else (n2w 0)) = b2w b`,
  CHEAT_TAC);;


let option_le_max_dest = prove
 (`option_le a b ==> OPTION_MAP2 MAX a b = b`,
  CHEAT_TAC);;

let option_map_max_comm = prove
 (`OPTION_MAP2 MAX a b = OPTION_MAP2 MAX b a`,
  CHEAT_TAC);;

(* [local] *)
let b2n_not = prove
 (`(if c then 0 else 1) = b2n (~c)`,
  CHEAT_TAC);;

let LongDiv1_thm' = prove
 (`!k n1 n2 m i1 i2 (t2:('a,'c,'ffi)wordSem_state)
        r1 r2 m1 is1 (c:data_to_word_config).
      single_div_loop (n2w k,[n1; n2],m,[i1; i2]) = (m1,is1) /\
      sptree_lookup LongDiv1_location (wordSem_state_code t2) = SOME
        (7,LongDiv1_code c) /\
      sptree_lookup 0 (wordSem_state_locals t2) = SOME (word_Loc r1 r2) /\
      sptree_lookup 2 (wordSem_state_locals t2) = SOME (word_Word (n2w k))
        /\
      sptree_lookup 4 (wordSem_state_locals t2) = SOME (word_Word n2) /\
      sptree_lookup 6 (wordSem_state_locals t2) = SOME (word_Word n1) /\
      sptree_lookup 8 (wordSem_state_locals t2) = SOME (word_Word m) /\
      sptree_lookup 10 (wordSem_state_locals t2) = SOME (word_Word i1) /\
      sptree_lookup 12 (wordSem_state_locals t2) = SOME (word_Word i2) /\
      k < dimword (:'a) /\ k < wordSem_state_clock t2 /\ good_dimindex (:'a)
        /\ ~(data_to_word_config_has_longdiv c) ==>
      (?j1 j2 max'.
        is1 = [j1; j2] /\
        wordSem_evaluate (LongDiv1_code c,t2) = (SOME (wordSem_Result
          (word_Loc r1 r2) [word_Word m1]),wordSem_state_store_fupd (K
          (wordSem_state_store t2 |+ (Temp (n2w 28),word_Word (HD is1))))
          (wordSem_state_stack_max_fupd (K max')
          (wordSem_state_locals_size_fupd (K (SOME 0))
          (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K
          (wordSem_state_clock t2 - k))
          t2))))) /\
       (max' = wordSem_state_stack_max t2 \/ max' = OPTION_MAP2 MAX
         (wordSem_state_stack_max t2)
          (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t2))
             (sptree_lookup LongDiv1_location (wordSem_state_stack_size
               t2)))))`,
  CHEAT_TAC);;

let LongDiv1_thm = prove
 (`!k n1 n2 m i1 i2 (t2:('a,'c,'ffi)wordSem_state)
        r1 r2 m1 is1 (c:data_to_word_config).
      single_div_loop (n2w k,[n1; n2],m,[i1; i2]) = (m1,is1) /\
      sptree_lookup LongDiv1_location (wordSem_state_code t2) = SOME
        (7,LongDiv1_code c) /\
      sptree_lookup 0 (wordSem_state_locals t2) = SOME (word_Loc r1 r2) /\
      sptree_lookup 2 (wordSem_state_locals t2) = SOME (word_Word (n2w k))
        /\
      sptree_lookup 4 (wordSem_state_locals t2) = SOME (word_Word n2) /\
      sptree_lookup 6 (wordSem_state_locals t2) = SOME (word_Word n1) /\
      sptree_lookup 8 (wordSem_state_locals t2) = SOME (word_Word m) /\
      sptree_lookup 10 (wordSem_state_locals t2) = SOME (word_Word i1) /\
      sptree_lookup 12 (wordSem_state_locals t2) = SOME (word_Word i2) /\
      k < dimword (:'a) /\ k < wordSem_state_clock t2 /\ good_dimindex (:'a)
        /\ ~(data_to_word_config_has_longdiv c) ==>
      (?j1 j2 max'.
        is1 = [j1; j2] /\
        wordSem_evaluate (LongDiv1_code c,t2) = (SOME (wordSem_Result
          (word_Loc r1 r2) [word_Word m1]),wordSem_state_store_fupd (K
          (wordSem_state_store t2 |+ (Temp (n2w 28),word_Word (HD is1))))
          (wordSem_state_stack_max_fupd (K max')
          (wordSem_state_locals_size_fupd (K (SOME 0))
          (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K
          (wordSem_state_clock t2 - k))
          t2))))) /\
      (option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t2))
        (wordSem_state_locals_size t2)) (wordSem_state_stack_max t2)
        /\ wordSem_state_locals_size
           t2 = sptree_lookup LongDiv1_location (wordSem_state_stack_size
             t2) ==> max' = wordSem_state_stack_max t2))`,
  CHEAT_TAC);;

(* [local] *)
let lt_dimindex_MOD_dimword = prove
 (`n < dimindex (:'a) ==> n MOD dimword (:'a) = n`,
  CHEAT_TAC);;
add_simp lt_dimindex_MOD_dimword;;

let get_real_addr_lemma = prove
 (`shift_length c < dimindex (:'a) /\
    good_dimindex (:'a) /\
    wordSem_get_var v (t:('a,'c,'ffi)wordSem_state) = SOME (word_Word ptr_w)
      /\
    get_real_addr c (wordSem_state_store t) ptr_w = SOME x ==>
    wordSem_word_exp t (real_addr c v) = SOME (word_Word (x:'a word))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_lookup = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs s st m dm
        (APPEND (join_env l1 (toAList (inter l2 (adjust_set l1)))) xs) /\
      sptree_lookup n l1 = SOME x /\ sptree_lookup (adjust_var n) l2 =
        SOME w ==>
      memory_rel c be ts refs s st m dm
       (CONS (x,w) (APPEND (join_env l1 (toAList (inter l2 (adjust_set
         l1)))) xs))`),
  CHEAT_TAC);;

let evaluate_AddNumSize = prove
 (`!src c l1 l2 s t locs i w.
      data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state)
        NONE locs /\
      dataSem_get_var src (dataSem_state_locals s) = SOME (dataSem_Number i)
        ==>
      wordSem_evaluate (AddNumSize c src,wordSem_set_var 1 (word_Word w) t)
        =
        (NONE,wordSem_set_var 1 (word_Word (w +
           n2w (4 * LENGTH ((SND (i2mw i):('a word) list))))) t)`,
  CHEAT_TAC);;

let AnyHeader_thm = prove
 (`!t1 t2 t3 r.
      data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state)
        NONE locs /\
      dataSem_get_var r (dataSem_state_locals s) = SOME (dataSem_Number i)
        /\
      ALL_DISTINCT [t1; t2; t3] ==>
      (?a2 a3 temp.
        wordSem_evaluate (AnyHeader c (adjust_var r) a t1 t2 t3,t) =
          (NONE,(wordSem_set_store (Temp t1) (word_Word (mc_header (i2mw
            i)))
                 (wordSem_set_store (Temp t2) (word_Word a2)
                 (wordSem_set_store (Temp t3) (word_Word a3)
                   (wordSem_set_var 7 temp t))))) /\
        (i = (&0:int) ==>
           small_int (:'a) (&0:int) /\ i2mw i = (F,[]) /\
           a2 = (n2w 0) /\ a3 = (n2w 0)) /\
        (small_int (:'a) i /\ ~(i = (&0)) ==>
           i2mw i = ((i < (&0)),[a3]) /\
           FLOOKUP (wordSem_state_store t) (if a then OtherHeap else
             NextFree) = SOME (word_Word a2)) /\
        (~(small_int (:'a) i) ==>
           (?w x. wordSem_get_var (adjust_var r) t = SOME (word_Word w) /\
                 get_real_addr c (wordSem_state_store t) w = SOME x /\
                 a2 = x + bytes_in_word)))`,
  CHEAT_TAC);;

let state_rel_set_store_Temp = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (wordSem_set_store (Temp tmp) w t)
  vs locs =
   data_to_word_gcProof_state_rel c l1 l2 s t vs locs`,
  CHEAT_TAC);;

let state_rel_IMP_num_size_limit = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs /\
    dataSem_get_var k (dataSem_state_locals s) = SOME (dataSem_Number i) ==>
    LENGTH (SND (i2mw i):('a word) list) < dimword (:'a) DIV 16`,
  CHEAT_TAC);;

let word_list_store_list = prove
 (`!xs a frame m dm.
      (misc_word_list a xs * frame) (fun2set (m,dm)) ==>
      (?m2. (data_to_word_memoryProof_store_list a (REPLICATE (LENGTH xs)
        (word_Word (n2w 0))) m dm = SOME m2) /\
           (misc_word_list a (REPLICATE (LENGTH xs) (word_Word (n2w 0))) *
             frame)
              (fun2set (m2,dm)))`,
  CHEAT_TAC);;

let MustTerminate_limit_SUB_2 = prove
 (`good_dimindex (:'a) ==> dimword (:'a) <= MustTerminate_limit (:'a) - 2`,
  CHEAT_TAC);;

let cut_env_fromList_sing = prove
 (`dataSem_cut_env (sptree_fromList [one]) (sptree_insert 0 (word_Loc l1 l2)
  LN) =
    SOME (sptree_insert 0 (word_Loc l1 l2) LN)`,
  CHEAT_TAC);;

let single_div_pre_IMP_single_div_full = prove
 (`single_div_pre x1 x2 y ==>
    single_div x1 x2 y = single_div_full x1 x2 y`,
  CHEAT_TAC);;

let IMP_LESS_MustTerminate_limit = prove
 (`i < dimword (:'a) ==>
    i < MustTerminate_limit (:'a) - 1`,
  CHEAT_TAC);;
add_simp IMP_LESS_MustTerminate_limit;;

let evaluate_LongDiv_code' = prove
 (`!(t:('a,'c,'ffi)wordSem_state) l1 l2 c w x1 x2 y d1 m1.
      single_div_pre x1 x2 y /\
      single_div x1 x2 y = (d1,(m1:'a word)) /\
      sptree_lookup LongDiv1_location (wordSem_state_code t) = SOME
        (7,LongDiv1_code c) /\
      sptree_lookup 0 (wordSem_state_locals t) = SOME (word_Loc l1 l2) /\
      sptree_lookup 2 (wordSem_state_locals t) = SOME (word_Word x1) /\
      sptree_lookup 4 (wordSem_state_locals t) = SOME (word_Word x2) /\
      sptree_lookup 6 (wordSem_state_locals t) = SOME (word_Word y) /\
      dimword (:'a) < wordSem_state_clock t /\ good_dimindex (:'a) ==>
      (?ck max'.
        wordSem_evaluate (LongDiv_code c,t) =
          (SOME (wordSem_Result (word_Loc l1 l2) [word_Word
            d1]),wordSem_state_stack_max_fupd (K max')
            (wordSem_state_store_fupd (K (wordSem_state_store t |+ (Temp (n2w
            28),word_Word m1))) (wordSem_state_locals_size_fupd (K (SOME 0))
            (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K ck)
           t))))) /\
     (max' = wordSem_state_stack_max t \/ max' = OPTION_MAP2 MAX
       (wordSem_state_stack_max t)
          (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t))
             (sptree_lookup LongDiv1_location (wordSem_state_stack_size
               t)))))`,
  CHEAT_TAC);;

let evaluate_LongDiv_code = prove
 (`!(t:('a,'c,'ffi)wordSem_state) l1 l2 c w x1 x2 y d1 m1.
      single_div_pre x1 x2 y /\
      single_div x1 x2 y = (d1,(m1:'a word)) /\
      sptree_lookup LongDiv1_location (wordSem_state_code t) = SOME
        (7,LongDiv1_code c) /\
      sptree_lookup 0 (wordSem_state_locals t) = SOME (word_Loc l1 l2) /\
      sptree_lookup 2 (wordSem_state_locals t) = SOME (word_Word x1) /\
      sptree_lookup 4 (wordSem_state_locals t) = SOME (word_Word x2) /\
      sptree_lookup 6 (wordSem_state_locals t) = SOME (word_Word y) /\
      dimword (:'a) < wordSem_state_clock t /\ good_dimindex (:'a) ==>
      (?ck max'.
        wordSem_evaluate (LongDiv_code c,t) =
          (SOME (wordSem_Result (word_Loc l1 l2) [word_Word
            d1]),wordSem_state_stack_max_fupd (K max')
            (wordSem_state_store_fupd (K (wordSem_state_store t |+ (Temp (n2w
            28),word_Word m1))) (wordSem_state_locals_size_fupd (K (SOME 0))
            (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K ck)
           t))))) /\
      (option_le (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t))
        (wordSem_state_locals_size t)) (wordSem_state_stack_max t)
        /\ wordSem_state_locals_size
       t = sptree_lookup LongDiv1_location (wordSem_state_stack_size t)
         ==> max' = wordSem_state_stack_max t))`,
  CHEAT_TAC);;

let div_code_assum_thm = prove
 (`data_to_word_gcProof_state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE
  locs ==>
    div_code_assum (:'ffi) (:'c) (wordSem_state_code t)`,
  CHEAT_TAC);;

let IMP_bignum_code_rel = prove
 (`word_bignum_compile Bignum_location 2 1 (Bignum_location + 1,[])
             mc_iop_code = (xx1,xx2,xx3,xx4,xx5) /\
    data_to_word_gcProof_state_rel c l1 l2 s t NONE locs ==>
    word_bignumProof_code_rel (xx4,xx5) (wordSem_state_code t)`,
  CHEAT_TAC);;

let TWO_LESS_MustTerminate_limit = prove
 (`2 < MustTerminate_limit (:'a) /\
    ~(MustTerminate_limit (:'a) <= 1)`,
  CHEAT_TAC);;
add_simp TWO_LESS_MustTerminate_limit;;

let arith_location_def = new_definition
  `Arith_location index =
     if index = 0 then Add_location else if index = 1 then Sub_location
       else if index = 4 then Mul_location else if index = 5 then
       Div_location else if index = 6 then Mod_location else ARB`;;

let push_env_code = prove
 (`wordSem_state_code
      (wordSem_push_env y NONE t) = wordSem_state_code t`,
  CHEAT_TAC);;

let arith_code_def = new_definition
  `Arith_code index =
     word_Seq (word_Assign 6 (word_Const (n2w (4 * index))))
       (word_Call NONE (SOME AnyArith_location) [0; 2; 4; 6] NONE)`;;

let lookup_Arith_location = prove
 (`data_to_word_gcProof_state_rel c l1 l2 x t NONE locs
  /\ data_to_word_bignumProof_int_op index i1 i2 = SOME r ==>
    sptree_lookup (Arith_location index) (wordSem_state_code t) = SOME
      (3,Arith_code index)`,
  CHEAT_TAC);;

(* Replicate_code_thm *)
let replicate_code_thm = prove
 (`!n a r m1 a1 a2 a3 a4 a5.
      sptree_lookup Replicate_location (wordSem_state_code r) = SOME
        (5,Replicate_code) /\
      data_to_word_memoryProof_store_list (a + bytes_in_word) (REPLICATE n
        v) (wordSem_state_memory
        (r:('a,'c,'ffi)wordSem_state)) (wordSem_state_mdomain r) = SOME m1
          /\
      wordSem_get_var a1 r = SOME (word_Loc l1 l2) /\
      wordSem_get_var a2 r = SOME (word_Word a) /\
      wordSem_get_var a3 r = SOME v /\
      wordSem_get_var a4 r = SOME (word_Word (n2w (4 * n))) /\
      wordSem_get_var a5 (r:('a,'c,'ffi)wordSem_state) = SOME ret_val /\
      4 * n < dimword (:'a) /\
      n < wordSem_state_clock r ==>
      (?m.
        wordSem_evaluate (word_Call NONE (SOME Replicate_location) [a1; a2;
          a3; a4; a5] NONE,r) =
          (SOME (wordSem_Result (word_Loc l1 l2)
            [ret_val]),wordSem_state_stack_max_fupd (K m)
            (wordSem_state_locals_size_fupd (K (SOME 0))
            (wordSem_state_locals_fupd (K LN) (wordSem_state_clock_fupd (K
            (wordSem_state_clock r - n - 1)) (wordSem_state_memory_fupd (K m1)
           r))))) /\
        option_le m
          (OPTION_MAP2 MAX (wordSem_state_stack_max r)
             (OPTION_MAP2 (+) (stack_size (wordSem_state_stack r))
                (sptree_lookup Replicate_location
                  (wordSem_state_stack_size r)))))`,
  CHEAT_TAC);;

(* Replicate_code_alt_thm *)
let replicate_code_alt_thm = prove
 (`!n a r m1 a1 a2 a3 a4 a5 var.
      sptree_lookup Replicate_location (wordSem_state_code r) = SOME
        (5,Replicate_code) /\
      data_to_word_memoryProof_store_list (a + bytes_in_word) (REPLICATE n
        v) (wordSem_state_memory
        (r:('a,'c,'ffi)wordSem_state)) (wordSem_state_mdomain r) = SOME m1
          /\
      wordSem_get_var a2 r = SOME (word_Word a) /\
      wordSem_get_var a3 r = SOME v /\
      wordSem_get_var a4 r = SOME (word_Word (n2w (4 * n))) /\
      wordSem_get_var 0 (r:('a,'c,'ffi)wordSem_state) = SOME ret_val /\
      4 * n < dimword (:'a) /\
      n < wordSem_state_clock r ==>
      (?max'.
        wordSem_evaluate (word_Call (SOME ([0],(sptree_fromList
          [one],LN),word_Skip,l1,l2))
                    (SOME Replicate_location) [a2; a3; a4; 0] NONE,r) =
        (NONE,wordSem_state_permute_fupd (K (\n. wordSem_state_permute r (n
          + 1))) (wordSem_state_stack_max_fupd (K max')
          (wordSem_state_locals_fupd (K (sptree_insert 0 ret_val LN))
          (wordSem_state_clock_fupd (K (wordSem_state_clock r - n - 1))
          (wordSem_state_memory_fupd (K m1)
         r))))))`,
  CHEAT_TAC);;

let bignum_digits_LENGTH_n2mw = prove
 (`good_dimindex (:'a) ==>
   (!n. bignum_digits (dimindex (:'a) = 64) n = LENGTH ((n2mw n):('a word)
     list))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:1145: the ML values that the
   definitions below antiquote *)

(* HOL4 data_to_word_bignumProofScript.sml:1147: ML code, not ported *)

(* HOL4 data_to_word_bignumProofScript.sml:1149-1152: ML code, not ported *)

let AnyArith_thm = prove
 (`!op_index i j v t s r2 r1 locs l2 l1 c.
     data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
       (t:('a,'c,'ffi)wordSem_state) NONE locs /\
     dataSem_get_vars [0; 1; 2] (dataSem_state_locals s) = SOME
       [dataSem_Number i; dataSem_Number j; dataSem_Number (&op_index)]
       /\ wordSem_state_clock
     t = MustTerminate_limit (:'a) - 2 /\ ~(wordSem_state_termdep t = 0) /\
     sptree_lookup 6 (wordSem_state_locals t) = SOME (word_Word (n2w (4 *
       op_index))) /\
     data_to_word_bignumProof_int_op op_index i j = SOME v ==>
     (?q r new_c.
       wordSem_evaluate (AnyArith_code c,t) = (q,r) /\
       (if q = SOME wordSem_NotEnoughSpace then wordSem_state_ffi
         r = wordSem_state_ffi t /\
         (~(data_to_word_config_gc_kind c = data_to_word_None)
           /\ no_thunks_in_refs (dataSem_state_refs s) ==>
            (let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
              s)) i in
            let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
              s)) j in
              il + jl <= 2 EXP data_to_word_config_len_size c ==>
                limits_heap_limit (dataSem_state_limits
              s) <
              il + jl + size_of_heap (cut_locals (sptree_fromList [one; one;
                one]) s)))
       else ?rv. q = SOME (wordSem_Result (word_Loc l1 l2) [rv]) /\
              data_to_word_gcProof_state_rel c r1 r2
                (dataSem_state_stack_max_fupd (K NONE)
                  (dataSem_state_space_fupd (K 0) (dataSem_state_clock_fupd (K
                  new_c) (dataSem_state_locals_size_fupd (K (SOME 0))
                  (dataSem_state_locals_fupd (K LN) s))))) r
                (SOME [(dataSem_Number v,rv)]) locs))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:2128: ML code, not ported *)

let MAP_FST_EQ_IMP_IS_SOME_ALOOKUP = prove
 (`!xs ys.
      MAP FST xs = MAP FST ys ==>
      IS_SOME (ALOOKUP xs n) = IS_SOME (ALOOKUP ys n)`,
  CHEAT_TAC);;

let domain_adjust_sets = prove
 (`~(domain (FST (adjust_sets kept_names)) = {})`,
  CHEAT_TAC);;

let env_to_list_domain_eq = prove
 (`env_to_list y2 (wordSem_state_permute t) = (l',permute) /\
   MAP FST l' = MAP FST ms ==>
   domain (fromAList ms) = domain y2`,
  CHEAT_TAC);;

let size_of_LE_append = prove
 (`!vs ys lims refs seen.
     FST (size_of lims ys refs seen) <= FST (size_of lims (APPEND vs ys)
       refs seen)`,
  CHEAT_TAC);;

let size_of_heap_LE_args = prove
 (`!vs s. size_of_heap s <= size_of_heap_args vs s`,
  CHEAT_TAC);;

let eval_Call_Arith_max_stack_NONE = prove
 (`!index r.
      data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
        (t:('a,'c,'ffi)wordSem_state) NONE locs /\ ~(names_opt = NONE) /\ 1 <
        wordSem_state_termdep t /\
      dataSem_get_vars [a1; a2] (dataSem_state_locals s) = SOME
        [dataSem_Number i1; dataSem_Number i2] /\
      dataSem_cut_state_opt names_opt s = SOME x /\
      data_to_word_bignumProof_int_op index i1 i2 = SOME r ==>
      (?q r'.
        (\(res,s1).
           if res = NONE then
             wordSem_evaluate (data_to_word_list_Seq [word_Move 2
               [(adjust_var dest,1)]],s1)
           else (res,s1))
          (wordSem_evaluate
            (word_MustTerminate
              (word_Call (SOME ([1],adjust_sets (data_to_word_get_names
                names_opt),word_Skip,n,l))
                (SOME (Arith_location index))
                [adjust_var a1; adjust_var a2] NONE),t)) = (q,r') /\
        (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
         r' = dataSem_state_ffi s /\
         (~(data_to_word_config_gc_kind c = data_to_word_None)
           /\ no_thunks_in_refs (dataSem_state_refs s) ==>
            (let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
              s)) i1 in
            let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
              s)) i2 in
              il + jl <= 2 EXP data_to_word_config_len_size c ==>
                limits_heap_limit (dataSem_state_limits
              s) < 2 * il + 2 * jl + size_of_heap x))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         data_to_word_gcProof_state_rel c l1 l2
           (dataSem_state_stack_max_fupd (K NONE) (dataSem_state_space_fupd
             (K 0) (dataSem_state_locals_fupd (K (sptree_insert dest
             (dataSem_Number r) (dataSem_state_locals x))) x)))
           r' NONE locs /\ q = NONE))`,
  CHEAT_TAC);;

let EVERY_IMP_ALOOKUP = prove
 (`!xs P. ALL P xs ==> (!x y. ALOOKUP xs x = SOME y ==> P (x,y))`,
  CHEAT_TAC);;

let structure_le_IMP_option_le = prove
 (`!l x y.
     structure_le x y ==>
     option_le (max_depth l x) (max_depth l y)`,
  CHEAT_TAC);;

let evaluate_Assign_Const =
  SIMP_CONV [wordSem_evaluate_def; word_exp_def; wordSem_set_var_def]
  `wordSem_evaluate (word_Assign n (word_Const w),s)`;;

let eval_Call_Arith = prove
 (`!index r.
      data_to_word_gcProof_state_rel c l1 l2 (s:('c,'ffi)dataSem_state)
        (t:('a,'c,'ffi)wordSem_state) NONE locs /\ ~(names_opt = NONE) /\ 1 <
        wordSem_state_termdep t /\
      dataSem_get_vars [a1; a2] (dataSem_state_locals s) = SOME
        [dataSem_Number i1; dataSem_Number i2] /\
      dataSem_cut_state_opt names_opt s = SOME x /\
      data_to_word_bignumProof_int_op index i1 i2 = SOME r ==>
      (?q r'.
        (\(res,s1).
           if res = NONE then
             wordSem_evaluate (data_to_word_list_Seq [word_Move 2
               [(adjust_var dest,1)]],s1)
           else (res,s1))
          (wordSem_evaluate
            (word_MustTerminate
              (word_Call (SOME ([1],adjust_sets (data_to_word_get_names
                names_opt),word_Skip,n,l))
                (SOME (Arith_location index))
                [adjust_var a1; adjust_var a2] NONE),t)) = (q,r') /\
        (let max' = OPTION_MAP2 MAX (dataSem_state_stack_max s)
                (OPTION_MAP2 (+) (stack_size (wordSem_state_stack t))
                  (OPTION_MAP2 (+) (wordSem_state_locals_size t)
                    (OPTION_MAP2 MAX (sptree_lookup (Arith_location index)
                      (wordSem_state_stack_size t))
                              (max_depth (wordSem_state_stack_size t)
                                AnyArith_call_tree)))) in
        option_le (wordSem_state_stack_max r') max' /\
        (q = SOME wordSem_NotEnoughSpace ==> wordSem_state_ffi
         r' = dataSem_state_ffi s /\
         (~(data_to_word_config_gc_kind c = data_to_word_None)
           /\ no_thunks_in_refs (dataSem_state_refs s) ==>
            (let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
              s)) i1 in
            let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
              s)) i2 in
              il + jl <= 2 EXP data_to_word_config_len_size c ==>
                limits_heap_limit (dataSem_state_limits
              s) <
                2 * il + 2 * jl + size_of_heap_args [dataSem_Number i1;
                  dataSem_Number i2] x))) /\
        (~(q = SOME wordSem_NotEnoughSpace) ==>
         data_to_word_gcProof_state_rel c l1 l2
           (dataSem_state_stack_max_fupd (K max') (dataSem_state_space_fupd
             (K 0) (dataSem_state_locals_fupd (K (sptree_insert dest
             (dataSem_Number r) (dataSem_state_locals x))) x)))
           r' NONE locs /\ q = NONE)))`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
