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
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
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
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/dataProps.ml";;
needs "compiler/backend/semantics/dataSem.ml";;
needs "compiler/backend/semantics/wordProps.ml";;
needs "compiler/backend/semantics/wordSem.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/alignment.ml";;
needs "lib/location.ml";;
needs "lib/mc_multiword.ml";;
needs "lib/multiword.ml";;
needs "lib/pegexec.ml";;
needs "lib/set_sep.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/proofs/semanticsProps.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "data_to_word_bignumProof"
  ["backend_common"; "copying_gc"; "dataProps"; "dataSem";
   "data_to_word"; "data_to_word_gcProof"; "data_to_word_memoryProof";
   "gc_shared"; "gen_gc"; "gen_gc_partial"; "mllist";
   "semanticsProps"; "wordLang"; "wordProps"; "wordSem";
   "word_bignum"; "word_bignumProof"; "word_depthProof";
   "word_gcFunctions"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["failed","pegexec_failed"];;
(* HOL4 ancestors outside the port: int_bitwise finite_map *)

hol4_overload "cut_env" "wordSem_cut_env";;

(* HOL4 data_to_word_bignumProofScript.sml:26-27: a proof *)

(* HOL4 data_to_word_bignumProofScript.sml:29-30: ML code, not ported *)

(* HOL4 data_to_word_bignumProofScript.sml:32-36: a proof *)

(* HOL4 data_to_word_bignumProofScript.sml:38-46: a theorem that HOL4
   states as the value of an ML expression: eq_eval *)

let word_list_IMP_store_list = prove
 (`!xs a frame m dm.
      (misc_word_list a xs * frame) (fun2set (m,dm)) ==>
      data_to_word_memoryProof_store_list a xs m dm = SOME m`,
  CHEAT_TAC);;

let word_exp_set_var_ShiftVar_lemma = prove
 (`wordSem_word_exp t (ShiftVar sow v n) =
    (match lookup v (state_locals t) with SOME (wordLang_Word w) ->
        OPTION_MAP wordLang_Word
          (match sow with Lsl -> SOME (w << n) | Lsr -> SOME (w >>>
            n) | Asr -> SOME (w >> n) | Ror -> SOME (word_ror w n)) |
            _1 -> FAIL (wordSem_word_exp t (ShiftVar sow v n))
            "lookup failed")`,
  CHEAT_TAC);;

let i2mw_small_int_IMP_0 = prove
 (`(!v1. ~(i2mw v = (F,[v1:'a word]))) /\ (!v1. ~(i2mw v = (T,[v1:'a
  word]))) /\
    small_int (:'a) v /\ good_dimindex (:'a) ==> v = (&0)`,
  CHEAT_TAC);;

let state_rel_Number_small_int = prove
 (`state_rel c r1 r2 s t (SOME [x]) locs /\ small_int (:'a) i ==>
    state_rel c r1 r2 s t (SOME [(Number i,wordLang_Word (Smallnum
      i:'a word))]) locs`,
  CHEAT_TAC);;

let heap_lookup_Unused_Bignum = prove
 (`heap_lookup a (Unused k :: hb) = SOME (Bignum j) <=>
    k + 1 <= a /\
    heap_lookup (a - (k + 1)) hb = SOME (Bignum j)`,
  CHEAT_TAC);;

let push_env_insert_0 = prove
 (`push_env (insert 0 x LN,LN) NONE t = wordSem_state_permute_fupd (K
  (\n. wordSem_state_permute t (n + 1))) (state_stack_max_fupd (K
                (OPTION_MAP2 MAX (state_stack_max t)
                  (stack_size (StackFrame (state_locals_size t)
                    [(0,x)] [] NONE :: stack t)))) (stack_fupd (K
                    (StackFrame (state_locals_size t) [(0,x)] [] NONE ::
                    stack t))
    t))`,
  CHEAT_TAC);;

let mc_header_i2mw_eq_0w = prove
 (`2 * LENGTH (SND (i2mw i):('a word) list) + 1 < dimword (:'a) ==>
    (mc_header (i2mw i:bool#('a word) list) = ((n2w 0):'a word) <=>
      i = (&0))`,
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
 (`word_cmp (Test:cmp) w (n2w 1) <=> ~(word_bit 0 w)`,
  CHEAT_TAC);;

let word_bit_if_1_0 = prove
 (`word_bit 0 (if b then (n2w 1) else (n2w 0)) <=> b`,
  CHEAT_TAC);;

let get_iop_def = new_definition
  `get_iop (n:num) =
     (if n = 0 then multiword_Add else
     if n = 1 then multiword_Sub else
     if n = 4 then multiword_Mul else
     if n = 5 then multiword_Div else
                   multiword_Mod)`;;

let data_to_word_bignumProof_int_op_def = new_definition
  `data_to_word_bignumProof_int_op op_index (i:int) (j:int) =
     (if op_index = 0 then SOME (i + j) else
     if op_index = 1 then SOME (i - j) else
     if op_index = 4 then SOME (i * j) else
     if op_index = 5 /\ ~(j = (&0)) then SOME (i / j) else
     if op_index = 6 /\ ~(j = (&0)) then SOME (i % j) else NONE)`;;
hol4_overload "int_op" "data_to_word_bignumProof_int_op";;

let get_sign_word_lemma = prove
 (`good_dimindex (:'a) ==> ((n2w 1) && x >>> 4) = (if word_bit 4 x
  then (n2w 1) else (n2w 0):'a word)`,
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

(* HOL4 data_to_word_bignumProofScript.sml:254-363: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   LongDiv1_thm' *)

(* HOL4 data_to_word_bignumProofScript.sml:365-478: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   LongDiv1_thm *)

(* [local,simp] *)
let lt_dimindex_MOD_dimword = prove
 (`n < dimindex (:'a) ==> n MOD dimword (:'a) = n`,
  CHEAT_TAC);;

let get_real_addr_lemma = prove
 (`shift_length c < dimindex (:'a) /\
    good_dimindex (:'a) /\
    get_var v (t:('a,'c,'ffi)wordSem_state) = SOME (wordLang_Word
      ptr_w) /\
    get_real_addr c (wordSem_state_store t) ptr_w = SOME x ==>
    wordSem_word_exp t (real_addr c v) = SOME (wordLang_Word (x:'a
      word))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let memory_rel_lookup = prove
 (cake_as_vars (fun () ->
    `memory_rel c be ts refs s st m dm
        (join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs) /\
      lookup n l1 = SOME x /\ lookup (adjust_var n) l2 = SOME w ==>
      memory_rel c be ts refs s st m dm
       ((x,w) :: (join_env l1 (toAList (inter l2 (adjust_set
         l1))) ++ xs))`),
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:516-577: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_AddNumSize *)

(* HOL4 data_to_word_bignumProofScript.sml:579-731: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   AnyHeader_thm *)

let state_rel_set_store_Temp = prove
 (`state_rel c l1 l2 s (wordSem_set_store (Temp tmp) w t) vs locs =
   state_rel c l1 l2 s t vs locs`,
  CHEAT_TAC);;

let state_rel_IMP_num_size_limit = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs /\
    get_var k (state_locals s) = SOME (Number i) ==>
    LENGTH (SND (i2mw i):('a word) list) < dimword (:'a) DIV 16`,
  CHEAT_TAC);;

let word_list_store_list = prove
 (`!xs a frame m dm.
      (misc_word_list a xs * frame) (fun2set (m,dm)) ==>
      (?m2. (data_to_word_memoryProof_store_list a (REPLICATE (LENGTH
        xs) (wordLang_Word (n2w 0))) m dm = SOME m2) /\
           (misc_word_list a (REPLICATE (LENGTH xs) (wordLang_Word
             (n2w 0))) * frame)
              (fun2set (m2,dm)))`,
  CHEAT_TAC);;

let MustTerminate_limit_SUB_2 = prove
 (`good_dimindex (:'a) ==> dimword (:'a) <= MustTerminate_limit (:'a)
  - 2`,
  CHEAT_TAC);;

let cut_env_fromList_sing = prove
 (`cut_env (fromList [one]) (insert 0 (Loc l1 l2) LN) =
    SOME (insert 0 (Loc l1 l2) LN)`,
  CHEAT_TAC);;

let single_div_pre_IMP_single_div_full = prove
 (`single_div_pre x1 x2 y ==>
    single_div x1 x2 y = single_div_full x1 x2 y`,
  CHEAT_TAC);;

(* [simp] *)
let IMP_LESS_MustTerminate_limit = prove
 (`i < dimword (:'a) ==>
    i < MustTerminate_limit (:'a) - 1`,
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:814-863: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_LongDiv_code' *)

(* HOL4 data_to_word_bignumProofScript.sml:865-915: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   evaluate_LongDiv_code *)

let div_code_assum_thm = prove
 (`state_rel c l1 l2 s (t:('a,'c,'ffi)wordSem_state) NONE locs ==>
    div_code_assum (:'ffi) (:'c) (wordSem_state_code t)`,
  CHEAT_TAC);;

let IMP_bignum_code_rel = prove
 (`compile Bignum_location 2 1 (Bignum_location + 1,[])
             mc_iop_code = (xx1,xx2,xx3,xx4,xx5) /\
    state_rel c l1 l2 s t NONE locs ==>
    code_rel (xx4,xx5) (state_code t)`,
  CHEAT_TAC);;

(* [simp] *)
let TWO_LESS_MustTerminate_limit = prove
 (`2 < MustTerminate_limit (:'a) /\
    ~(MustTerminate_limit (:'a) <= 1)`,
  CHEAT_TAC);;

let arith_location_def = new_definition
  `Arith_location index =
     (if index = 0 then Add_location else
     if index = 1 then Sub_location else
     if index = 4 then Mul_location else
     if index = 5 then Div_location else
     if index = 6 then Mod_location else ARB)`;;

let push_env_code = prove
 (`state_code
      (push_env y NONE t) = state_code t`,
  CHEAT_TAC);;

let arith_code_def = new_definition
  `Arith_code index =
     Seq (Assign 6 (wordLang_Const (n2w (4 * index))))
       (Call NONE (SOME AnyArith_location) [0; 2; 4; 6] NONE)`;;

let lookup_Arith_location = prove
 (`state_rel c l1 l2 x t NONE locs /\ int_op index i1 i2 = SOME r ==>
    lookup (Arith_location index) (state_code t) = SOME
      (3,Arith_code index)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:1010-1055: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   Replicate_code_thm *)

(* HOL4 data_to_word_bignumProofScript.sml:1057-1130: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   Replicate_code_alt_thm *)

let bignum_digits_LENGTH_n2mw = prove
 (`good_dimindex (:'a) ==>
   (!n. bignum_digits (dimindex (:'a) = 64) n = LENGTH ((n2mw
     n):('a word) list))`,
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:1145: the ML values that
   the definitions below antiquote *)

(* HOL4 data_to_word_bignumProofScript.sml:1147: ML code, not ported *)

(* HOL4 data_to_word_bignumProofScript.sml:1149-1152: ML code, not
   ported *)

(* HOL4 data_to_word_bignumProofScript.sml:1154-2126: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   AnyArith_thm *)

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
     FST (size_of lims ys refs seen) <= FST (size_of lims (vs ++
       ys) refs seen)`,
  CHEAT_TAC);;

let size_of_heap_LE_args = prove
 (`!vs s. size_of_heap s <= size_of_heap_args vs s`,
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:2181-2419: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   eval_Call_Arith_max_stack_NONE *)

let EVERY_IMP_ALOOKUP = prove
 (`!xs P. EVERY P xs ==> (!x y. ALOOKUP xs x = SOME y ==> P (x,y))`,
  CHEAT_TAC);;

let structure_le_IMP_option_le = prove
 (`!l x y.
     structure_le x y ==>
     option_le (max_depth l x) (max_depth l y)`,
  CHEAT_TAC);;

(* HOL4 data_to_word_bignumProofScript.sml:2450-2453: a theorem that
   HOL4 states as the value of an ML expression:
   evaluate_Assign_Const *)

(* HOL4 data_to_word_bignumProofScript.sml:2455-2583: a theorem whose
   statement HOL Light does not read (tools/unstated.py):
   eval_Call_Arith *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
