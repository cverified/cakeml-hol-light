(* ======================================================== *)
(*  dataSem: ported from HOL4's
    compiler/backend/semantics/dataSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of dataLang
*)

needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/compiler.ml";;
needs "semantics/semantics.ml";;
(* HOL4 ancestors outside the port: (* TODO: immoral, shouldn't
   depend on *) backendProps *)

let dataSem_v_INDUCT,dataSem_v_RECURSION = define_datatype
  "dataSem_v = dataSem_Number (int) | dataSem_Word64 (word64) | \
   dataSem_Block (num) (num) (dataSem_v list) | dataSem_CodePtr (num) \
   | dataSem_RefPtr (bool) (num)";;

let Boolv_def = cake_define
  `dataSem_Boolv b = dataSem_Block 0 (bool_to_tag b) []`;;

let Unit_def = cake_define
  `dataSem_Unit = dataSem_Block 0 (tuple_tag) []`;;

(* Stack frame with:
   -  A stack frame size `ss` (NONE when unbounded)
   -  The local environment `env`
   -  Possibly a `handler`

  *)
let stack_INDUCT,stack_RECURSION = define_datatype
  "stack = dataSem_Env (num option) (dataSem_v spt) | dataSem_Exc \
   (num option) (dataSem_v spt) (num)";;

let limits_FIELDS = define_record "limits"
  ["heap_limit","num";
   "length_limit","num";
   "stack_limit","num";
   "arch_64_bit","bool";
   "has_fp_ops","bool";
   "has_fp_tops","bool"];;

let dataSem_state_FIELDS = define_record "dataSem_state"
  ["locals","dataSem_v spt";
   "locals_size","num option";
   "stack","stack list";
   "stack_max","num option";
   "stack_frame_sizes","num spt";
   "global","num option";
   "handler","num";
   "refs","(dataSem_v bvlSem_ref) spt";
   "compile","'c->(num#num#dataLang_prog) list->(word8 list#word64 \
   list#'c) option";
   "clock","num";
   "code","(num#dataLang_prog) spt";
   "ffi","'ffi ffi_state";
   "space","num";
   "tstamps","num option";
   "limits","limits";
   "safe_for_space","bool";
   "peak_heap_length","num";
   "compile_oracle","num->'c#(num#num#dataLang_prog) list"];;

(* HOL4 ML code, not ported:
val s = ``(s:('c,'ffi) dataSem$state)``
val vs = ``(vs:dataSem$v list)``
*)

let arch_size_def = cake_define
  `arch_size lims = (if limits_arch_64_bit lims then 64 else 32:num)`;;

let check_res_def = cake_define
  `check_res r (n,refs,seen) =
     (if sptree_size refs <= sptree_size r then (n,refs,seen) else
       (n,r,seen))`;;

let small_num_def = cake_define
  `small_num arch64 (i:int) =
     (if arch64 then --(2 EXP 61) <= i /\ i < (2 EXP 61) else --(2
       EXP 29) <= i /\ i < (2 EXP 29))`;;

let bignum_digits_def = cake_define
  `bignum_digits arch64 n =
     (if n = 0 then 0 else
       let d = if arch64 then 64 else 32 in
         1 + bignum_digits arch64 (n DIV 2 EXP d))`;;

let bignum_size_def = cake_define
  `bignum_size arch64 i =
     1 + bignum_digits arch64 (num_of_int (abs i))`;;

(* HOL4 termination: \\ rpt strip_tac \\ fs
   [sptreeTheory.size_delete] \\ imp_res_tac miscTheory.lookup_zero
   \\ fs [] \\ rw [] \\ fs [] \\ imp_res_tac check_res_IMP \\ fs [] *)
let size_of_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE (list_size v_size))
                             (\(lims,vs,refs,seen). (sptree_size
                               refs,vs)))`
  `(size_of lims [] refs seen = (0,refs,seen)) /\
   (size_of lims (x :: y :: ys) refs seen =
     (let (n1,refs1,seen1) = check_res refs (size_of lims (y :: ys)
       refs seen) in
     let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
       (n1 + n2,refs2,seen2))) /\
   (size_of lims [dataSem_Word64 _1] refs seen = (3,refs,seen)) /\
   (size_of lims [dataSem_Number i] refs seen =
     (if small_num (limits_arch_64_bit lims) i then 0 else
       bignum_size (limits_arch_64_bit lims) i,refs,seen)) /\
   (size_of lims [dataSem_CodePtr _2] refs seen = (0,refs,seen)) /\
   (size_of lims [dataSem_RefPtr _3 r] refs seen =
      (match sptree_lookup r refs with NONE -> (0,refs,seen) | SOME
        (bvlSem_ByteArray _4 bs) -> (LENGTH bs DIV (arch_size lims DIV
        8) + 2,balanced_map_delete r refs,seen) | SOME
        (bvlSem_ValueArray vs) -> (let (n,refs,seen) = size_of lims vs
        (balanced_map_delete r refs) seen in
                              (n + LENGTH vs + 1,refs,seen)) | SOME
                                (bvlSem_Thunk _5 dataSem_v) -> (let
                                (n,refs,seen) = size_of lims [dataSem_v]
                                (balanced_map_delete r refs) seen in
                              (n + 2,refs,seen)) | SOME
                                (bvlSem_MutBlock tg fin ls c rs) ->
          (let (n,refs,seen) = size_of lims (ls ++ [c] ++ rs)
            (balanced_map_delete r refs) seen in
            (n + LENGTH ls + LENGTH rs + 2,refs,seen)))) /\
   (size_of lims [dataSem_Block ts pattern_semantics_tag []]) refs
     seen = (0,refs,seen) /\
   (size_of lims [dataSem_Block ts pattern_semantics_tag vs] refs
     seen =
      (if IS_SOME (sptree_lookup ts seen) then (0,refs,seen) else
        let (n,refs,seen) = size_of lims vs refs (balanced_map_insert
          ts one seen) in
          (n + LENGTH vs + 1,refs,seen)))`;;

let extract_stack_def = cake_define
  `extract_stack (dataSem_Env _6 env) = mlvector_toList env /\
   extract_stack (dataSem_Exc _7 env _8) = mlvector_toList env`;;

let global_to_vs_def = cake_define
  `global_to_vs NONE = [] /\
   global_to_vs (SOME n) = [dataSem_RefPtr T n]`;;

let stack_to_vs_def = cake_define
  `^
     stack_to_vs s =
       mlvector_toList (dataSem_state_locals s) ++ FLAT (MAP
         extract_stack (?_stack s)) ++ global_to_vs
         (dataSem_state_global s)`;;

(* Measures the amount of space everything in a dataLang "heap" would
   need
   to fit in wordLang memory (over-approximation) *)
let size_of_heap_def = cake_define
  `^
     size_of_heap s =
       (let (n,_9,_10) = ^ (size_of (dataSem_state_limits s) (^
         stack_to_vs s)) (?_refs s LN) in
         n)`;;

let no_thunks_in_refs_def = cake_define
  `no_thunks_in_refs refs <=> (!k e dataSem_v. ~(balanced_map_lookup
  k refs = SOME (bvlSem_Thunk e dataSem_v)))`;;

(* HOL4 overload (expanded in the port):
     add_space_safe = λk ^s. s.safe_for_space
           ∧ no_thunks_in_refs s.refs
           ∧ size_of_heap s + k <= s.limits.heap_limit *)

(* HOL4 overload (expanded in the port):
     heap_peak = λk ^s. MAX (s.peak_heap_length) (size_of_heap s + k) *)

let add_space_def = cake_define
  `^
     add_space (s k) = dataSem_state_peak_heap_length_fupd (K
       (heap_peak k s)) (dataSem_state_safe_for_space_fupd (K
       (add_space_safe k s)) (dataSem_state_space_fupd (K k)
       s))`;;

(* Args-aware variant: cost reflects op_args + non-arg locals as the
   GC-root set, matching wordSem's view at the op's inner Alloc.
   stack_to_vs already covers s.locals (which, when the dataLang
   evaluator hands the state to do_app, is the NARROW cut without args).
     *)
let size_of_heap_args_def = cake_define
  `^
     (size_of_heap_args op_args) s =
       (let (n,_11,_12) = ^ (size_of (dataSem_state_limits s) (^
         (op_args ++ stack_to_vs) s)) (?_refs s LN) in
         n)`;;

(* HOL4 overload (expanded in the port):
     add_space_safe_args = λk op_args ^s. s.safe_for_space
                  ∧ size_of_heap_args op_args s + k <=
                    s.limits.heap_limit *)

(* HOL4 overload (expanded in the port):
     heap_peak_args = λk op_args ^s. MAX (s.peak_heap_length)
       (size_of_heap_args op_args s + k) *)

let consume_space_def = cake_define
  `^
     (consume_space k) s =
       (if dataSem_state_space s < k then NONE else SOME
         (dataSem_state_space_fupd (K (dataSem_state_space s - k))
         s))`;;

(* Determines which operations are safe for space *)
let allowed_op_def = cake_define
  `allowed_op flatLang_op _13 = (~(flatLang_op = closLang_Install) /\
  (!t i. ~(flatLang_op = closLang_MemOp (closLang_MutCons t i))))`;;

let v_to_list_def = cake_define
  `dataSem_v_to_list x1 =
        match x1 with
          (dataSem_Block ts pattern_semantics_tag []) ->
        if pattern_semantics_tag = nil_tag then SOME [] else NONE
        | (dataSem_Block ts pattern_semantics_tag [h; bt]) ->
        if pattern_semantics_tag = cons_tag then
          (match dataSem_v_to_list bt with SOME t -> SOME (h :: t) |
            _14 -> NONE) else NONE
        | _15 -> NONE`;;

(* HOL4 overload (expanded in the port):
     bignum_limit = \i1 i2 s.
      let il = bignum_size s.limits.arch_64_bit i1 in
      let jl = bignum_size s.limits.arch_64_bit i2 in
        2 * il + 2 * jl *)

(* Gives an upper bound to the memory consuption of an operation *)
let space_consumed_def = cake_define
  `(^ space_consumed (s (closLang_BlockOp (closLang_ConsExtend
  pattern_semantics_tag)) (dataSem_Block _16 _17 xs' :: dataSem_Number
  lower :: dataSem_Number len :: dataSem_Number tot :: xs)) =
    LENGTH (xs ++ TAKE (num_of_int len) (DROP (num_of_int lower)
      xs')) + 1) /\
   (space_consumed s (closLang_MemOp closLang_RefArray)
     [dataSem_Number len; _18] = num_of_int len + 1) /\
   (space_consumed s (closLang_MemOp (closLang_RefByte _19))
     [dataSem_Number len; _20] = num_of_int len DIV (arch_size
     (dataSem_state_limits s) DIV 8) + 2) /\
   (space_consumed s (closLang_BlockOp (closLang_FromList n))
     [dataSem_Number len; lv] = num_of_int len + 1) /\
   (space_consumed s (closLang_IntOp word_bignum_Add) [dataSem_Number
     i1; dataSem_Number i2] =
     (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
       /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) i2 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1 +
          i2) then 0 else (\i1 i2 s.
       let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i1 in
       let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i2 in
         2 * il + 2 * jl) i1 i2 s)) /\
   (space_consumed s (closLang_IntOp word_bignum_Sub) [dataSem_Number
     i1; dataSem_Number i2] =
     (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
       /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) i2 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1 -
          i2) then 0 else (\i1 i2 s.
       let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i1 in
       let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i2 in
         2 * il + 2 * jl) i1 i2 s)) /\
   (space_consumed s (closLang_IntOp closLang_Mult) [dataSem_Number
     i1; dataSem_Number i2] =
     (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
       /\ 0 <= i1 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) i2 /\
          0 <= i2 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1 *
          i2) then 0 else (\i1 i2 s.
       let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i1 in
       let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i2 in
         2 * il + 2 * jl) i1 i2 s)) /\
   (space_consumed s (closLang_IntOp word_bignum_Div) [dataSem_Number
     i1; dataSem_Number i2] =
     (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
       /\ 0 <= i1 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) i2 /\
          0 <= i2 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1 /
          i2) then 0 else (\i1 i2 s.
       let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i1 in
       let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i2 in
         2 * il + 2 * jl) i1 i2 s)) /\
   (space_consumed s (closLang_IntOp tokens_Mod) [dataSem_Number i1;
     dataSem_Number i2] =
     (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
       /\ 0 <= i1 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) i2 /\
          0 <= i2 /\
        small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1 %
          i2) then 0 else (\i1 i2 s.
       let il = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i1 in
       let jl = bignum_size (limits_arch_64_bit (dataSem_state_limits
         s)) i2 in
         2 * il + 2 * jl) i1 i2 s)) /\
   (space_consumed s (closLang_BlockOp closLang_ListAppend) [lv1;
     lv2] =
    (match dataSem_v_to_list lv1 with
     SOME l -> SUC (LENGTH l) * 3 | NONE -> 0)) /\
   (space_consumed s (flatLang_op:closLang_op) (vs:dataSem_v list)
     = (0:num))`;;

let vb_size_def = cake_define
  `vb_size x1 =
        match x1 with
          (dataSem_Block ts t ls) -> 1 + t + SUM (MAP vb_size ls) +
            LENGTH ls
        | _21 -> 1`;;

let vs_depth_def = cake_define
  `vs_depth x1 =
        match x1 with
          (dataSem_Block ts t ls) -> vs_depth_list ls
        | _22 -> 0
        | [] -> 0
        | (x :: xs) -> MAX (1 + vs_depth x) (vs_depth_list xs)`;;

let eq_code_stack_max_def = cake_define
  `eq_code_stack_max n tsz =
   OPTION_MAP ((*) n)
     (OPTION_MAP2 MAX
       (sptree_lookup Equal_location tsz)
       (OPTION_MAP2 MAX
         (balanced_map_lookup Equal1_location tsz)
         (balanced_map_lookup Compare1_location tsz)))`;;

let stack_consumed_def = cake_define
  `stack_consumed sfs lims p vs =
        match (p,vs) with
          ((closLang_MemOp (closLang_CopyByte _23)),vs) ->
       OPTION_MAP2 MAX
        (sptree_lookup ByteCopy_location sfs)
        (OPTION_MAP2 MAX
           (balanced_map_lookup ByteCopyAdd_location sfs)
           (balanced_map_lookup ByteCopySub_location sfs))
        | ((closLang_MemOp (closLang_RefByte _24)),vs) ->
       OPTION_MAP2 MAX
        (balanced_map_lookup RefByte_location sfs)
        (balanced_map_lookup Replicate_location sfs)
        | ((closLang_MemOp (closLang_RefArray)),vs) ->
       OPTION_MAP2 MAX
        (balanced_map_lookup RefArray_location sfs)
        (balanced_map_lookup Replicate_location sfs)
        | ((closLang_MemOp closLang_XorByte),vs) ->
       balanced_map_lookup XorLoop_location sfs
        | ((closLang_MemOp (closLang_StringCmp b cmp)),vs) ->
       balanced_map_lookup StringCmpLoop_location sfs
        | ((closLang_BlockOp (closLang_ConsExtend _25)),vs) ->
       balanced_map_lookup MemCopy_location sfs
        | ((closLang_BlockOp (closLang_FromList _26)),vs) ->
       OPTION_MAP2 MAX
        (balanced_map_lookup FromList_location sfs)
        (balanced_map_lookup FromList1_location sfs)
        | ((closLang_BlockOp closLang_ListAppend),vs) ->
       OPTION_MAP2 MAX
        (balanced_map_lookup Append_location sfs)
        (OPTION_MAP2 MAX
          (balanced_map_lookup AppendLenLoop_location sfs)
          (balanced_map_lookup AppendMainLoop_location sfs))
        | ((closLang_IntOp word_bignum_Div),[dataSem_Number n1;
          dataSem_Number n2]) ->
       if small_num (limits_arch_64_bit lims) n1 /\ 0 <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ 0 <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 / n2) then
         OPTION_MAP2 MAX
           (balanced_map_lookup LongDiv_location sfs)
           (balanced_map_lookup LongDiv1_location sfs) else
         OPTION_MAP2 MAX (balanced_map_lookup Div_location sfs)
           (max_depth sfs AnyArith_call_tree)
        | ((closLang_IntOp tokens_Mod),[dataSem_Number n1;
          dataSem_Number n2]) ->
       if small_num (limits_arch_64_bit lims) n1 /\ 0 <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ 0 <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 % n2) then
         OPTION_MAP2 MAX
           (balanced_map_lookup LongDiv_location sfs)
           (balanced_map_lookup LongDiv1_location sfs) else
         OPTION_MAP2 MAX (balanced_map_lookup Mod_location sfs)
           (max_depth sfs AnyArith_call_tree)
        | ((closLang_IntOp closLang_Mult),[dataSem_Number n1;
          dataSem_Number n2]) ->
       if small_num (limits_arch_64_bit lims) n1 /\ 0 <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ 0 <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 * n2) then SOME 0
            else
         OPTION_MAP2 MAX (balanced_map_lookup Mul_location sfs)
           (max_depth sfs AnyArith_call_tree)
        | ((closLang_BlockOp (EQUAL)),[v1; v2]) ->
      (eq_code_stack_max (MIN (vs_depth v1 + 1) (vs_depth v2 + 1))
        sfs)
        | ((closLang_IntOp word_bignum_Sub),[dataSem_Number n1;
          dataSem_Number n2]) ->
       if small_num (limits_arch_64_bit lims) n1 /\
          small_num (limits_arch_64_bit lims) n2 /\
          small_num (limits_arch_64_bit lims) (n1 - n2) then SOME 0
            else
         OPTION_MAP2 MAX (balanced_map_lookup Sub_location sfs)
           (max_depth sfs AnyArith_call_tree)
        | ((closLang_IntOp word_bignum_Add),[dataSem_Number n1;
          dataSem_Number n2]) ->
       if small_num (limits_arch_64_bit lims) n1 /\
          small_num (limits_arch_64_bit lims) n2 /\
          small_num (limits_arch_64_bit lims) (n1 + n2) then SOME 0
            else
         OPTION_MAP2 MAX (balanced_map_lookup Add_location sfs)
           (max_depth sfs AnyArith_call_tree)
        | ((closLang_IntOp closLang_LessEq),vs) ->
       OPTION_MAP2 MAX
        (balanced_map_lookup Compare_location sfs)
        (balanced_map_lookup Compare1_location sfs)
        | ((closLang_IntOp (LESS)),vs) ->
       OPTION_MAP2 MAX
        (balanced_map_lookup Compare_location sfs)
        (balanced_map_lookup Compare1_location sfs)
        | (p,vs) ->
        if allowed_op p (LENGTH vs) then SOME 0 else NONE`;;

(* HOL4 overload (expanded in the port):
     do_space_safe = λop vs ^s. if op_space_reset op
              then s.safe_for_space
                   ∧ no_thunks_in_refs s.refs
                   ∧ size_of_heap_args vs s
                       + space_consumed s op vs
                     <= s.limits.heap_limit
              else s.safe_for_space *)

(* HOL4 overload (expanded in the port):
     do_space_peak = λop vs ^s. if op_space_reset op
              then heap_peak_args (space_consumed s op vs) vs s
              else s.peak_heap_length *)

let do_space_def = cake_define
  `^
     (do_space flatLang_op vs) s =
       (if op_space_reset flatLang_op then SOME
         (dataSem_state_peak_heap_length_fupd (K (do_space_peak
         flatLang_op vs s)) (dataSem_state_safe_for_space_fupd (K
         (do_space_safe flatLang_op vs s)) (dataSem_state_space_fupd
         (K 0) s))) else if op_space_req flatLang_op (LENGTH vs) = 0
         then SOME s else consume_space (op_space_req flatLang_op
         (LENGTH vs)) s)`;;

let size_of_stack_frame_def = cake_define
  `size_of_stack_frame (dataSem_Env n _27) = n /\ size_of_stack_frame
  (dataSem_Exc n _28 _29) = OPTION_MAP ((+) 3) n`;;

let size_of_stack_def = cake_define
  `size_of_stack = FOLDR (OPTION_MAP2 (+) o size_of_stack_frame)
  (SOME 1)`;;

let do_stack_def = cake_define
  `^
     (do_stack flatLang_op vs) s =
     (let new_stack = OPTION_MAP2 (+) (stack_consumed
       (dataSem_state_stack_frame_sizes s) (dataSem_state_limits s)
       flatLang_op vs)
                         (OPTION_MAP2 (+) (size_of_stack (?_stack s))
                           (dataSem_state_locals_size s)) in
                           dataSem_state_stack_max_fupd (K (OPTION_MAP2
                           MAX (dataSem_state_stack_max s) new_stack))
                           (dataSem_state_safe_for_space_fupd (K (
                              dataSem_state_safe_for_space s /\ the F
                                (OPTION_MAP ((>) (limits_stack_limit
                                (dataSem_state_limits s))) new_stack)))
       s))`;;

let v_to_bytes_def = cake_define
  `dataSem_v_to_bytes lv = some (\(ns:word8 list).
                     dataSem_v_to_list lv = SOME (MAP
                       (dataSem_Number o & o w2n) ns))`;;

let v_to_words_def = cake_define
  `dataSem_v_to_words lv = some (\ns. dataSem_v_to_list lv = SOME
  (MAP dataSem_Word64 ns))`;;

(* TODO: move this stuff *)
let isClos_def = cake_define
  `dataSem_isClos t1 l1 = (((t1 = closure_tag) \/ (t1 =
  partial_app_tag)) /\ ~(l1 = []))`;;

let do_eq_def = cake_define
  `dataSem_do_eq refs x2 x3 =
        match (x2,x3) with
          ((dataSem_CodePtr _30),_31) -> Eq_type_error
        | (_32,(dataSem_CodePtr _33)) -> Eq_type_error
        | ((dataSem_Number n1),(dataSem_Number n2)) -> (Eq_val (n1 =
          n2))
        | ((dataSem_Number _34),_35) -> Eq_type_error
        | (_36,(dataSem_Number _37)) -> Eq_type_error
        | ((dataSem_Word64 w1),(dataSem_Word64 w2)) -> (Eq_val (w1 =
          w2))
        | ((dataSem_Word64 _38),_39) -> Eq_type_error
        | (_40,(dataSem_Word64 _41)) -> Eq_type_error
        | ((dataSem_RefPtr b1 n1),(dataSem_RefPtr b2 n2)) ->
       if b1 /\ b2 then
        (match (sptree_lookup n1 refs,sptree_lookup n2 refs) with
           (SOME (bvlSem_ByteArray T bs1),SOME (bvlSem_ByteArray T
             bs2)) -> Eq_val (bs1 = bs2) | (SOME (bvlSem_ByteArray T
             bs1),_42) -> Eq_type_error | (_43,SOME (bvlSem_ByteArray T
             bs2)) -> Eq_type_error | _44 -> Eq_val (n1 = n2)) else
             Eq_type_error
        | ((dataSem_RefPtr _45 _46),_47) -> Eq_type_error
        | (_48,(dataSem_RefPtr _49 _50)) -> Eq_type_error
        | ((dataSem_Block _51 t1 l1),(dataSem_Block _52 t2 l2)) ->
      if dataSem_isClos t1 l1 \/ dataSem_isClos t2 l2 then if
        dataSem_isClos t1 l1 /\ dataSem_isClos t2 l2 then Eq_val T else
        Eq_type_error else if (t1 = t2) /\ (LENGTH l1 = LENGTH l2) then
        dataSem_do_eq_list refs l1 l2 else Eq_val F
        | ([],[]) -> Eq_val T
        | ((v1 :: vs1),(v2 :: vs2)) ->
      match dataSem_do_eq refs v1 v2 with Eq_val T ->
        dataSem_do_eq_list refs vs1 vs2 | Eq_val F -> Eq_val F | bad ->
        bad
        | (_53,_54) -> Eq_val F`;;

(* HOL4 overload (expanded in the port):
     Error = (Rerr(Rabort Rtype_error)):(dataSem$v#('c,'ffi)
       dataSem$state, dataSem$v)result *)

let do_install_def = cake_define
  `^
     (do_install vs) s =
         (match vs with [v1; v2; vl1; vl2] ->
              (match (dataSem_v_to_bytes v1,dataSem_v_to_words v2)
                with (SOME bytes,SOME data) ->
                  (if ~(vl1 = dataSem_Number (&LENGTH bytes)) \/ ~(
                     vl2 = dataSem_Number (&LENGTH data)) then Rerr
                       (Rabort Rtype_error) else
                  let (cfg,progs) = ?_compile_oracle s 0 in
                  let new_oracle = shift_seq 1 (?_compile_oracle s)
                    in
                    (match (?_compile s cfg progs,progs) with (SOME
                      (bytes',data',cfg'),(k,labLang_prog) :: _55) ->
                         (if bytes = bytes' /\ data = data' /\ FST
                           (new_oracle 0) = cfg' then
                           let s' = ?_compile_oracle_fupd (K
                             new_oracle) (?_code_fupd (K
                             (balanced_map_union (?_code s) (fromAList
                             progs))) (dataSem_state_safe_for_space_fupd
                             (K F)
                             s)) in
                             Rval (dataSem_CodePtr k,s') else Rerr
                               (Rabort Rtype_error)) | _56 -> Rerr
                               (Rabort Rtype_error))) | _57 -> Rerr
                               (Rabort Rtype_error)) | _58 -> Rerr
                               (Rabort Rtype_error))`;;

let list_to_v_def = cake_define
  `dataSem_list_to_v ts t [] = t /\
   dataSem_list_to_v ts t (h :: l) = dataSem_Block ts cons_tag [h;
     dataSem_list_to_v (ts + 1) t l]`;;

(* HOL4 overload (expanded in the port):
     Block_nil = Block 0 nil_tag [] *)

let with_fresh_ts_def = cake_define
  `^
     with_fresh_ts (s n f) = (match dataSem_state_tstamps s with
                              SOME ts -> f ts
                                (dataSem_state_tstamps_fupd (K (SOME
                                (ts + n))) s) | NONE -> f 0 s)`;;

let lim_safe_part_def = cake_define
  `(lim_safe_part lims (flatLang_Con pattern_semantics_tag xs) <=> (if
  xs = [] then pattern_semantics_tag < 2 EXP (arch_size lims) DIV 16
  else
                              LENGTH xs < 2 EXP limits_length_limit
                                lims /\
                              LENGTH xs < 2 EXP (arch_size lims - 4)
                                /\
                              4 * pattern_semantics_tag < 2 EXP
                                (arch_size lims) DIV 16 /\
                              4 * pattern_semantics_tag < 2 EXP
                                (arch_size lims - limits_length_limit
                                lims - 2))) /\
   (lim_safe_part lims (jsonLang_Int i) <=>
      (if small_num (limits_arch_64_bit lims) i then T else
         let il = bignum_size (limits_arch_64_bit lims) i in
           il <= 2 EXP limits_length_limit lims)) /\
   (lim_safe_part lims (mlsexp_Str s) <=>
      (let i = strlen s in
         i DIV (arch_size lims DIV 8) < 2 EXP (arch_size lims) DIV
           arch_size lims /\
         i DIV (arch_size lims DIV 8) + 1 < 2 EXP limits_length_limit
           lims /\
         small_num (limits_arch_64_bit lims) (&i))) /\
   (lim_safe_part lims (closLang_W64 w) <=> 1 <
     limits_length_limit lims)`;;

let lim_safe_def = cake_define
  `lim_safe lims x2 xs =
        match (x2,xs) with
          ((closLang_BlockOp (pattern_semantics_Cons
            pattern_semantics_tag)),xs) ->
       if xs = [] then pattern_semantics_tag < 2 EXP (arch_size lims)
         DIV 16 else
         LENGTH xs < 2 EXP limits_length_limit lims /\
         LENGTH xs < 2 EXP (arch_size lims - 4) /\
         4 * pattern_semantics_tag < 2 EXP (arch_size lims) DIV 16 /\
         4 * pattern_semantics_tag < 2 EXP (arch_size lims -
           limits_length_limit lims - 2)
        | ((closLang_MemOp (closLang_MutCons pattern_semantics_tag
          i)),xs) ->
         (LENGTH xs < 2 EXP limits_length_limit lims /\
          LENGTH xs < 2 EXP (arch_size lims - 4) /\
          4 * pattern_semantics_tag < 2 EXP (arch_size lims) DIV 16
            /\
          4 * pattern_semantics_tag < 2 EXP (arch_size lims -
            limits_length_limit lims - 2))
        | ((closLang_BlockOp (closLang_FromList
          pattern_semantics_tag)),xs) ->
      (match xs with [len; lv] ->
         (match dataSem_v_to_list lv with SOME n ->
             (if len = dataSem_Number (&(LENGTH n)) then small_num
               (limits_arch_64_bit lims) (&(LENGTH n)) /\
                  LENGTH n < 2 EXP limits_length_limit lims /\
                  LENGTH n < arch_size lims DIV 16 /\
                  4 * pattern_semantics_tag < 2 EXP (arch_size lims -
                    limits_length_limit lims - 2) /\
                  4 * pattern_semantics_tag < 2 EXP (arch_size lims)
                    DIV 16 else T) | _59 -> T) | _60 -> T)
        | ((closLang_BlockOp closLang_ListAppend),[x1; x2]) ->
      (match (dataSem_v_to_list x1,dataSem_v_to_list x2) with (SOME
        xs,SOME ys) ->
           1 < limits_length_limit lims /\
           3 * (SUC (LENGTH xs)) < 2 EXP (arch_size lims) DIV 8 | _61
             -> T)
        | ((closLang_BlockOp (closLang_ConsExtend
          pattern_semantics_tag)),(dataSem_Block _62 _63 xs' ::
          dataSem_Number lower :: dataSem_Number len :: dataSem_Number
          tot :: xs)) ->
           if lower < 0 \/ len < 0 \/ lower + len > &LENGTH xs' \/
              tot = 0 \/ ~(tot = &LENGTH xs + len) then T else LENGTH
                (xs ++ TAKE (num_of_int len) (DROP (num_of_int lower)
                xs')) < 2 EXP limits_length_limit lims /\
                LENGTH (xs ++ TAKE (num_of_int len) (DROP (num_of_int
                  lower) xs')) < 2 EXP (arch_size lims) DIV 16 /\
                4 * pattern_semantics_tag < 2 EXP (arch_size lims)
                  DIV 16 /\
                4 * pattern_semantics_tag < 2 EXP (arch_size lims -
                  limits_length_limit lims - 2)
        | ((closLang_IntOp word_bignum_Add),[dataSem_Number i1;
          dataSem_Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 + i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp word_bignum_Sub),[dataSem_Number i1;
          dataSem_Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 - i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp closLang_Mult),[dataSem_Number i1;
          dataSem_Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ 0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ 0 <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 * i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp word_bignum_Div),[dataSem_Number i1;
          dataSem_Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ 0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ 0 <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 / i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp tokens_Mod),[dataSem_Number i1;
          dataSem_Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ 0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ 0 <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 % i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_MemOp closLang_RefArray),[dataSem_Number i;
          dataSem_v]) ->
      (0 <= i /\
       num_of_int i < 2 EXP (arch_size lims) DIV 16 /\
       num_of_int i < 2 EXP limits_length_limit lims)
        | ((closLang_MemOp (closLang_RefByte _64)),(dataSem_Number i
          :: xs)) ->
      (0 <= i /\
       num_of_int i DIV (arch_size lims DIV 8) < 2 EXP (arch_size
         lims) DIV arch_size lims /\
       num_of_int i DIV (arch_size lims DIV 8) + 1 < 2 EXP
         limits_length_limit lims /\
       small_num (limits_arch_64_bit lims) i)
        | ((closLang_MemOp pattern_semantics_Ref),xs) ->
      (LENGTH xs < 2 EXP limits_length_limit lims /\
       LENGTH xs < 2 EXP arch_size lims DIV 16)
        | ((closLang_BlockOp (closLang_Build parts)),_65) ->
      EVERY (lim_safe_part lims) parts
        | ((closLang_WordOp WordToInt),_66) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp WordFromInt),_67) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (WordOpw closLang_W64 _68)),_69) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (WordShift closLang_W64 _70 _71)),_72) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (WordFromWord _73)),_74) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (FP_cmp _75)),_76) -> ?_has_fp_ops
      lims
        | ((closLang_WordOp (FP_uop _77)),_78) ->
      (?_has_fp_ops lims /\ (limits_arch_64_bit lims \/ 1 <
        limits_length_limit lims))
        | ((closLang_WordOp (FP_bop _79)),_80) ->
      (?_has_fp_ops lims /\ (limits_arch_64_bit lims \/ 1 <
        limits_length_limit lims))
        | ((closLang_WordOp (FP_top _81)),_82) ->
      (?_has_fp_ops lims /\ limits_has_fp_tops lims /\
        (limits_arch_64_bit lims \/ 1 < limits_length_limit lims))
        | (_83,_84) -> T`;;

let do_lim_safe = cake_define
  `^
     do_lim_safe (s flatLang_op vs) =
       dataSem_state_safe_for_space_fupd (K (
                              lim_safe (dataSem_state_limits s)
                                flatLang_op vs /\
                                dataSem_state_safe_for_space s))
     s`;;

let check_lim_def = cake_define
  `^
     check_lim (s n) = dataSem_state_safe_for_space_fupd (K (n < 2
       EXP limits_length_limit (dataSem_state_limits s) /\
       dataSem_state_safe_for_space
                              s))
        s`;;

let do_part_def = cake_define
  `dataSem_do_part m (jsonLang_Int i) s ts = (dataSem_Number i,s,ts) /\
   dataSem_do_part m (closLang_W64 w) s ts = (dataSem_Word64 w,s,ts)
     /\
   dataSem_do_part m (flatLang_Con t ns) s ts =
     (if ns = [] then (dataSem_Block 0 t [],s,ts) else match ts with
       NONE -> (dataSem_Block 0 t (MAP m ns),s,ts) | SOME n ->
       (dataSem_Block n t (MAP m ns),s,SOME (n + (1:num)))) /\
   dataSem_do_part m (mlsexp_Str t) s ts =
     (let ptr = (minimal (\ptr. ~(ptr IN domain s))) in
     let bytes = MAP (n2w o ORD) (explode t) in
       (dataSem_RefPtr T ptr,balanced_map_insert ptr
         (bvlSem_ByteArray T bytes) s,ts))`;;

let do_build_def = cake_define
  `dataSem_do_build m i [] s ts = (m (i - 1),s,ts) /\
   dataSem_do_build m i (p :: rest) s ts =
     (let (x,s1,ts1) = dataSem_do_part m p s ts in
       dataSem_do_build ((i =+ x) m) (i + 1) rest s1 ts1)`;;

let do_build_const_def = cake_define
  `dataSem_do_build_const xs s ts = dataSem_do_build (\x.
  dataSem_Number 0) 0 xs s ts`;;

let do_int_app_def = cake_define
  `dataSem_do_int_app x1 x2 =
      match (x1,x2) with
        ((word_depth_Const n),[]) ->
     (if small_enough_int n then SOME (dataSem_Number n) else NONE)
      | ((word_bignum_Add),[dataSem_Number n1; dataSem_Number n2]) ->
        SOME (dataSem_Number (n1 + n2))
      | ((word_bignum_Sub),[dataSem_Number n1; dataSem_Number n2]) ->
        SOME (dataSem_Number (n1 - n2))
      | ((closLang_Mult),[dataSem_Number n1; dataSem_Number n2]) ->
        SOME (dataSem_Number (n1 * n2))
      | ((word_bignum_Div),[dataSem_Number n1; dataSem_Number n2]) ->
       (if n2 = 0 then NONE else SOME (dataSem_Number (n1 / n2)))
      | ((tokens_Mod),[dataSem_Number n1; dataSem_Number n2]) ->
       (if n2 = 0 then NONE else SOME (dataSem_Number (n1 % n2)))
      | (((LESS)),[dataSem_Number n1; dataSem_Number n2]) -> SOME
        (dataSem_Boolv (n1 < n2))
      | ((closLang_LessEq),[dataSem_Number n1; dataSem_Number n2]) ->
        SOME (dataSem_Boolv (n1 <= n2))
      | (((GREATER)),[dataSem_Number n1; dataSem_Number n2]) -> SOME
        (dataSem_Boolv (n1 > n2))
      | ((closLang_GreaterEq),[dataSem_Number n1; dataSem_Number n2])
        -> SOME (dataSem_Boolv (n1 >= n2))
      | ((closLang_LessConstSmall n),[dataSem_Number i]) ->
         (if 0 <= i /\ i <= 1000000 /\ n < 1000000 then
           SOME (dataSem_Boolv (i < &n)) else NONE)
      | ((flatLang_op:closLang_int_op),(vs:dataSem_v list)) ->
        NONE`;;

let do_word_app_def = cake_define
  `dataSem_do_word_app x1 ws =
        match (x1,ws) with
          ((WordOpw ast_W8 opw),[dataSem_Number n1; dataSem_Number
            n2]) ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (dataSem_Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw closLang_W64 opw),[dataSem_Word64 w1;
          dataSem_Word64 w2]) ->
           SOME (dataSem_Word64 (opw_lookup opw w1 w2))
        | ((WordTest ast_W8 test),[dataSem_Number n1; dataSem_Number
          n2]) ->
          (if 0 <= n1 /\ n1 < 256 /\ 0 <= n2 /\ n2 < 256 then
             (match test with (EQUAL) -> SOME (dataSem_Boolv (n1 =
               n2)) | ast_Compare ast_Lt -> SOME (dataSem_Boolv (n1 <
               n2)) | ast_Compare ast_Leq -> SOME (dataSem_Boolv (n1 <=
               n2)) | _85 -> NONE) else NONE)
        | ((WordShift ast_W8 sh n),[dataSem_Number i]) ->
          (match some (\(w:word8). i = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (dataSem_Number (&(w2n (shift_lookup sh w
            n)))))
        | ((WordShift closLang_W64 sh n),[dataSem_Word64 w]) ->
          SOME (dataSem_Word64 (shift_lookup sh w n))
        | ((WordFromInt),[dataSem_Number i]) ->
          SOME (dataSem_Word64 (i2w i))
        | (WordToInt,[dataSem_Word64 w]) ->
          SOME (dataSem_Number (&(w2n w)))
        | ((WordFromWord T),[dataSem_Word64 w]) ->
          SOME (dataSem_Number (&(w2n ((w2w:word64->word8) w))))
        | ((WordFromWord F),[dataSem_Number n]) ->
          (match some (\(w:word8). n = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (dataSem_Word64 (w2w w)))
        | ((FP_top t_op),ws) ->
           (match ws with [dataSem_Word64 w1; dataSem_Word64 w2;
             dataSem_Word64 w3] ->
                (SOME (dataSem_Word64 (fp_top_comp t_op w1 w2 w3))) |
                  _86 -> NONE)
        | ((FP_bop bop),ws) ->
           (match ws with [dataSem_Word64 w1; dataSem_Word64 w2] ->
             (SOME (dataSem_Word64 (fp_bop_comp bop w1 w2))) | _87 ->
             NONE)
        | ((FP_uop uop),ws) ->
           (match ws with [dataSem_Word64 w] -> (SOME (dataSem_Word64
             (fp_uop_comp uop w))) | _88 -> NONE)
        | ((FP_cmp cmp),ws) ->
           (match ws with [dataSem_Word64 w1; dataSem_Word64 w2] ->
             (SOME (dataSem_Boolv (fp_cmp_comp cmp w1 w2))) | _89 ->
             NONE)
        | ((flatLang_op:closLang_word_op),(vs:dataSem_v list)) ->
          NONE`;;

let dest_Boolv_def = cake_define
  `dest_Boolv x1 =
      match x1 with
        (dataSem_Block _90 pattern_semantics_tag xs) ->
     (if xs = [] /\ pattern_semantics_tag < 2 then SOME
       (pattern_semantics_tag = 1) else NONE)
      | _91 -> NONE`;;

let dataSem_dest_thunk_ret_INDUCT,dataSem_dest_thunk_ret_RECURSION =
  define_datatype
  "dataSem_dest_thunk_ret = dataSem_BadRef | dataSem_NotThunk | \
   dataSem_IsThunk (thunk_mode) (dataSem_v)";;

let dest_thunk_def = cake_define
  `dataSem_dest_thunk v refs =
      match v with
        (dataSem_RefPtr b ptr) ->
     (match balanced_map_lookup ptr refs with NONE -> dataSem_BadRef
       | SOME (bvlSem_Thunk Evaluated dataSem_v) ->
          (if b then dataSem_BadRef else dataSem_IsThunk Evaluated
            dataSem_v) | SOME (bvlSem_Thunk NotEvaluated dataSem_v) ->
          (if b then dataSem_BadRef else dataSem_IsThunk NotEvaluated
            dataSem_v) | SOME _92 -> dataSem_NotThunk)
      | dataSem_v -> dataSem_NotThunk`;;

let bad_thunk_update_def = cake_define
  `dataSem_bad_thunk_update m dataSem_v refs <=>
     m = Evaluated /\ ~(dataSem_dest_thunk dataSem_v refs =
       dataSem_NotThunk)`;;

(* mirrors bviSem$finalise_cons, but threads the timestamp counter so
   that
   each block produced by the finalisation gets a fresh time stamp *)
(* HOL4 termination: \\ rw [] \\ imp_res_tac miscTheory.lookup_zero
   \\ fs [sptreeTheory.size_delete] *)
let finalise_cons_def = cake_define_wf
  `MEASURE (sptree_size o FST o SND)`
  `dataSem_finalise_cons v refs ts =
        match v with
          (dataSem_RefPtr b ptr) ->
       match balanced_map_lookup ptr refs with SOME (bvlSem_MutBlock
         pattern_semantics_tag finalised l c r) ->
           (if ~finalised then
             (match dataSem_finalise_cons c (balanced_map_delete ptr
               refs) ts with SOME (c',refs',ts') ->
                  SOME (dataSem_Block (match ts' with NONE -> 0 |
                    SOME n -> n) pattern_semantics_tag (l ++ [c'] ++ r),
                        balanced_map_insert ptr (bvlSem_MutBlock
                          pattern_semantics_tag T l c r) refs',
                        OPTION_MAP SUC ts') | NONE -> NONE) else
                          NONE) | SOME res -> SOME (dataSem_RefPtr b
                          ptr,refs,ts) | NONE -> NONE
        | dataSem_v -> SOME (dataSem_v,refs,ts)`;;

let do_app_aux_def = cake_define
  `^ (^
     (do_app_aux flatLang_op) vs) s =
       (match (flatLang_op,vs) with (labLang_Label l,xs) ->
           (match xs with [] -> (if l IN domain (?_code s) then
                      Rval (dataSem_CodePtr l,s) else ((Rerr (Rabort
                        Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                        #string+dataSem_v#string)) | _93 -> ((Rerr
                        (Rabort
                        Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                        #string+dataSem_v#string)) | (closLang_GlobOp
                        GlobalsPtr,xs) ->
           (match xs with [] -> (match dataSem_state_global s with
             SOME p -> Rval (dataSem_RefPtr T p,s) | NONE -> ((Rerr
             (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | _94 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_GlobOp (Global n),xs) ->
           (match xs with [] -> (match dataSem_state_global s with
             SOME ptr ->
                         (match sptree_lookup ptr (?_refs s) with
                           SOME (bvlSem_ValueArray xs) ->
                              (if n < LENGTH xs then Rval (EL n xs,s)
                                else ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _95 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | NONE -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _96 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | (closLang_GlobOp (SetGlobal
                                n),xs) ->
           (match xs with [x] -> (match dataSem_state_global s with
             SOME ptr ->
                          (match balanced_map_lookup ptr (?_refs s)
                            with SOME (bvlSem_ValueArray xs) ->
                              (if n < LENGTH xs then Rval
                                (dataSem_Unit,?_refs_fupd (K
                                (balanced_map_insert ptr
                              (bvlSem_ValueArray (LUPDATE x n xs))
                                (?_refs s))) s) else ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _97 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | NONE -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _98 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | (closLang_GlobOp
                                (SetGlobalsPtr),xs) ->
           (match xs with [dataSem_RefPtr T p] -> Rval
             (dataSem_Unit,dataSem_state_global_fupd (K (SOME p)) s) |
             _99 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_BlockOp (closLang_FromList
             n),xs) ->
           (match xs with [len; lv] ->
               (match dataSem_v_to_list lv with SOME [] -> (if len =
                 dataSem_Number 0 then Rval (dataSem_Block 0 n [],s)
                 else ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | SOME vs -> (if len =
                 dataSem_Number (&(LENGTH vs)) then with_fresh_ts s 1
                              (\ts s'. Rval (dataSem_Block ts n vs,
                              check_lim (s') (LENGTH vs))) else
                                ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _100 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _101 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | (closLang_MemOp
                                (closLang_RefByte f'),xs) ->
           (match xs with [dataSem_Number i; dataSem_Number b] ->
               (if 0 <= i /\ (?(w:word8). b = &(w2n w)) then
                 let ptr = (minimal (\ptr. ~(ptr IN domain (?_refs
                   s)))) in
                   Rval (dataSem_RefPtr T ptr,?_refs_fupd (K
                     (balanced_map_insert ptr
                     (bvlSem_ByteArray f' (REPLICATE (num_of_int i)
                       (i2w b))) (?_refs s))) s) else Rerr (Rabort
                       Rtype_error)) | _102 -> Rerr (Rabort
                       Rtype_error)) | (closLang_GlobOp
                       AllocGlobal,_103) -> Rerr (Rabort Rtype_error) |
                       (closLang_MemOp closLang_FromListByte,_104) ->
                       Rerr (Rabort Rtype_error) | (closLang_MemOp
                       closLang_ConcatByteVec,_105) -> Rerr (Rabort
                       Rtype_error) | (closLang_MemOp (closLang_CopyByte
                       T),_106) -> Rerr (Rabort Rtype_error) |
                       (closLang_BlockOp (closLang_Build parts),[]) ->
           (match dataSem_do_build_const parts (?_refs s)
             (dataSem_state_tstamps s) with (dataSem_v,s1,ts1) -> Rval
             (dataSem_v,dataSem_state_tstamps_fupd (K ts1) (?_refs_fupd
             (K s1) s))) | (closLang_BlockOp (pattern_semantics_Cons
             pattern_semantics_tag),xs) -> (if xs = [] then Rval
             (dataSem_Block 0 pattern_semantics_tag [],s) else
             with_fresh_ts s 1
                              (\ts s'. Rval (dataSem_Block ts
                                pattern_semantics_tag xs,
                              check_lim s' (LENGTH xs)))) |
                                (closLang_BlockOp (closLang_ConsExtend
                                pattern_semantics_tag),dataSem_Block x y
                                xs' :: dataSem_Number lower ::
                                dataSem_Number len :: dataSem_Number tot
                                :: xs) ->
           (if lower < 0 \/ len < 0 \/ lower + len > &LENGTH xs' \/
              tot = 0 \/ ~(tot = &LENGTH xs + len) then
             ((Rerr (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
               +dataSem_v#string) else with_fresh_ts s 1
                              (\ts s'.
                              let l = (xs ++ TAKE (num_of_int len)
                                (DROP (num_of_int lower) xs')) in Rval
                                (dataSem_Block ts pattern_semantics_tag
                                l,
                              check_lim s' (LENGTH l)))) |
                                (closLang_BlockOp (closLang_ConsExtend
                                pattern_semantics_tag),_107) -> ((Rerr
                                (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string) | (closLang_MemOp
                                flatLang_El,[dataSem_Block _108
                                pattern_semantics_tag xs; dataSem_Number
                                i]) ->
           (if 0 <= i /\ num_of_int i < LENGTH xs then Rval (EL
             (num_of_int i) xs,s) else ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_MemOp
             flatLang_El,[dataSem_RefPtr _109 ptr; dataSem_Number i]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval (EL
                 (num_of_int i) xs,s) else ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | _110 -> ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | (closLang_BlockOp
                 (closLang_ElemAt n),[dataSem_Block _111
                 pattern_semantics_tag xs]) ->
           (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
             (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_BlockOp (closLang_ElemAt
             n),[dataSem_RefPtr _112 ptr]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_ValueArray xs) ->
               (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
                 (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | _113 -> ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | (closLang_BlockOp
                 (closLang_BoolTest test),[v1; v2]) ->
           (match (dest_Boolv v1,dest_Boolv v2) with (SOME b1,SOME
             b2) -> Rval (dataSem_Boolv (b1 = b2),s) | _114 -> ((Rerr
             (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_BlockOp
             closLang_BoolNot,[v1]) ->
           (match dest_Boolv v1 with SOME b1 -> Rval (dataSem_Boolv
             (~b1),s) | _115 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_BlockOp
             closLang_ListAppend,[x1; x2]) ->
           (match (dataSem_v_to_list x1,dataSem_v_to_list x2) with
             (SOME xs,SOME ys) -> ^
                with_fresh_ts (s (LENGTH xs)
                (\ts s'. Rval (dataSem_list_to_v ts x2 xs,
                              check_lim (s') 2))) | _116 -> ((Rerr
                                (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | (closLang_BlockOp
                                closLang_LengthBlock,[dataSem_Block _117
                                pattern_semantics_tag xs]) ->
           Rval (dataSem_Number (&LENGTH xs),s) | (closLang_MemOp
             closLang_Length,[dataSem_RefPtr _118 ptr]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_ValueArray xs) ->
                 Rval (dataSem_Number (&LENGTH xs),s) | _119 ->
                   ((Rerr (Rabort
                   Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                   #string+dataSem_v#string)) | (closLang_MemOp
                   closLang_LengthByte,[dataSem_RefPtr _120 ptr]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_ByteArray _121 xs) ->
                 Rval (dataSem_Number (&LENGTH xs),s) | _122 ->
                   ((Rerr (Rabort
                   Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                   #string+dataSem_v#string)) | (closLang_MemOp
                   closLang_RefArray,[dataSem_Number i; dataSem_v]) ->
           (if 0 <= i then
             let ptr = (minimal (\ptr. ~(ptr IN domain (?_refs s))))
               in
               Rval (dataSem_RefPtr T ptr,?_refs_fupd (K
                 (balanced_map_insert ptr
                              (bvlSem_ValueArray (REPLICATE
                                (num_of_int i) dataSem_v)) (?_refs s)))
                     s) else ((Rerr (Rabort
                       Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                       #string+dataSem_v#string)) | (closLang_MemOp
                       closLang_DerefByte,[dataSem_RefPtr _123 ptr;
                       dataSem_Number i]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_ByteArray _124 ws) ->
               (if 0 <= i /\ i < &LENGTH ws then Rval (dataSem_Number
                 (&(w2n (EL (num_of_int i) ws))),s) else ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | _125 -> ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | (closLang_MemOp
                 closLang_UpdateByte,[dataSem_RefPtr _126 ptr;
                 dataSem_Number i; dataSem_Number b]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_ByteArray f' bs) ->
               (if 0 <= i /\ i < &LENGTH bs /\ (?(w:word8). b = &(w2n
                 w)) then
                  Rval (dataSem_Unit,?_refs_fupd (K
                    (balanced_map_insert ptr
                    (bvlSem_ByteArray f' (LUPDATE (i2w b) (num_of_int
                      i) bs)) (?_refs s))) s) else ((Rerr (Rabort
                      Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                      #string+dataSem_v#string)) | _127 -> ((Rerr
                      (Rabort
                      Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                      #string+dataSem_v#string)) | (closLang_MemOp
                      closLang_XorByte,[dataSem_RefPtr _128 dst;
                      dataSem_RefPtr _129 src]) ->
           (match (balanced_map_lookup src (?_refs
             s),balanced_map_lookup dst (?_refs s)) with (SOME
             (bvlSem_ByteArray _130 ws),SOME (bvlSem_ByteArray f' ds))
             ->
              (match xor_bytes ws ds with SOME ds1 -> Rval
                (dataSem_Unit,?_refs_fupd (K (balanced_map_insert dst
                (bvlSem_ByteArray f' ds1) (?_refs s))) s) | NONE ->
                ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | _131 -> ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | (closLang_MemOp
                (closLang_StringCmp b cmp),[dataSem_RefPtr _132 s1;
                dataSem_RefPtr _133 s2]) ->
           (match (balanced_map_lookup s1 (?_refs
             s),balanced_map_lookup s2 (?_refs s)) with (SOME
             (bvlSem_ByteArray _134 ws1),SOME (bvlSem_ByteArray _135
             ws2)) ->
                (let s1 = implode (MAP (CHR o w2n) ws1) in
                 let s2 = implode (MAP (CHR o w2n) ws2) in
                   Rval (dataSem_Boolv (str_cmp b cmp s1 s2),s)) |
                     _136 -> ((Rerr (Rabort
                     Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                     #string+dataSem_v#string)) | (closLang_MemOp
                     (closLang_CopyByte F),[dataSem_RefPtr _137 src;
                     dataSem_Number srcoff; dataSem_Number len;
                     dataSem_RefPtr _138 dst; dataSem_Number dstoff]) ->
           (match (balanced_map_lookup src (?_refs
             s),balanced_map_lookup dst (?_refs s)) with (SOME
             (bvlSem_ByteArray _139 ws),SOME (bvlSem_ByteArray fl ds))
             ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff))
                with SOME ds -> Rval (dataSem_Unit,?_refs_fupd (K
                (balanced_map_insert dst (bvlSem_ByteArray fl ds)
                (?_refs s))) s) | NONE -> ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | _140 -> ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | (closLang_BlockOp (closLang_TagEq
                n),[dataSem_Block _141 pattern_semantics_tag xs]) ->
           Rval (dataSem_Boolv (pattern_semantics_tag = n),s) |
             (closLang_BlockOp (flatLang_LenEq l),[dataSem_Block _142
             pattern_semantics_tag xs]) ->
           Rval (dataSem_Boolv (LENGTH xs = l),s) | (closLang_BlockOp
             (pattern_semantics_TagLenEq n l),[dataSem_Block _143
             pattern_semantics_tag xs]) ->
           Rval (dataSem_Boolv (pattern_semantics_tag = n /\ LENGTH
             xs = l),s) | (closLang_BlockOp (closLang_EqualConst
             p),[x1]) ->
           (match p with jsonLang_Int i -> (match x1 with
             dataSem_Number j -> Rval (dataSem_Boolv (i = j),s) | _144
             -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | closLang_W64 i -> (match x1 with
             dataSem_Word64 j -> Rval (dataSem_Boolv (i = j),s) | _145
             -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | mlsexp_Str i -> (match x1 with
             dataSem_RefPtr _146 p ->
                          (match balanced_map_lookup p (?_refs s)
                            with SOME (bvlSem_ByteArray T j) ->
                             Rval (dataSem_Boolv (j = MAP (n2w o ORD)
                               (explode i)),s) | _147 -> ((Rerr (Rabort
                               Rtype_error)):(dataSem_v#('c
                               ,'ffi)dataSem_state)#string+dataSem_v
                               #string)) | _148 -> ((Rerr (Rabort
                               Rtype_error)):(dataSem_v#('c
                               ,'ffi)dataSem_state)#string+dataSem_v
                               #string)) | _149 -> ((Rerr (Rabort
                               Rtype_error)):(dataSem_v#('c
                               ,'ffi)dataSem_state)#string+dataSem_v
                               #string)) | (closLang_BlockOp
                               (EQUAL),[x1; x2]) ->
           (match dataSem_do_eq (?_refs s) x1 x2 with Eq_val b ->
             Rval (dataSem_Boolv b,s) | _150 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_MemOp
             pattern_semantics_Ref,xs) ->
           (let ptr = (minimal (\ptr. ~(ptr IN domain (?_refs s))))
             in
             Rval (dataSem_RefPtr T ptr,?_refs_fupd (K
               (balanced_map_insert ptr (bvlSem_ValueArray xs) (?_refs
               s))) s)) | (closLang_MemOp
               closLang_Update,[dataSem_RefPtr _151 ptr; dataSem_Number
               i; x]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval
                 (dataSem_Unit,?_refs_fupd (K (balanced_map_insert ptr
                              (bvlSem_ValueArray (LUPDATE x
                                (num_of_int i) xs)) (?_refs s))) s) else
                                ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _152 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | (closLang_MemOp
                                (closLang_MutCons pattern_semantics_tag
                                i),xs) ->
           (let ptr = (minimal (\ptr. ~(ptr IN domain (?_refs s))))
             in
              if i >= LENGTH xs then ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string) else
                let l = TAKE i xs in
                let c = EL i xs in
                let r = DROP (i + 1) xs in
                  Rval (dataSem_RefPtr F ptr,?_refs_fupd (K
                    (balanced_map_insert ptr (bvlSem_MutBlock
                    pattern_semantics_tag F l c r) (?_refs s)))
                        s)) | (closLang_MemOp
                          closLang_UpdateCons,[dataSem_RefPtr _153 ptr;
                          dataSem_Number i; x]) ->
           (match balanced_map_lookup ptr (?_refs s) with SOME
             (bvlSem_MutBlock pattern_semantics_tag finalised l c r) ->
                (if ~(i = &LENGTH l) \/ finalised then ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string) else
                  Rval (dataSem_Unit,?_refs_fupd (K
                    (balanced_map_insert ptr (bvlSem_MutBlock
                    pattern_semantics_tag F l x r) (?_refs s))) s)) |
                    _154 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (closLang_MemOp
                    closLang_FinaliseCons,[x]) ->
           (match dataSem_finalise_cons x (?_refs s)
             (dataSem_state_tstamps s) with SOME (dataSem_v,refs',ts')
             ->
                Rval (dataSem_v,dataSem_state_tstamps_fupd (K ts')
                  (?_refs_fupd (K refs') s)) | NONE -> ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string)) | (closLang_IntOp intop,vs)
                  ->
           (match dataSem_do_int_app intop vs with SOME res -> Rval
             (res,s) | _155 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (closLang_WordOp wordop,vs) ->
           (match dataSem_do_word_app wordop vs with SOME res -> Rval
             (res,s) | _156 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (wordLang_FFI n,[dataSem_RefPtr _157
             cptr; dataSem_RefPtr _158 ptr]) ->
           (match (balanced_map_lookup cptr (?_refs
             s),balanced_map_lookup ptr (?_refs s)) with (SOME
             (bvlSem_ByteArray T cws),SOME (bvlSem_ByteArray F ws)) ->
              (match call_FFI (?_ffi s) (ExtCall n) cws ws with
                FFI_return ffi' ws' ->
                   Rval (dataSem_Unit,?_ffi_fupd (K ffi')
                     (?_refs_fupd (K (balanced_map_insert ptr
                     (bvlSem_ByteArray F ws') (?_refs s)))
                         s)) | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome))) | _159 ->
                     ((Rerr (Rabort
                     Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                     #string+dataSem_v#string)) | (closLang_BlockOp
                     closLang_BoundsCheckBlock,xs) ->
           (match xs with [dataSem_Block _160 pattern_semantics_tag
             ys; dataSem_Number i] ->
                  Rval (dataSem_Boolv (0 <= i /\ i < &LENGTH ys),s) |
                    _161 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (closLang_MemOp
                    (closLang_BoundsCheckByte loose),xs) ->
           (match xs with [dataSem_RefPtr _162 ptr; dataSem_Number i]
             ->
             (match balanced_map_lookup ptr (?_refs s) with SOME
               (bvlSem_ByteArray _163 ws) ->
                  Rval (dataSem_Boolv (0 <= i /\ (if loose then (<=)
                    else (<)) i (&LENGTH ws)),s) | _164 -> ((Rerr
                    (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | _165 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (closLang_MemOp
                    closLang_BoundsCheckArray,xs) ->
           (match xs with [dataSem_RefPtr _166 ptr; dataSem_Number i]
             ->
             (match balanced_map_lookup ptr (?_refs s) with SOME
               (bvlSem_ValueArray ws) ->
                  Rval (dataSem_Boolv (0 <= i /\ i < &LENGTH ws),s) |
                    _167 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | _168 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (closLang_MemOp
                    closLang_ConfigGC,[dataSem_Number _169;
                    dataSem_Number _170]) -> (Rval (dataSem_Unit,s)) |
                    (closLang_ThunkOp th_op,vs) ->
           (match (th_op,vs) with (AllocThunk m,[dataSem_v]) ->
                (if dataSem_bad_thunk_update m dataSem_v (?_refs s)
                  then ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string) else
                 let ptr = (minimal (\ptr. ~(ptr IN domain (?_refs
                   s)))) in
                   Rval (dataSem_RefPtr F ptr,?_refs_fupd (K
                     (balanced_map_insert ptr (bvlSem_Thunk m dataSem_v)
                     (?_refs s)))
                         s)) | (UpdateThunk m,[dataSem_RefPtr F ptr;
                           dataSem_v]) ->
                (if dataSem_bad_thunk_update m dataSem_v (?_refs s)
                  then ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string) else
                 match balanced_map_lookup ptr (?_refs s) with SOME
                   (bvlSem_Thunk NotEvaluated _171) ->
                    Rval (dataSem_Unit,?_refs_fupd (K
                      (balanced_map_insert ptr (bvlSem_Thunk m
                      dataSem_v) (?_refs s))) s) | _172 -> ((Rerr
                      (Rabort
                      Rtype_error)):(dataSem_v#('c
                      ,'ffi)dataSem_state)#string+dataSem_v#string))
                      | _173 -> ((Rerr (Rabort
                      Rtype_error)):(dataSem_v#('c
                      ,'ffi)dataSem_state)#string+dataSem_v#string))
                      | _174 -> ((Rerr (Rabort
                      Rtype_error)):(dataSem_v#('c
                      ,'ffi)dataSem_state)#string+dataSem_v#string))`;;

(* HOL4 overload (expanded in the port):
     do_app_safe = λop vs s. if allowed_op op (LENGTH vs)
              then (do_space_safe op vs s ∧ lim_safe s.limits op vs
                    ∧ the F (OPTION_MAP ($> s.limits.stack_limit)
                           (OPTION_MAP2 $+ (stack_consumed
                             s.stack_frame_sizes s.limits op vs)
                             (OPTION_MAP2 $+ (size_of_stack s.stack)
                               s.locals_size))))
              else F *)

(* HOL4 overload (expanded in the port):
     do_app_peak = λop vs s. if op = Install
              then s.peak_heap_length
              else if MEM op [IntOp Greater; IntOp GreaterEq] then
                s.peak_heap_length
              else do_space_peak op vs s *)

let do_app_def = cake_define
  `^
     (semanticPrimitives_do_app flatLang_op vs) s =
       (if flatLang_op = labLang_Install then do_install vs
         (dataSem_state_stack_frame_sizes_fupd (K LN)
         (dataSem_state_stack_max_fupd (K NONE) s)) else
       if MEM flatLang_op [closLang_IntOp (GREATER); closLang_IntOp
         closLang_GreaterEq] then ((Rerr (Rabort
         Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
         +dataSem_v#string) else
       match do_space flatLang_op vs s with NONE -> ((Rerr (Rabort
         Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
         +dataSem_v#string) | SOME s1 -> do_app_aux flatLang_op vs
         (do_stack flatLang_op vs (do_lim_safe s1 flatLang_op vs)))`;;

let get_var_def = cake_define
  `dataSem_get_var dataSem_v = sptree_lookup dataSem_v`;;

let get_vars_def = cake_define
  `(dataSem_get_vars [] s = SOME []) /\
   (dataSem_get_vars (dataSem_v :: vs) s =
      (match dataSem_get_var dataSem_v s with NONE -> NONE | SOME
        x -> (match dataSem_get_vars vs s with NONE -> NONE | SOME xs
        -> SOME (x :: xs))))`;;

let set_var_def = cake_define
  `dataSem_set_var dataSem_v x s = (dataSem_state_locals_fupd (K
  (balanced_map_insert dataSem_v x (dataSem_state_locals s))) s)`;;

let dec_clock_def = cake_define
  `dataSem_dec_clock s = ?_clock_fupd (K (?_clock s - 1)) s`;;

let fix_clock_def = cake_define
  `dataSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;

let flush_state_def = cake_define
  `^
      (flush_state T) s  =
        match  with
           -> dataSem_state_locals_size_fupd (K (SOME 0))
             (?_stack_fupd (K []) (dataSem_state_locals_fupd (K LN) s))
        |  -> dataSem_state_locals_size_fupd (K (SOME 0))
          (dataSem_state_locals_fupd (K LN) s)`;;

let call_env_def = cake_define
  `^
     (call_env args balanced_map_size) s =
       (let new_stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max
         s)
                              (OPTION_MAP2 (+) (size_of_stack
                                (?_stack s)) balanced_map_size) in let
           stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit
             (dataSem_state_limits s))) new_stack_max) in
             dataSem_state_safe_for_space_fupd (K
             (dataSem_state_safe_for_space s /\ stack_safe))
             (dataSem_state_stack_max_fupd (K new_stack_max)
             (dataSem_state_locals_size_fupd (K balanced_map_size)
             (dataSem_state_locals_fupd (K (fromList args))
         s))))`;;

let push_env_def = cake_define
  `^ (push_env env F) s  =
        match  with
           ->
       let stack = dataSem_Env (dataSem_state_locals_size s) env ::
         ?_stack s in let
           stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max s)
             (size_of_stack stack) in let
           stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit
             (dataSem_state_limits s))) stack_max) in
             dataSem_state_safe_for_space_fupd (K
             (dataSem_state_safe_for_space s /\ stack_safe))
             (dataSem_state_stack_max_fupd (K stack_max) (?_stack_fupd
             (K stack) s))
        |  ->
      let stack = dataSem_Exc (dataSem_state_locals_size s) env
        (dataSem_state_handler s) :: ?_stack s in let
          stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max s)
            (size_of_stack stack) in let
          stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit
            (dataSem_state_limits s))) stack_max) in
            dataSem_state_safe_for_space_fupd (K
            (dataSem_state_safe_for_space s /\ stack_safe))
            (dataSem_state_handler_fupd (K (LENGTH (?_stack s)))
            (dataSem_state_stack_max_fupd (K stack_max) (?_stack_fupd
            (K stack) s)))`;;

let pop_env_def = cake_define
  `^
     pop_env s =
       (match ?_stack s with (dataSem_Env ss e :: xs) ->
           SOME (dataSem_state_locals_size_fupd (K ss) (?_stack_fupd
             (K xs) (dataSem_state_locals_fupd (K e) s))) | (dataSem_Exc
             ss e n :: xs) ->
           SOME (dataSem_state_handler_fupd (K n)
             (dataSem_state_locals_size_fupd (K ss) (?_stack_fupd (K
             xs) (dataSem_state_locals_fupd (K e) s)))) | _175 ->
             NONE)`;;

let jump_exc_def = cake_define
  `^
     jump_exc s =
       (if dataSem_state_handler s < LENGTH (?_stack s) then
         match LASTN (dataSem_state_handler s + 1) (?_stack s) with
           dataSem_Exc ss e n :: xs ->
             SOME (dataSem_state_locals_size_fupd (K ss)
               (?_stack_fupd (K xs) (dataSem_state_locals_fupd (K e)
               (dataSem_state_handler_fupd (K n) s)))) | _176 -> NONE
               else NONE)`;;

let cut_env_def = cake_define
  `dataSem_cut_env (name_set:one spt) env =
     (if domain name_set SUBSET domain env then SOME (mk_wf (inter
       env name_set)) else NONE)`;;

let cut_state_def = cake_define
  `^
     (cut_state names) s =
       (match dataSem_cut_env names (dataSem_state_locals s) with
         NONE -> NONE | SOME env -> SOME (dataSem_state_locals_fupd
         (K env) s))`;;

let cut_state_opt_def = cake_define
  `cut_state_opt names s =
     (match names with NONE -> SOME s | SOME names -> cut_state
       names s)`;;

let find_code_def = cake_define
  `(dataSem_find_code (SOME p) args code ssize =
      (match sptree_lookup p code with NONE -> NONE | SOME
        (arity,flatLang_exp) ->
         (if LENGTH args = arity then SOME
           (args,flatLang_exp,balanced_map_lookup p ssize) else NONE)))
           /\ (dataSem_find_code NONE args code ssize =
      (if args = [] then NONE else
        match LAST args with dataSem_CodePtr loc ->
            (match sptree_lookup loc code with NONE -> NONE | SOME
              (arity,flatLang_exp) ->
                (if LENGTH args = arity + 1 then SOME (FRONT
                  args,flatLang_exp,balanced_map_lookup loc ssize)
                  else NONE)) | other -> NONE))`;;

let isBool_def = cake_define
  `isBool b x2 =
      match x2 with
        (dataSem_Block _177 pattern_semantics_tag []) -> (bool_to_tag
          b = pattern_semantics_tag)
      | _178 -> F`;;

let install_sfs_def = cake_define
  `^
     (install_sfs flatLang_op) s =
       dataSem_state_safe_for_space_fupd (K (~(flatLang_op =
       closLang_Install) /\ dataSem_state_safe_for_space s)) s`;;

let set_vars_def = cake_define
  `set_vars ns vs s = (dataSem_state_locals_fupd (K
  (balanced_map_union (fromAList (ZIP (ns,vs))) (dataSem_state_locals
  s))) s)`;;

(* HOL4 termination: \\ rpt strip_tac \\ simp[dec_clock_def] \\
   imp_res_tac fix_clock_IMP \\ imp_res_tac (GSYM fix_clock_IMP) \\
   FULL_SIMP_TAC (srw_ss()) [set_var_def,push_env_clock,
   call_env_def,LET_THM] \\ fs [dec_clock_def] *)
let evaluate_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE prog_size)
                            (\(xs,s). (?_clock s,xs)))`
  `(dataSem_evaluate (word_bignum_Skip,s) = (NONE,s)) /\
   (dataSem_evaluate (wordLang_Move dest src,s) =
      (match dataSem_get_var src (dataSem_state_locals s) with NONE
        -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME dataSem_v ->
        (NONE,dataSem_set_var dest dataSem_v s))) /\
   (dataSem_evaluate (word_bignum_Assign dest flatLang_op args
     names_opt,s) =
      (if op_requires_names flatLang_op = IS_NONE names_opt then
        (SOME (Rerr (Rabort Rtype_error)),s) else
        match dataSem_get_vars args (dataSem_state_locals s) with
          NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs ->
            (match cut_state_opt names_opt s with NONE -> (SOME (Rerr
              (Rabort Rtype_error)),s) | SOME s ->
                (match semanticPrimitives_do_app flatLang_op xs s
                  with Rerr e -> (SOME (Rerr e),flush_state T
                  (install_sfs flatLang_op s)) | Rval (dataSem_v,s) ->
                    (NONE,dataSem_set_var dest dataSem_v (install_sfs
                      flatLang_op s)))))) /\
   (dataSem_evaluate (wordLang_Tick,s) =
      (if ?_clock s = 0 then (SOME (Rerr (Rabort
        Rtimeout_error)),flush_state T s) else (NONE,dataSem_dec_clock
        s))) /\
   (dataSem_evaluate (dataLang_MakeSpace k names,s) =
      (match dataSem_cut_env names (dataSem_state_locals s) with NONE
        -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME env ->
        (NONE,add_space (dataSem_state_locals_fupd (K env) s) k))) /\
   (dataSem_evaluate (flatLang_Raise n,s) =
      (match dataSem_get_var n (dataSem_state_locals s) with NONE ->
        (SOME (Rerr (Rabort Rtype_error)),s) | SOME x ->
        (match jump_exc s with NONE -> (SOME (Rerr (Rabort
          Rtype_error)),s) | SOME s -> (SOME (Rerr (Rraise x)),s)))) /\
   (dataSem_evaluate (wordLang_Return ns,s) =
      (match dataSem_get_vars ns (dataSem_state_locals s) with NONE
        -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs -> (SOME (Rval
        xs),flush_state F s))) /\
   (dataSem_evaluate (linear_scan_Seq c1 c2,s) =
      (let (res,s1) = dataSem_fix_clock s (dataSem_evaluate (c1,s))
        in
        if res = NONE then dataSem_evaluate (c2,s1) else (res,s1)))
          /\
   (dataSem_evaluate (pattern_semantics_If n c1 c2,s) =
      (match dataSem_get_var n (dataSem_state_locals s) with NONE ->
        (SOME (Rerr (Rabort Rtype_error)),s) | SOME x -> (if isBool T x
        then dataSem_evaluate (c1,s) else
                  if isBool F x then dataSem_evaluate (c2,s) else
                    (SOME (Rerr (Rabort Rtype_error)),s)))) /\
   (dataSem_evaluate (bvl_Force ret loc src,s) =
      (match dataSem_get_var src (dataSem_state_locals s) with NONE
        -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME thunk_v ->
        (match dataSem_dest_thunk thunk_v (?_refs s) with
          dataSem_BadRef -> (SOME (Rerr (Rabort Rtype_error)),s) |
          dataSem_NotThunk -> (SOME (Rerr (Rabort Rtype_error)),s) |
          dataSem_IsThunk Evaluated dataSem_v ->
           (match ret with NONE -> (SOME (Rval
             [dataSem_v]),flush_state F s) | SOME (dest,names) ->
              (match dataSem_cut_env names (dataSem_state_locals s)
                with NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME
                env -> (NONE,dataSem_set_var dest dataSem_v
                (dataSem_state_locals_fupd (K env) s)))) |
                dataSem_IsThunk NotEvaluated f' ->
            (match dataSem_find_code (SOME loc) [thunk_v; f'] (?_code
              s) (dataSem_state_stack_frame_sizes s) with NONE -> (SOME
              (Rerr (Rabort Rtype_error)),s) | SOME
              (args1,labLang_prog,ss) ->
               (match ret with NONE ->
                   (if ?_clock s = 0 then
                      (SOME (Rerr (Rabort
                        Rtimeout_error)),dataSem_state_locals_fupd (K
                        LN) (?_stack_fupd (K [])
                            s)) else
                      (match dataSem_evaluate (labLang_prog,call_env
                        args1 ss (dataSem_dec_clock s)) with (NONE,s) ->
                        (SOME (Rerr (Rabort Rtype_error)),s) | (SOME
                        res,s) -> (SOME res,s))) | SOME (dest,names) ->
                  (match dataSem_cut_env names (dataSem_state_locals
                    s) with NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                    | SOME env ->
                       (let s1 = call_env args1 ss (push_env env F
                         (dataSem_dec_clock s)) in
                         if ?_clock s = 0 then
                           (SOME (Rerr (Rabort
                             Rtimeout_error)),dataSem_state_locals_fupd
                             (K LN) (?_stack_fupd (K [])
                            s1)) else
                           (match dataSem_fix_clock s1
                             (dataSem_evaluate (labLang_prog,s1)) with
                             (SOME (Rval xs),s2) ->
                              (if LENGTH xs = 1 then
                              match pop_env s2 with NONE -> (SOME
                                (Rerr (Rabort Rtype_error)),s2) | SOME
                                s1 -> (NONE,dataSem_set_var dest (HD xs)
                                s1) else
                              (SOME (Rerr (Rabort Rtype_error)),s2))
                                | (NONE,s) -> (SOME (Rerr (Rabort
                                Rtype_error)),s) | res -> res)))))))) /\
   (dataSem_evaluate (labLang_Call ret dest args handler,s) =
      (match dataSem_get_vars args (dataSem_state_locals s) with NONE
        -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs ->
        (match dataSem_find_code dest xs (?_code s)
          (dataSem_state_stack_frame_sizes s) with NONE -> (SOME (Rerr
          (Rabort Rtype_error)),s) | SOME (args1,labLang_prog,ss) ->
           (match ret with NONE ->
              (if handler = NONE then
                if ?_clock s = 0 then (SOME (Rerr (Rabort
                  Rtimeout_error)),
                      flush_state T s) else
                  (match dataSem_evaluate (labLang_prog,call_env
                    args1 ss (dataSem_dec_clock s)) with (NONE,s) ->
                    (SOME (Rerr (Rabort Rtype_error)),s) | (SOME res,s)
                    -> (SOME res,s)) else (SOME (Rerr (Rabort
                    Rtype_error)),s)) | SOME (ns,names) ->
              (if ~ALL_DISTINCT ns then (SOME (Rerr (Rabort
                Rtype_error)),s) else
              (match dataSem_cut_env names (dataSem_state_locals s)
                with NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME
                env ->
                 (let s1 = call_env args1 ss
                         (push_env env (IS_SOME handler)
                           (dataSem_dec_clock s)) in if ?_clock s = 0
                           then (SOME (Rerr (Rabort
                           Rtimeout_error)),dataSem_state_locals_fupd (K
                           LN) (?_stack_fupd (K [])
                         s1)) else (match dataSem_fix_clock s1
                           (dataSem_evaluate (labLang_prog,s1)) with
                           (SOME (Rval xs),s2) ->
                            (if LENGTH xs = LENGTH ns then
                              (match pop_env s2 with NONE -> (SOME
                                (Rerr (Rabort Rtype_error)),s2) | SOME
                                s1 -> (NONE,set_vars ns xs s1)) else
                              (SOME (Rerr (Rabort Rtype_error)),s2))
                                | (SOME (Rerr (Rraise x)),s2) ->
                            (match handler with NONE -> (SOME
                              (Rerr (Rraise x)),s2) | SOME (n,h) ->
                              dataSem_evaluate (h,dataSem_set_var n x
                              s2)) | (NONE,s) -> (SOME (Rerr (Rabort
                              Rtype_error)),s) | res -> res))))))))`;;

(* HOL4 ML code, not ported:
val evaluate_ind = theorem"evaluate_ind";
*)

let evaluate_safe_def = cake_define
  `evaluate_safe c s = (let (x,s1) = dataSem_evaluate (c,s) in
  dataSem_state_safe_for_space s1)`;;

let evaluate_peak_def = cake_define
  `evaluate_peak c s = (let (x,s1) = dataSem_evaluate (c,s) in
  dataSem_state_peak_heap_length s1)`;;

(* We prove that the clock never increases. *)

(* Finally, we remove fix_clock from the induction and definition
   theorems. *)

(* observational semantics *)

let initial_state_def = cake_define
  `dataSem_initial_state ffi code coracle cc stamps lims ss k =
  mk_dataSem_state LN (SOME 0) [] (SOME 1) ss NONE 0 LN cc k code ffi
  0 (if stamps then SOME 0 else NONE) lims (if stamps then T else F)
  0 coracle`;;

let semantics_def = cake_define
  `dataSem_semantics init_ffi code coracle cc lims ss start =
   (let p = labLang_Call NONE (SOME start) [] NONE in
   let init = dataSem_initial_state init_ffi code coracle cc T lims
     ss in
     if ?k. match FST (dataSem_evaluate (p,init k)) with SOME (Rerr
       e) -> ~(e = Rabort Rtimeout_error) /\ (!f'. ~(e = Rabort
       (Rffi_error f'))) | NONE -> T | _179 -> F then
       pattern_semantics_Fail else
     match some (\res.
       ?k s r outcome.
         dataSem_evaluate (p,init k) = (SOME r,s) /\
         (match r with Rerr (Rabort (Rffi_error e)) -> outcome =
           ffi_FFI_outcome e | Rval _180 -> outcome = ffi_Success | _181
           -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events (?_ffi s)))
           with SOME res -> res | NONE ->
        ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (?_ffi (SND
              (dataSem_evaluate (p,init k)))))) UNIV)))`;;

let data_lang_safe_for_space_def = cake_define
  `data_lang_safe_for_space init_ffi code (lims:limits) (ss:num spt)
  start =
     (!ck.
       let p = labLang_Call NONE (SOME start) [] NONE in
       let init = dataSem_initial_state init_ffi code ARB ARB T lims
         ss in
       let (res,s) = dataSem_evaluate (p,((init
         ck):(one,'ffi)dataSem_state)) in dataSem_state_safe_for_space
         s)`;;

let compute_limits_def = cake_define
  `compute_limits len_bits a64 fpops fptops stack_heap_limit =
      mk_limits (SND stack_heap_limit) len_bits (FST
        stack_heap_limit) a64 fpops fptops`;;

(* clean up *)

(* HOL4 ML code, not ported:
val _ = map delete_binding ["evaluate_AUX_def",
  "evaluate_primitive_def"];
*)
