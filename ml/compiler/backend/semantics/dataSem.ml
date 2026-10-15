(* ======================================================== *)
(*  dataSem: ported from HOL4's
    compiler/backend/semantics/dataSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of dataLang
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/compiler.ml";;
needs "lib/comparison.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/multiword.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/semantics.ml";;
(* HOL4 ancestors outside the port: (* TODO: immoral, shouldn't
   depend on *) *)

let dataSem_v_INDUCT,dataSem_v_RECURSION = define_datatype
  "dataSem_v = dataSem_Number (int) | dataSem_Word64 (word64) | \
   dataSem_Block (num) (num) (dataSem_v list) | dataSem_CodePtr (num) \
   | dataSem_RefPtr (bool) (num)";;
hol4_overload "Number" "dataSem_Number";;
hol4_overload "Word64" "dataSem_Word64";;
hol4_overload "Block" "dataSem_Block";;
hol4_overload "CodePtr" "dataSem_CodePtr";;
hol4_overload "RefPtr" "dataSem_RefPtr";;

let boolv_def = cake_define
  `dataSem_Boolv b = Block 0 (bool_to_tag b) []`;;
hol4_overload "Boolv" "dataSem_Boolv";;

let unit_def = cake_define
  `dataSem_Unit = Block 0 (tuple_tag) []`;;
hol4_overload "Unit" "dataSem_Unit";;

(* Stack frame with:
   -  A stack frame size `ss` (NONE when unbounded)
   -  The local environment `env`
   -  Possibly a `handler`

  *)
let stack_INDUCT,stack_RECURSION = define_datatype
  "stack = dataSem_Env (num option) (dataSem_v spt) | dataSem_Exc \
   (num option) (dataSem_v spt) (num)";;
hol4_overload "Env" "dataSem_Env";;
hol4_overload "Exc" "dataSem_Exc";;

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

let size_of_def = cake_define_list
  [`size_of lims [] refs seen = (0,refs,seen)`;
   `size_of lims (x :: y :: ys) refs seen =
        (let (n1,refs1,seen1) = check_res refs (size_of lims (y ::
          ys) refs seen) in
        let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
          (n1 + n2,refs2,seen2))`;
   `size_of lims [(Word64 _1:dataSem_v)] refs seen = (3,refs,seen)`;
   `size_of lims [(Number i:dataSem_v)] refs seen =
        ((if small_num (limits_arch_64_bit lims) i then 0 else
          bignum_size (limits_arch_64_bit lims) i),refs,seen)`;
   `size_of lims [(CodePtr _2:dataSem_v)] refs seen = (0,refs,seen)`;
   `size_of lims [(RefPtr _3 r:dataSem_v)] refs seen =
         (match sptree_lookup r refs with NONE -> (0,refs,seen) |
           SOME (ByteArray _4 bs) -> (LENGTH bs DIV (arch_size lims DIV
           8) + 2,delete r refs,seen) | SOME (ValueArray vs) -> (let
           (n,refs,seen) = size_of lims vs (delete r refs) seen in
                              (n + LENGTH vs + 1,refs,seen)) | SOME
                                (Thunk _5 v) -> (let (n,refs,seen) =
                                size_of lims [v] (delete r refs) seen in
                              (n + 2,refs,seen)) | SOME (MutBlock tg
                                fin ls c rs) ->
             (let (n,refs,seen) = size_of lims (ls ++ [c] ++ rs)
               (delete r refs) seen in
               (n + LENGTH ls + LENGTH rs + 2,refs,seen)))`;
   `(size_of lims [Block ts tag []]) refs seen = (0,refs,seen)`;
   `size_of lims [(Block ts tag vs:dataSem_v)] refs seen =
         (if IS_SOME (sptree_lookup ts seen) then (0,refs,seen) else
           let (n,refs,seen) = size_of lims vs refs (insert ts one
             seen) in
             (n + LENGTH vs + 1,refs,seen))`];;

let extract_stack_def = cake_define
  `extract_stack (Env _6 env) = mlvector_toList env /\
   extract_stack (Exc _7 env _8) = mlvector_toList env`;;

let global_to_vs_def = cake_define
  `global_to_vs NONE = [] /\
   global_to_vs (SOME n) = [RefPtr T n]`;;

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
  `no_thunks_in_refs refs <=> (!k e v. ~(lookup k refs = SOME (Thunk
  e v)))`;;

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
  `allowed_op op _13 = (~(op = closLang_Install) /\ (!t i. ~(op =
  MemOp (MutCons t i))))`;;

let v_to_list_def = cake_define
  `dataSem_v_to_list x1 =
        match x1 with
          (Block ts tag []) ->
        (if tag = nil_tag then SOME [] else NONE)
        | (Block ts tag [h; bt]) ->
        (if tag = cons_tag then
          (match dataSem_v_to_list bt with SOME t -> SOME (h :: t) |
            _14 -> NONE) else NONE)
        | _15 -> NONE`;;
hol4_overload "v_to_list" "dataSem_v_to_list";;

(* HOL4 overload (expanded in the port):
     bignum_limit = \i1 i2 s.
      let il = bignum_size s.limits.arch_64_bit i1 in
      let jl = bignum_size s.limits.arch_64_bit i2 in
        2 * il + 2 * jl *)

(* Gives an upper bound to the memory consuption of an operation *)
let space_consumed_def = cake_define
  `(^ space_consumed (s (BlockOp (ConsExtend tag)) (Block _16 _17 xs' ::
  Number lower :: Number len :: Number tot :: xs)) =
    LENGTH (xs ++ TAKE (num_of_int len) (DROP (num_of_int lower)
      xs')) + 1) /\
   (space_consumed s (MemOp RefArray) [Number len; _18] = num_of_int
     len + 1) /\
   (space_consumed s (MemOp (RefByte _19)) [Number len; _20] =
     num_of_int len DIV (arch_size (dataSem_state_limits s) DIV 8) + 2)
     /\
   (space_consumed s (BlockOp (FromList n)) [Number len; lv] =
     num_of_int len + 1) /\
   (space_consumed s (IntOp Add) [Number i1; Number i2] =
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
   (space_consumed s (IntOp Sub) [Number i1; Number i2] =
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
   (space_consumed s (IntOp Mult) [Number i1; Number i2] =
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
   (space_consumed s (IntOp Div) [Number i1; Number i2] =
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
   (space_consumed s (IntOp Mod) [Number i1; Number i2] =
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
   (space_consumed s (BlockOp ListAppend) [lv1; lv2] =
    (match v_to_list lv1 with
     SOME l -> SUC (LENGTH l) * 3 | NONE -> 0)) /\
   (space_consumed s (op:closLang_op) (vs:dataSem_v list) =
     (0:num))`;;

let vb_size_def = cake_define
  `vb_size x1 =
        match x1 with
          (Block ts t ls) -> 1 + t + SUM (MAP vb_size ls) + LENGTH ls
        | _21 -> 1`;;

let vs_depth_def = cake_define
  `vs_depth x1 =
        match x1 with
          (Block ts t ls) -> vs_depth_list ls
        | _22 -> 0
        | [] -> 0
        | (x :: xs) -> MAX (1 + vs_depth x) (vs_depth_list xs)`;;

let eq_code_stack_max_def = cake_define
  `eq_code_stack_max n tsz =
   OPTION_MAP ((*) n)
     (OPTION_MAP2 MAX
       (sptree_lookup Equal_location tsz)
       (OPTION_MAP2 MAX
         (lookup Equal1_location tsz)
         (lookup Compare1_location tsz)))`;;

let stack_consumed_def = cake_define
  `stack_consumed sfs lims p vs =
        match (p,vs) with
          ((MemOp (CopyByte _23)),vs) ->
       OPTION_MAP2 MAX
        (sptree_lookup ByteCopy_location sfs)
        (OPTION_MAP2 MAX
           (lookup ByteCopyAdd_location sfs)
           (lookup ByteCopySub_location sfs))
        | ((MemOp (RefByte _24)),vs) ->
       OPTION_MAP2 MAX
        (lookup RefByte_location sfs)
        (lookup Replicate_location sfs)
        | ((MemOp (RefArray)),vs) ->
       OPTION_MAP2 MAX
        (lookup RefArray_location sfs)
        (lookup Replicate_location sfs)
        | ((MemOp XorByte),vs) ->
       lookup XorLoop_location sfs
        | ((MemOp (StringCmp b cmp)),vs) ->
       lookup StringCmpLoop_location sfs
        | ((BlockOp (ConsExtend _25)),vs) ->
       lookup MemCopy_location sfs
        | ((BlockOp (FromList _26)),vs) ->
       OPTION_MAP2 MAX
        (lookup FromList_location sfs)
        (lookup FromList1_location sfs)
        | ((BlockOp ListAppend),vs) ->
       OPTION_MAP2 MAX
        (lookup Append_location sfs)
        (OPTION_MAP2 MAX
          (lookup AppendLenLoop_location sfs)
          (lookup AppendMainLoop_location sfs))
        | ((IntOp Div),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\ 0 <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ 0 <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 / n2) then
         OPTION_MAP2 MAX
           (lookup LongDiv_location sfs)
           (lookup LongDiv1_location sfs) else
         OPTION_MAP2 MAX (lookup Div_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((IntOp Mod),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\ 0 <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ 0 <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 % n2) then
         OPTION_MAP2 MAX
           (lookup LongDiv_location sfs)
           (lookup LongDiv1_location sfs) else
         OPTION_MAP2 MAX (lookup Mod_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((IntOp Mult),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\ 0 <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ 0 <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 * n2) then SOME 0
            else
         OPTION_MAP2 MAX (lookup Mul_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((BlockOp Equal),[v1; v2]) ->
      (eq_code_stack_max (MIN (vs_depth v1 + 1) (vs_depth v2 + 1))
        sfs)
        | ((IntOp Sub),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\
          small_num (limits_arch_64_bit lims) n2 /\
          small_num (limits_arch_64_bit lims) (n1 - n2) then SOME 0
            else
         OPTION_MAP2 MAX (lookup Sub_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((IntOp Add),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\
          small_num (limits_arch_64_bit lims) n2 /\
          small_num (limits_arch_64_bit lims) (n1 + n2) then SOME 0
            else
         OPTION_MAP2 MAX (lookup Add_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((IntOp LessEq),vs) ->
       OPTION_MAP2 MAX
        (lookup Compare_location sfs)
        (lookup Compare1_location sfs)
        | ((IntOp Less),vs) ->
       OPTION_MAP2 MAX
        (lookup Compare_location sfs)
        (lookup Compare1_location sfs)
        | (p,vs) ->
        (if allowed_op p (LENGTH vs) then SOME 0 else NONE)`;;

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
     (do_space op vs) s =
       (if op_space_reset op then SOME
         (dataSem_state_peak_heap_length_fupd (K (do_space_peak op vs
         s)) (dataSem_state_safe_for_space_fupd (K (do_space_safe op
         vs s)) (dataSem_state_space_fupd (K 0) s))) else if
         op_space_req op (LENGTH vs) = 0 then SOME s else
         consume_space (op_space_req op (LENGTH vs)) s)`;;

let size_of_stack_frame_def = cake_define
  `size_of_stack_frame (Env n _27) = n /\ size_of_stack_frame (Exc n
  _28 _29) = OPTION_MAP ((+) 3) n`;;

let size_of_stack_def = cake_define
  `size_of_stack = FOLDR (OPTION_MAP2 (+) o size_of_stack_frame)
  (SOME 1)`;;

let do_stack_def = cake_define
  `^
     (do_stack op vs) s =
     (let new_stack = OPTION_MAP2 (+) (stack_consumed
       (dataSem_state_stack_frame_sizes s) (dataSem_state_limits s) op
       vs)
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
                     v_to_list lv = SOME (MAP (Number o (&) o w2n)
                       ns))`;;
hol4_overload "v_to_bytes" "dataSem_v_to_bytes";;

let v_to_words_def = cake_define
  `dataSem_v_to_words lv = some (\ns. v_to_list lv = SOME (MAP Word64
  ns))`;;
hol4_overload "v_to_words" "dataSem_v_to_words";;

(* TODO: move this stuff *)
let isClos_def = cake_define
  `dataSem_isClos t1 l1 = (((t1 = closure_tag) \/ (t1 =
  partial_app_tag)) /\ ~(l1 = []))`;;
hol4_overload "isClos" "dataSem_isClos";;

let do_eq_def = cake_define
  `dataSem_do_eq refs x2 x3 =
        match (x2,x3) with
          ((CodePtr _30),_31) -> Eq_type_error
        | (_32,(CodePtr _33)) -> Eq_type_error
        | ((Number n1),(Number n2)) -> (Eq_val (n1 = n2))
        | ((Number _34),_35) -> Eq_type_error
        | (_36,(Number _37)) -> Eq_type_error
        | ((Word64 w1),(Word64 w2)) -> (Eq_val (w1 = w2))
        | ((Word64 _38),_39) -> Eq_type_error
        | (_40,(Word64 _41)) -> Eq_type_error
        | ((RefPtr b1 n1),(RefPtr b2 n2)) ->
       (if b1 /\ b2 then
        (match (sptree_lookup n1 refs,sptree_lookup n2 refs) with
           (SOME (ByteArray T bs1),SOME (ByteArray T bs2)) -> Eq_val
             (bs1 = bs2) | (SOME (ByteArray T bs1),_42) -> Eq_type_error
             | (_43,SOME (ByteArray T bs2)) -> Eq_type_error | _44 ->
             Eq_val (n1 = n2)) else Eq_type_error)
        | ((RefPtr _45 _46),_47) -> Eq_type_error
        | (_48,(RefPtr _49 _50)) -> Eq_type_error
        | ((Block _51 t1 l1),(Block _52 t2 l2)) ->
      (if isClos t1 l1 \/ isClos t2 l2 then if isClos t1 l1 /\ isClos
        t2 l2 then Eq_val T else Eq_type_error else if (t1 = t2) /\
        (LENGTH l1 = LENGTH l2) then dataSem_do_eq_list refs l1 l2 else
        Eq_val F)
        | ([],[]) -> Eq_val T
        | ((v1 :: vs1),(v2 :: vs2)) ->
      (match dataSem_do_eq refs v1 v2 with Eq_val T ->
        dataSem_do_eq_list refs vs1 vs2 | Eq_val F -> Eq_val F | bad ->
        bad)
        | (_53,_54) -> Eq_val F`;;
hol4_overload "do_eq" "dataSem_do_eq";;
hol4_overload "do_eq_list" "dataSem_do_eq_list";;

(* HOL4 overload (expanded in the port):
     Error = (Rerr(Rabort Rtype_error)):(dataSem$v#('c,'ffi)
       dataSem$state, dataSem$v)result *)

let do_install_def = cake_define
  `^
     (do_install vs) s =
         (match vs with [v1; v2; vl1; vl2] ->
              (match (v_to_bytes v1,v_to_words v2) with (SOME
                bytes,SOME data) ->
                  (if ~(vl1 = Number (&LENGTH bytes)) \/ ~(
                     vl2 = Number (&LENGTH data)) then Rerr (Rabort
                       Rtype_error) else
                  let (cfg,progs) = ?_compile_oracle s 0 in
                  let new_oracle = shift_seq 1 (?_compile_oracle s)
                    in
                    (match (?_compile s cfg progs,progs) with (SOME
                      (bytes',data',cfg'),(k,prog) :: _55) ->
                         (if bytes = bytes' /\ data = data' /\ FST
                           (new_oracle 0) = cfg' then
                           let s' = ?_compile_oracle_fupd (K
                             new_oracle) (?_code_fupd (K (union (?_code
                             s) (fromAList progs)))
                             (dataSem_state_safe_for_space_fupd (K F)
                             s)) in
                             Rval (CodePtr k,s') else Rerr (Rabort
                               Rtype_error)) | _56 -> Rerr (Rabort
                               Rtype_error))) | _57 -> Rerr (Rabort
                               Rtype_error)) | _58 -> Rerr (Rabort
                               Rtype_error))`;;

let list_to_v_def = cake_define
  `dataSem_list_to_v ts t [] = t /\
   dataSem_list_to_v ts t (h :: l) = Block ts cons_tag [h;
     dataSem_list_to_v (ts + 1) t l]`;;
hol4_overload "list_to_v" "dataSem_list_to_v";;

(* HOL4 overload (expanded in the port):
     Block_nil = Block 0 nil_tag [] *)

let with_fresh_ts_def = cake_define
  `^
     with_fresh_ts (s n f) = (match dataSem_state_tstamps s with
                              SOME ts -> f ts
                                (dataSem_state_tstamps_fupd (K (SOME
                                (ts + n))) s) | NONE -> f 0 s)`;;

let lim_safe_part_def = cake_define
  `(lim_safe_part lims (Con tag xs) <=> (if xs = [] then tag < 2 EXP
  (arch_size lims) DIV 16 else
                              LENGTH xs < 2 EXP limits_length_limit
                                lims /\
                              LENGTH xs < 2 EXP (arch_size lims - 4)
                                /\
                              4 * tag < 2 EXP (arch_size lims) DIV 16
                                /\
                              4 * tag < 2 EXP (arch_size lims -
                                limits_length_limit lims - 2))) /\
   (lim_safe_part lims (Int i) <=>
      (if small_num (limits_arch_64_bit lims) i then T else
         let il = bignum_size (limits_arch_64_bit lims) i in
           il <= 2 EXP limits_length_limit lims)) /\
   (lim_safe_part lims (Str s) <=>
      (let i = strlen s in
         i DIV (arch_size lims DIV 8) < 2 EXP (arch_size lims) DIV
           arch_size lims /\
         i DIV (arch_size lims DIV 8) + 1 < 2 EXP limits_length_limit
           lims /\
         small_num (limits_arch_64_bit lims) (&i))) /\
   (lim_safe_part lims (W64 w) <=> 1 < limits_length_limit lims)`;;

let lim_safe_def = cake_define
  `lim_safe lims x2 xs =
        match (x2,xs) with
          ((BlockOp (Cons tag)),xs) ->
       (if xs = [] then tag < 2 EXP (arch_size lims) DIV 16 else
         LENGTH xs < 2 EXP limits_length_limit lims /\
         LENGTH xs < 2 EXP (arch_size lims - 4) /\
         4 * tag < 2 EXP (arch_size lims) DIV 16 /\
         4 * tag < 2 EXP (arch_size lims - limits_length_limit lims -
           2))
        | ((MemOp (MutCons tag i)),xs) ->
         (LENGTH xs < 2 EXP limits_length_limit lims /\
          LENGTH xs < 2 EXP (arch_size lims - 4) /\
          4 * tag < 2 EXP (arch_size lims) DIV 16 /\
          4 * tag < 2 EXP (arch_size lims - limits_length_limit lims
            - 2))
        | ((BlockOp (FromList tag)),xs) ->
      (match xs with [len; lv] ->
         (match v_to_list lv with SOME n ->
             (if len = Number (&(LENGTH n)) then small_num
               (limits_arch_64_bit lims) (&(LENGTH n)) /\
                  LENGTH n < 2 EXP limits_length_limit lims /\
                  LENGTH n < arch_size lims DIV 16 /\
                  4 * tag < 2 EXP (arch_size lims -
                    limits_length_limit lims - 2) /\
                  4 * tag < 2 EXP (arch_size lims) DIV 16 else T) |
                    _59 -> T) | _60 -> T)
        | ((BlockOp ListAppend),[x1; x2]) ->
      (match (v_to_list x1,v_to_list x2) with (SOME xs,SOME ys) ->
           1 < limits_length_limit lims /\
           3 * (SUC (LENGTH xs)) < 2 EXP (arch_size lims) DIV 8 | _61
             -> T)
        | ((BlockOp (ConsExtend tag)),(Block _62 _63 xs' :: Number
          lower :: Number len :: Number tot :: xs)) ->
           (if lower < 0 \/ len < 0 \/ lower + len > &LENGTH xs' \/
              tot = 0 \/ ~(tot = &LENGTH xs + len) then T else LENGTH
                (xs ++ TAKE (num_of_int len) (DROP (num_of_int lower)
                xs')) < 2 EXP limits_length_limit lims /\
                LENGTH (xs ++ TAKE (num_of_int len) (DROP (num_of_int
                  lower) xs')) < 2 EXP (arch_size lims) DIV 16 /\
                4 * tag < 2 EXP (arch_size lims) DIV 16 /\
                4 * tag < 2 EXP (arch_size lims - limits_length_limit
                  lims - 2))
        | ((IntOp Add),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 + i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((IntOp Sub),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 - i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((IntOp Mult),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ 0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ 0 <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 * i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((IntOp Div),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ 0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ 0 <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 / i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((IntOp Mod),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ 0 <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ 0 <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 % i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((MemOp RefArray),[Number i; v]) ->
      (0 <= i /\
       num_of_int i < 2 EXP (arch_size lims) DIV 16 /\
       num_of_int i < 2 EXP limits_length_limit lims)
        | ((MemOp (RefByte _64)),(Number i :: xs)) ->
      (0 <= i /\
       num_of_int i DIV (arch_size lims DIV 8) < 2 EXP (arch_size
         lims) DIV arch_size lims /\
       num_of_int i DIV (arch_size lims DIV 8) + 1 < 2 EXP
         limits_length_limit lims /\
       small_num (limits_arch_64_bit lims) i)
        | ((MemOp Ref),xs) ->
      (LENGTH xs < 2 EXP limits_length_limit lims /\
       LENGTH xs < 2 EXP arch_size lims DIV 16)
        | ((BlockOp (Build parts)),_65) ->
      EVERY (lim_safe_part lims) parts
        | ((WordOp WordToInt),_66) ->
      (1 < limits_length_limit lims)
        | ((WordOp WordFromInt),_67) ->
      (1 < limits_length_limit lims)
        | ((WordOp (WordOpw W64 _68)),_69) ->
      (1 < limits_length_limit lims)
        | ((WordOp (WordShift W64 _70 _71)),_72) ->
      (1 < limits_length_limit lims)
        | ((WordOp (WordFromWord _73)),_74) ->
      (1 < limits_length_limit lims)
        | ((WordOp (FP_cmp _75)),_76) -> ?_has_fp_ops
      lims
        | ((WordOp (FP_uop _77)),_78) ->
      (?_has_fp_ops lims /\ (limits_arch_64_bit lims \/ 1 <
        limits_length_limit lims))
        | ((WordOp (FP_bop _79)),_80) ->
      (?_has_fp_ops lims /\ (limits_arch_64_bit lims \/ 1 <
        limits_length_limit lims))
        | ((WordOp (FP_top _81)),_82) ->
      (?_has_fp_ops lims /\ limits_has_fp_tops lims /\
        (limits_arch_64_bit lims \/ 1 < limits_length_limit lims))
        | (_83,_84) -> T`;;

let do_lim_safe = cake_define
  `^
     do_lim_safe (s op vs) = dataSem_state_safe_for_space_fupd (K (
                              lim_safe (dataSem_state_limits s) op vs
                                /\ dataSem_state_safe_for_space s))
     s`;;

let check_lim_def = cake_define
  `^
     check_lim (s n) = dataSem_state_safe_for_space_fupd (K (n < 2
       EXP limits_length_limit (dataSem_state_limits s) /\
       dataSem_state_safe_for_space
                              s))
        s`;;

let do_part_def = cake_define_list
  [`dataSem_do_part m (Int i:const_part) s ts = (Number i,s,ts)`;
   `dataSem_do_part m (W64 w:const_part) s ts = (Word64 w,s,ts)`;
   `dataSem_do_part m (Con t ns:const_part) s ts =
      (if ns = [] then (Block 0 t [],s,ts) else match ts with
        NONE -> (Block 0 t (MAP m ns),s,ts) | SOME n -> (Block n t
        (MAP m ns),s,SOME (n + (1:num))))`;
   `dataSem_do_part m (Str t:const_part) s ts =
      (let ptr = (LEAST (\ptr. ~(ptr IN domain s))) in
      let bytes = MAP (n2w o ORD) (explode t) in
        (RefPtr T ptr,insert ptr (ByteArray T bytes) s,ts))`];;
hol4_overload "do_part" "dataSem_do_part";;

let do_build_def = cake_define
  `dataSem_do_build m i [] s ts = (m (i - 1),s,ts) /\
   dataSem_do_build m i (p :: rest) s ts =
     (let (x,s1,ts1) = do_part m p s ts in
       dataSem_do_build ((i =+ x) m) (i + 1) rest s1 ts1)`;;
hol4_overload "do_build" "dataSem_do_build";;

let do_build_const_def = cake_define
  `dataSem_do_build_const xs s ts = do_build (\x. Number (&0)) 0 xs s
  ts`;;
hol4_overload "do_build_const" "dataSem_do_build_const";;

let do_int_app_def = cake_define
  `dataSem_do_int_app x1 x2 =
      match (x1,x2) with
        ((Const n),[]) ->
     (if small_enough_int n then SOME (Number n) else NONE)
      | ((Add),[Number n1; Number n2]) -> SOME (Number (n1 + n2))
      | ((Sub),[Number n1; Number n2]) -> SOME (Number (n1 - n2))
      | ((Mult),[Number n1; Number n2]) -> SOME (Number (n1 * n2))
      | ((Div),[Number n1; Number n2]) ->
       (if n2 = 0 then NONE else SOME (Number (n1 / n2)))
      | ((Mod),[Number n1; Number n2]) ->
       (if n2 = 0 then NONE else SOME (Number (n1 % n2)))
      | ((Less),[Number n1; Number n2]) -> SOME (Boolv (n1 < n2))
      | ((LessEq),[Number n1; Number n2]) -> SOME (Boolv (n1 <= n2))
      | ((Greater),[Number n1; Number n2]) -> SOME (Boolv (n1 > n2))
      | ((GreaterEq),[Number n1; Number n2]) -> SOME (Boolv (n1 >=
        n2))
      | ((LessConstSmall n),[Number i]) ->
         (if 0 <= i /\ i <= 1000000 /\ n < 1000000 then
           SOME (Boolv (i < &n)) else NONE)
      | ((op:closLang_int_op),(vs:dataSem_v list)) -> NONE`;;
hol4_overload "do_int_app" "dataSem_do_int_app";;

let do_word_app_def = cake_define
  `dataSem_do_word_app x1 ws =
        match (x1,ws) with
          ((WordOpw W8 opw),[Number n1; Number n2]) ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw W64 opw),[Word64 w1; Word64 w2]) ->
           SOME (Word64 (opw_lookup opw w1 w2))
        | ((WordTest W8 test),[Number n1; Number n2]) ->
          (if 0 <= n1 /\ n1 < 256 /\ 0 <= n2 /\ n2 < 256 then
             (match test with Equal -> SOME (Boolv (n1 = n2)) |
               Compare Lt -> SOME (Boolv (n1 < n2)) | Compare Leq ->
               SOME (Boolv (n1 <= n2)) | _85 -> NONE) else NONE)
        | ((WordShift W8 sh n),[Number i]) ->
          (match some (\(w:word8). i = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (Number (&(w2n (shift_lookup sh w n)))))
        | ((WordShift W64 sh n),[Word64 w]) ->
          SOME (Word64 (shift_lookup sh w n))
        | ((WordFromInt),[Number i]) ->
          SOME (Word64 (i2w i))
        | (WordToInt,[Word64 w]) ->
          SOME (Number (&(w2n w)))
        | ((WordFromWord T),[Word64 w]) ->
          SOME (Number (&(w2n ((w2w:word64->word8) w))))
        | ((WordFromWord F),[Number n]) ->
          (match some (\(w:word8). n = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (Word64 (w2w w)))
        | ((FP_top t_op),ws) ->
           (match ws with [Word64 w1; Word64 w2; Word64 w3] ->
                (SOME (Word64 (fp_top_comp t_op w1 w2 w3))) | _86 ->
                  NONE)
        | ((FP_bop bop),ws) ->
           (match ws with [Word64 w1; Word64 w2] -> (SOME (Word64
             (fp_bop_comp bop w1 w2))) | _87 -> NONE)
        | ((FP_uop uop),ws) ->
           (match ws with [Word64 w] -> (SOME (Word64 (fp_uop_comp
             uop w))) | _88 -> NONE)
        | ((FP_cmp cmp),ws) ->
           (match ws with [Word64 w1; Word64 w2] -> (SOME (Boolv
             (fp_cmp_comp cmp w1 w2))) | _89 -> NONE)
        | ((op:closLang_word_op),(vs:dataSem_v list)) -> NONE`;;
hol4_overload "do_word_app" "dataSem_do_word_app";;

let dest_Boolv_def = cake_define
  `dest_Boolv x1 =
      match x1 with
        (Block _90 tag xs) ->
     (if xs = [] /\ tag < 2 then SOME (tag = 1) else NONE)
      | _91 -> NONE`;;

let dataSem_dest_thunk_ret_INDUCT,dataSem_dest_thunk_ret_RECURSION =
  define_datatype
  "dataSem_dest_thunk_ret = dataSem_BadRef | dataSem_NotThunk | \
   dataSem_IsThunk (thunk_mode) (dataSem_v)";;
hol4_overload "BadRef" "dataSem_BadRef";;
hol4_overload "NotThunk" "dataSem_NotThunk";;
hol4_overload "IsThunk" "dataSem_IsThunk";;

let dest_thunk_def = cake_define
  `dataSem_dest_thunk v refs =
      match v with
        (RefPtr b ptr) ->
     (match lookup ptr refs with NONE -> BadRef | SOME (Thunk
       Evaluated v) ->
          (if b then BadRef else IsThunk Evaluated v) | SOME (Thunk
            NotEvaluated v) ->
          (if b then BadRef else IsThunk NotEvaluated v) | SOME _92
            -> NotThunk)
      | v -> NotThunk`;;
hol4_overload "dest_thunk" "dataSem_dest_thunk";;

let bad_thunk_update_def = cake_define
  `dataSem_bad_thunk_update m v refs <=>
     m = Evaluated /\ ~(dest_thunk v refs = NotThunk)`;;
hol4_overload "bad_thunk_update" "dataSem_bad_thunk_update";;

(* mirrors bviSem$finalise_cons, but threads the timestamp counter so
   that
   each block produced by the finalisation gets a fresh time stamp *)
let _ = size_thms "sptree";;
(* HOL4 termination: \\ rw [] \\ imp_res_tac miscTheory.lookup_zero
   \\ fs [sptreeTheory.size_delete] *)
let finalise_cons_def = cake_define_wf
  `MEASURE (sptree_size o FST o SND)`
  `dataSem_finalise_cons v refs ts =
        match v with
          (RefPtr b ptr) ->
       (match lookup ptr refs with SOME (MutBlock tag finalised l c
         r) ->
           (if ~finalised then
             (match dataSem_finalise_cons c (delete ptr refs) ts with
               SOME (c',refs',ts') ->
                  SOME (Block (match ts' with NONE -> 0 | SOME n ->
                    n) tag (l ++ [c'] ++ r),
                        insert ptr (MutBlock tag T l c r) refs',
                        OPTION_MAP SUC ts') | NONE -> NONE) else
                          NONE) | SOME res -> SOME (RefPtr b
                          ptr,refs,ts) | NONE -> NONE)
        | v -> SOME (v,refs,ts)`;;
hol4_overload "finalise_cons" "dataSem_finalise_cons";;

let do_app_aux_def = cake_define
  `^ (^
     (do_app_aux op) vs) s =
       (match (op,vs) with (Label l,xs) ->
           (match xs with [] -> (if l IN domain (?_code s) then
                      Rval (CodePtr l,s) else ((Rerr (Rabort
                        Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                        #string+dataSem_v#string)) | _93 -> ((Rerr
                        (Rabort
                        Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                        #string+dataSem_v#string)) | (GlobOp
                        GlobalsPtr,xs) ->
           (match xs with [] -> (match dataSem_state_global s with
             SOME p -> Rval (RefPtr T p,s) | NONE -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | _94 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (GlobOp (Global n),xs) ->
           (match xs with [] -> (match dataSem_state_global s with
             SOME ptr ->
                         (match sptree_lookup ptr (?_refs s) with
                           SOME (ValueArray xs) ->
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
                                #string)) | (GlobOp (SetGlobal n),xs) ->
           (match xs with [x] -> (match dataSem_state_global s with
             SOME ptr ->
                          (match lookup ptr (?_refs s) with SOME
                            (ValueArray xs) ->
                              (if n < LENGTH xs then Rval
                                (Unit,?_refs_fupd (K (insert ptr
                              (ValueArray (LUPDATE x n xs)) (?_refs
                                s))) s) else ((Rerr (Rabort
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
                                #string)) | (GlobOp (SetGlobalsPtr),xs)
                                ->
           (match xs with [RefPtr T p] -> Rval
             (Unit,dataSem_state_global_fupd (K (SOME p)) s) | _99 ->
             ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (BlockOp (FromList n),xs) ->
           (match xs with [len; lv] ->
               (match v_to_list lv with SOME [] -> (if len = Number
                 (&0) then Rval (Block 0 n [],s) else ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | SOME vs -> (if len = Number
                 (&(LENGTH vs)) then with_fresh_ts s 1
                              (\ts s'. Rval (Block ts n vs,
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
                                #string)) | (MemOp (RefByte f),xs) ->
           (match xs with [Number i; Number b] ->
               (if 0 <= i /\ (?(w:word8). b = &(w2n w)) then
                 let ptr = (LEAST (\ptr. ~(ptr IN domain (?_refs
                   s)))) in
                   Rval (RefPtr T ptr,?_refs_fupd (K (insert ptr
                     (ByteArray f (REPLICATE (num_of_int i) (i2w b)))
                       (?_refs s))) s) else Rerr (Rabort Rtype_error)) |
                       _102 -> Rerr (Rabort Rtype_error)) | (GlobOp
                       AllocGlobal,_103) -> Rerr (Rabort Rtype_error) |
                       (MemOp FromListByte,_104) -> Rerr (Rabort
                       Rtype_error) | (MemOp ConcatByteVec,_105) -> Rerr
                       (Rabort Rtype_error) | (MemOp (CopyByte T),_106)
                       -> Rerr (Rabort Rtype_error) | (BlockOp (Build
                       parts),[]) ->
           (match do_build_const parts (?_refs s)
             (dataSem_state_tstamps s) with (v,s1,ts1) -> Rval
             (v,dataSem_state_tstamps_fupd (K ts1) (?_refs_fupd (K s1)
             s))) | (BlockOp (Cons tag),xs) -> (if xs = [] then Rval
             (Block 0 tag [],s) else with_fresh_ts s 1
                              (\ts s'. Rval (Block ts tag xs,
                              check_lim s' (LENGTH xs)))) | (BlockOp
                                (ConsExtend tag),Block x y xs' :: Number
                                lower :: Number len :: Number tot :: xs)
                                ->
           (if lower < 0 \/ len < 0 \/ lower + len > &LENGTH xs' \/
              tot = 0 \/ ~(tot = &LENGTH xs + len) then
             ((Rerr (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
               +dataSem_v#string) else with_fresh_ts s 1
                              (\ts s'.
                              let l = (xs ++ TAKE (num_of_int len)
                                (DROP (num_of_int lower) xs')) in Rval
                                (Block ts tag l,
                              check_lim s' (LENGTH l)))) | (BlockOp
                                (ConsExtend tag),_107) -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string) | (MemOp El,[Block _108 tag xs;
                                Number i]) ->
           (if 0 <= i /\ num_of_int i < LENGTH xs then Rval (EL
             (num_of_int i) xs,s) else ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (MemOp El,[RefPtr _109 ptr; Number
             i]) ->
           (match lookup ptr (?_refs s) with SOME (ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval (EL
                 (num_of_int i) xs,s) else ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | _110 -> ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | (BlockOp (ElemAt n),[Block _111
                 tag xs]) ->
           (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
             (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (BlockOp (ElemAt n),[RefPtr _112
             ptr]) ->
           (match lookup ptr (?_refs s) with SOME (ValueArray xs) ->
               (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
                 (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | _113 -> ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | (BlockOp (BoolTest test),[v1;
                 v2]) ->
           (match (dest_Boolv v1,dest_Boolv v2) with (SOME b1,SOME
             b2) -> Rval (Boolv (b1 = b2),s) | _114 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (BlockOp BoolNot,[v1]) ->
           (match dest_Boolv v1 with SOME b1 -> Rval (Boolv (~b1),s)
             | _115 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (BlockOp ListAppend,[x1; x2]) ->
           (match (v_to_list x1,v_to_list x2) with (SOME xs,SOME ys)
             -> ^
                with_fresh_ts (s (LENGTH xs)
                (\ts s'. Rval (list_to_v ts x2 xs,
                              check_lim (s') 2))) | _116 -> ((Rerr
                                (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | (BlockOp LengthBlock,[Block
                                _117 tag xs]) ->
           Rval (Number (&LENGTH xs),s) | (MemOp Length,[RefPtr _118
             ptr]) ->
           (match lookup ptr (?_refs s) with SOME (ValueArray xs) ->
                 Rval (Number (&LENGTH xs),s) | _119 -> ((Rerr
                   (Rabort
                   Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                   #string+dataSem_v#string)) | (MemOp
                   LengthByte,[RefPtr _120 ptr]) ->
           (match lookup ptr (?_refs s) with SOME (ByteArray _121 xs)
             ->
                 Rval (Number (&LENGTH xs),s) | _122 -> ((Rerr
                   (Rabort
                   Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                   #string+dataSem_v#string)) | (MemOp RefArray,[Number
                   i; v]) ->
           (if 0 <= i then
             let ptr = (LEAST (\ptr. ~(ptr IN domain (?_refs s)))) in
               Rval (RefPtr T ptr,?_refs_fupd (K (insert ptr
                              (ValueArray (REPLICATE (num_of_int i)
                                v)) (?_refs s)))
                     s) else ((Rerr (Rabort
                       Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                       #string+dataSem_v#string)) | (MemOp
                       DerefByte,[RefPtr _123 ptr; Number i]) ->
           (match lookup ptr (?_refs s) with SOME (ByteArray _124 ws)
             ->
               (if 0 <= i /\ i < &LENGTH ws then Rval (Number (&(w2n
                 (EL (num_of_int i) ws))),s) else ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | _125 -> ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                 +dataSem_v#string)) | (MemOp UpdateByte,[RefPtr _126
                 ptr; Number i; Number b]) ->
           (match lookup ptr (?_refs s) with SOME (ByteArray f bs) ->
               (if 0 <= i /\ i < &LENGTH bs /\ (?(w:word8). b = &(w2n
                 w)) then
                  Rval (Unit,?_refs_fupd (K (insert ptr
                    (ByteArray f (LUPDATE (i2w b) (num_of_int i) bs))
                      (?_refs s))) s) else ((Rerr (Rabort
                      Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                      #string+dataSem_v#string)) | _127 -> ((Rerr
                      (Rabort
                      Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                      #string+dataSem_v#string)) | (MemOp
                      XorByte,[RefPtr _128 dst; RefPtr _129 src]) ->
           (match (lookup src (?_refs s),lookup dst (?_refs s)) with
             (SOME (ByteArray _130 ws),SOME (ByteArray f ds)) ->
              (match xor_bytes ws ds with SOME ds1 -> Rval
                (Unit,?_refs_fupd (K (insert dst (ByteArray f ds1)
                (?_refs s))) s) | NONE -> ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | _131 -> ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | (MemOp (StringCmp b cmp),[RefPtr
                _132 s1; RefPtr _133 s2]) ->
           (match (lookup s1 (?_refs s),lookup s2 (?_refs s)) with
             (SOME (ByteArray _134 ws1),SOME (ByteArray _135 ws2)) ->
                (let s1 = implode (MAP (CHR o w2n) ws1) in
                 let s2 = implode (MAP (CHR o w2n) ws2) in
                   Rval (Boolv (str_cmp b cmp s1 s2),s)) | _136 ->
                     ((Rerr (Rabort
                     Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                     #string+dataSem_v#string)) | (MemOp (CopyByte
                     F),[RefPtr _137 src; Number srcoff; Number len;
                     RefPtr _138 dst; Number dstoff]) ->
           (match (lookup src (?_refs s),lookup dst (?_refs s)) with
             (SOME (ByteArray _139 ws),SOME (ByteArray fl ds)) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff))
                with SOME ds -> Rval (Unit,?_refs_fupd (K (insert dst
                (ByteArray fl ds) (?_refs s))) s) | NONE -> ((Rerr
                (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | _140 -> ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string)) | (BlockOp (TagEq n),[Block _141 tag
                xs]) ->
           Rval (Boolv (tag = n),s) | (BlockOp (LenEq l),[Block _142
             tag xs]) ->
           Rval (Boolv (LENGTH xs = l),s) | (BlockOp (TagLenEq n
             l),[Block _143 tag xs]) ->
           Rval (Boolv (tag = n /\ LENGTH xs = l),s) | (BlockOp
             (EqualConst p),[x1]) ->
           (match p with Int i -> (match x1 with Number j -> Rval
             (Boolv (i = j),s) | _144 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | W64 i -> (match x1 with Word64 j ->
             Rval (Boolv (i = j),s) | _145 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | Str i -> (match x1 with RefPtr _146 p
             ->
                          (match lookup p (?_refs s) with SOME
                            (ByteArray T j) ->
                             Rval (Boolv (j = MAP (n2w o ORD)
                               (explode i)),s) | _147 -> ((Rerr (Rabort
                               Rtype_error)):(dataSem_v#('c
                               ,'ffi)dataSem_state)#string+dataSem_v
                               #string)) | _148 -> ((Rerr (Rabort
                               Rtype_error)):(dataSem_v#('c
                               ,'ffi)dataSem_state)#string+dataSem_v
                               #string)) | _149 -> ((Rerr (Rabort
                               Rtype_error)):(dataSem_v#('c
                               ,'ffi)dataSem_state)#string+dataSem_v
                               #string)) | (BlockOp Equal,[x1; x2]) ->
           (match do_eq (?_refs s) x1 x2 with Eq_val b -> Rval (Boolv
             b,s) | _150 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (MemOp Ref,xs) ->
           (let ptr = (LEAST (\ptr. ~(ptr IN domain (?_refs s)))) in
             Rval (RefPtr T ptr,?_refs_fupd (K (insert ptr
               (ValueArray xs) (?_refs s))) s)) | (MemOp Update,[RefPtr
               _151 ptr; Number i; x]) ->
           (match lookup ptr (?_refs s) with SOME (ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval
                 (Unit,?_refs_fupd (K (insert ptr
                              (ValueArray (LUPDATE x (num_of_int i)
                                xs)) (?_refs s))) s) else ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | _152 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state)#string+dataSem_v
                                #string)) | (MemOp (MutCons tag i),xs)
                                ->
           (let ptr = (LEAST (\ptr. ~(ptr IN domain (?_refs s)))) in
              if i >= LENGTH xs then ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
                +dataSem_v#string) else
                let l = TAKE i xs in
                let c = EL i xs in
                let r = DROP (i + 1) xs in
                  Rval (RefPtr F ptr,?_refs_fupd (K (insert ptr
                    (MutBlock tag F l c r) (?_refs s)))
                        s)) | (MemOp UpdateCons,[RefPtr _153 ptr;
                          Number i; x]) ->
           (match lookup ptr (?_refs s) with SOME (MutBlock tag
             finalised l c r) ->
                (if ~(i = &LENGTH l) \/ finalised then ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string) else
                  Rval (Unit,?_refs_fupd (K (insert ptr (MutBlock tag
                    F l x r) (?_refs s))) s)) | _154 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (MemOp
                    FinaliseCons,[x]) ->
           (match finalise_cons x (?_refs s) (dataSem_state_tstamps
             s) with SOME (v,refs',ts') ->
                Rval (v,dataSem_state_tstamps_fupd (K ts')
                  (?_refs_fupd (K refs') s)) | NONE -> ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string)) | (IntOp intop,vs) ->
           (match do_int_app intop vs with SOME res -> Rval (res,s) |
             _155 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (WordOp wordop,vs) ->
           (match do_word_app wordop vs with SOME res -> Rval (res,s)
             | _156 -> ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
             +dataSem_v#string)) | (FFI n,[RefPtr _157 cptr; RefPtr _158
             ptr]) ->
           (match (lookup cptr (?_refs s),lookup ptr (?_refs s)) with
             (SOME (ByteArray T cws),SOME (ByteArray F ws)) ->
              (match call_FFI (?_ffi s) (ExtCall n) cws ws with
                FFI_return ffi' ws' ->
                   Rval (Unit,?_ffi_fupd (K ffi') (?_refs_fupd (K
                     (insert ptr (ByteArray F ws') (?_refs s)))
                         s)) | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome))) | _159 ->
                     ((Rerr (Rabort
                     Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                     #string+dataSem_v#string)) | (BlockOp
                     BoundsCheckBlock,xs) ->
           (match xs with [Block _160 tag ys; Number i] ->
                  Rval (Boolv (0 <= i /\ i < &LENGTH ys),s) | _161 ->
                    ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (MemOp (BoundsCheckByte
                    loose),xs) ->
           (match xs with [RefPtr _162 ptr; Number i] ->
             (match lookup ptr (?_refs s) with SOME (ByteArray _163
               ws) ->
                  Rval (Boolv (0 <= i /\ (if loose then (<=) else
                    (<)) i (&LENGTH ws)),s) | _164 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | _165 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (MemOp
                    BoundsCheckArray,xs) ->
           (match xs with [RefPtr _166 ptr; Number i] ->
             (match lookup ptr (?_refs s) with SOME (ValueArray ws)
               ->
                  Rval (Boolv (0 <= i /\ i < &LENGTH ws),s) | _167 ->
                    ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | _168 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                    #string+dataSem_v#string)) | (MemOp ConfigGC,[Number
                    _169; Number _170]) -> (Rval (Unit,s)) | (ThunkOp
                    th_op,vs) ->
           (match (th_op,vs) with (AllocThunk m,[v]) ->
                (if bad_thunk_update m v (?_refs s) then ((Rerr
                  (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string) else
                 let ptr = (LEAST (\ptr. ~(ptr IN domain (?_refs
                   s)))) in
                   Rval (RefPtr F ptr,?_refs_fupd (K (insert ptr
                     (Thunk m v) (?_refs s)))
                         s)) | (UpdateThunk m,[RefPtr F ptr; v]) ->
                (if bad_thunk_update m v (?_refs s) then ((Rerr
                  (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)
                  #string+dataSem_v#string) else
                 match lookup ptr (?_refs s) with SOME (Thunk
                   NotEvaluated _171) ->
                    Rval (Unit,?_refs_fupd (K (insert ptr (Thunk m
                      v) (?_refs s))) s) | _172 -> ((Rerr (Rabort
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
     (do_app op vs) s =
       (if op = Install then do_install vs
         (dataSem_state_stack_frame_sizes_fupd (K LN)
         (dataSem_state_stack_max_fupd (K NONE) s)) else
       if MEM op [IntOp Greater; IntOp GreaterEq] then ((Rerr (Rabort
         Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
         +dataSem_v#string) else
       match do_space op vs s with NONE -> ((Rerr (Rabort
         Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state)#string
         +dataSem_v#string) | SOME s1 -> do_app_aux op vs (do_stack
         op vs (do_lim_safe s1 op vs)))`;;

let get_var_def = cake_define
  `dataSem_get_var v = sptree_lookup v`;;
hol4_overload "get_var" "dataSem_get_var";;

let get_vars_def = cake_define
  `(dataSem_get_vars [] s = SOME []) /\
   (dataSem_get_vars (v :: vs) s =
      (match get_var v s with NONE -> NONE | SOME x -> (match
        dataSem_get_vars vs s with NONE -> NONE | SOME xs -> SOME (x
        :: xs))))`;;
hol4_overload "get_vars" "dataSem_get_vars";;

let set_var_def = cake_define
  `dataSem_set_var v x s = (dataSem_state_locals_fupd (K (insert v x
  (dataSem_state_locals s))) s)`;;
hol4_overload "set_var" "dataSem_set_var";;

let dec_clock_def = cake_define
  `dataSem_dec_clock s = ?_clock_fupd (K (?_clock s - 1)) s`;;
hol4_overload "dec_clock" "dataSem_dec_clock";;

let fix_clock_def = cake_define
  `dataSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;
hol4_overload "fix_clock" "dataSem_fix_clock";;

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
     (call_env args size) s =
       (let new_stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max
         s)
                              (OPTION_MAP2 (+) (size_of_stack
                                (?_stack s)) size) in let
           stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit
             (dataSem_state_limits s))) new_stack_max) in
             dataSem_state_safe_for_space_fupd (K
             (dataSem_state_safe_for_space s /\ stack_safe))
             (dataSem_state_stack_max_fupd (K new_stack_max)
             (dataSem_state_locals_size_fupd (K size)
             (dataSem_state_locals_fupd (K (fromList args))
         s))))`;;

let push_env_def = cake_define
  `^ (push_env env F) s  =
        match  with
           ->
       (let stack = Env (dataSem_state_locals_size s) env :: ?_stack
         s in let
           stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max s)
             (size_of_stack stack) in let
           stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit
             (dataSem_state_limits s))) stack_max) in
             dataSem_state_safe_for_space_fupd (K
             (dataSem_state_safe_for_space s /\ stack_safe))
             (dataSem_state_stack_max_fupd (K stack_max) (?_stack_fupd
             (K stack) s)))
        |  ->
      (let stack = Exc (dataSem_state_locals_size s) env
        (dataSem_state_handler s) :: ?_stack s in let
          stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max s)
            (size_of_stack stack) in let
          stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit
            (dataSem_state_limits s))) stack_max) in
            dataSem_state_safe_for_space_fupd (K
            (dataSem_state_safe_for_space s /\ stack_safe))
            (dataSem_state_handler_fupd (K (LENGTH (?_stack s)))
            (dataSem_state_stack_max_fupd (K stack_max) (?_stack_fupd
            (K stack) s))))`;;

let pop_env_def = cake_define
  `^
     pop_env s =
       (match ?_stack s with (Env ss e :: xs) ->
           SOME (dataSem_state_locals_size_fupd (K ss) (?_stack_fupd
             (K xs) (dataSem_state_locals_fupd (K e) s))) | (Exc ss e n
             :: xs) ->
           SOME (dataSem_state_handler_fupd (K n)
             (dataSem_state_locals_size_fupd (K ss) (?_stack_fupd (K
             xs) (dataSem_state_locals_fupd (K e) s)))) | _175 ->
             NONE)`;;

let jump_exc_def = cake_define
  `^
     jump_exc s =
       (if dataSem_state_handler s < LENGTH (?_stack s) then
         match LASTN (dataSem_state_handler s + 1) (?_stack s) with
           Exc ss e n :: xs ->
             SOME (dataSem_state_locals_size_fupd (K ss)
               (?_stack_fupd (K xs) (dataSem_state_locals_fupd (K e)
               (dataSem_state_handler_fupd (K n) s)))) | _176 -> NONE
               else NONE)`;;

let cut_env_def = cake_define
  `dataSem_cut_env (name_set:1 spt) env =
     (if domain name_set SUBSET domain env then SOME (mk_wf (inter
       env name_set)) else NONE)`;;
hol4_overload "cut_env" "dataSem_cut_env";;

let cut_state_def = cake_define
  `^
     (cut_state names) s =
       (match cut_env names (dataSem_state_locals s) with NONE ->
         NONE | SOME env -> SOME (dataSem_state_locals_fupd (K env)
         s))`;;

let cut_state_opt_def = cake_define
  `cut_state_opt names s =
     (match names with NONE -> SOME s | SOME names -> cut_state
       names s)`;;

let find_code_def = cake_define
  `(dataSem_find_code (SOME p) args code ssize =
      (match sptree_lookup p code with NONE -> NONE | SOME
        (arity,exp) ->
         (if LENGTH args = arity then SOME (args,exp,lookup p ssize)
           else NONE))) /\ (dataSem_find_code NONE args code ssize =
      (if args = [] then NONE else
        match LAST args with CodePtr loc ->
            (match sptree_lookup loc code with NONE -> NONE | SOME
              (arity,exp) ->
                (if LENGTH args = arity + 1 then SOME (FRONT
                  args,exp,lookup loc ssize) else NONE)) | other ->
                  NONE))`;;
hol4_overload "find_code" "dataSem_find_code";;

let isBool_def = cake_define
  `isBool b x2 =
      match x2 with
        (Block _177 tag []) -> (bool_to_tag b = tag)
      | _178 -> F`;;

let install_sfs_def = cake_define
  `^
     (install_sfs op) s = dataSem_state_safe_for_space_fupd (K
       (~(op = closLang_Install) /\ dataSem_state_safe_for_space s))
       s`;;

let set_vars_def = cake_define
  `set_vars ns vs s = (dataSem_state_locals_fupd (K (union (fromAList
  (ZIP (ns,vs))) (dataSem_state_locals s))) s)`;;

let evaluate_def = cake_define_list
  [`dataSem_evaluate (Skip,s) = (NONE,s)`;
   `dataSem_evaluate (Move dest src,s) =
         (match get_var src (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME v ->
           (NONE,set_var dest v s))`;
   `dataSem_evaluate (Assign dest op args names_opt,s) =
         (if op_requires_names op = IS_NONE names_opt then
           (SOME (Rerr (Rabort Rtype_error)),s) else
           match get_vars args (dataSem_state_locals s) with NONE ->
             (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs ->
               (match cut_state_opt names_opt s with NONE -> (SOME
                 (Rerr (Rabort Rtype_error)),s) | SOME s ->
                   (match do_app op xs s with Rerr e -> (SOME (Rerr
                     e),flush_state T (install_sfs op s)) | Rval (v,s)
                     ->
                       (NONE,set_var dest v (install_sfs op
                         s)))))`;
   `dataSem_evaluate (Tick,s) =
         (if ?_clock s = 0 then (SOME (Rerr (Rabort
           Rtimeout_error)),flush_state T s) else (NONE,dec_clock s))`;
   `dataSem_evaluate (MakeSpace k names,s) =
         (match cut_env names (dataSem_state_locals s) with NONE
           -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME env ->
           (NONE,add_space (dataSem_state_locals_fupd (K env) s) k))`;
   `dataSem_evaluate (Raise n,s) =
         (match get_var n (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME x ->
           (match jump_exc s with NONE -> (SOME (Rerr (Rabort
             Rtype_error)),s) | SOME s -> (SOME (Rerr (Rraise
             x)),s)))`;
   `dataSem_evaluate (Return ns,s) =
         (match get_vars ns (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs -> (SOME
           (Rval xs),flush_state F s))`;
   `dataSem_evaluate (Seq c1 c2,s) =
         (let (res,s1) = fix_clock s (dataSem_evaluate (c1,s)) in
           if res = NONE then dataSem_evaluate (c2,s1) else
             (res,s1))`;
   `dataSem_evaluate (If n c1 c2,s) =
         (match get_var n (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME x -> (if isBool T
           x then dataSem_evaluate (c1,s) else
                     if isBool F x then dataSem_evaluate (c2,s) else
                       (SOME (Rerr (Rabort Rtype_error)),s)))`;
   `dataSem_evaluate (Force ret loc src,s) =
         (match get_var src (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME thunk_v ->
           (match dest_thunk thunk_v (?_refs s) with BadRef -> (SOME
             (Rerr (Rabort Rtype_error)),s) | NotThunk -> (SOME (Rerr
             (Rabort Rtype_error)),s) | IsThunk Evaluated v ->
              (match ret with NONE -> (SOME (Rval [v]),flush_state F
                s) | SOME (dest,names) ->
                 (match cut_env names (dataSem_state_locals s) with
                   NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME
                   env -> (NONE,set_var dest v
                   (dataSem_state_locals_fupd (K env) s)))) | IsThunk
                   NotEvaluated f ->
               (match find_code (SOME loc) [thunk_v; f] (?_code s)
                 (dataSem_state_stack_frame_sizes s) with NONE -> (SOME
                 (Rerr (Rabort Rtype_error)),s) | SOME (args1,prog,ss)
                 ->
                  (match ret with NONE ->
                      (if ?_clock s = 0 then
                         (SOME (Rerr (Rabort
                           Rtimeout_error)),dataSem_state_locals_fupd (K
                           LN) (?_stack_fupd (K [])
                              s)) else
                         (match dataSem_evaluate (prog,call_env
                           args1 ss (dec_clock s)) with (NONE,s) ->
                           (SOME (Rerr (Rabort Rtype_error)),s) | (SOME
                           res,s) -> (SOME res,s))) | SOME (dest,names)
                           ->
                     (match cut_env names (dataSem_state_locals s)
                       with NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                       | SOME env ->
                          (let s1 = call_env args1 ss (push_env env
                            F (dec_clock s)) in
                            if ?_clock s = 0 then
                              (SOME (Rerr (Rabort
                                Rtimeout_error))
                                ,dataSem_state_locals_fupd (K LN)
                                (?_stack_fupd (K [])
                              s1)) else
                              (match fix_clock s1 (dataSem_evaluate
                                (prog,s1)) with (SOME (Rval xs),s2) ->
                              (if LENGTH xs = 1 then
                              match pop_env s2 with NONE -> (SOME
                                (Rerr (Rabort Rtype_error)),s2) | SOME
                                s1 -> (NONE,set_var dest (HD xs) s1)
                                else
                              (SOME (Rerr (Rabort
                                Rtype_error)),s2)) | (NONE,s) ->
                                (SOME (Rerr (Rabort Rtype_error)),s)
                                | res -> res)))))))`;
   `dataSem_evaluate (Call ret dest args handler,s) =
         (match get_vars args (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs ->
           (match find_code dest xs (?_code s)
             (dataSem_state_stack_frame_sizes s) with NONE -> (SOME
             (Rerr (Rabort Rtype_error)),s) | SOME (args1,prog,ss) ->
              (match ret with NONE ->
                 (if handler = NONE then
                   if ?_clock s = 0 then (SOME (Rerr (Rabort
                     Rtimeout_error)),
                         flush_state T s) else
                     (match dataSem_evaluate (prog,call_env args1 ss
                       (dec_clock s)) with (NONE,s) -> (SOME (Rerr
                       (Rabort Rtype_error)),s) | (SOME res,s) -> (SOME
                       res,s)) else (SOME (Rerr (Rabort
                       Rtype_error)),s)) | SOME (ns,names) ->
                 (if ~ALL_DISTINCT ns then (SOME (Rerr (Rabort
                   Rtype_error)),s) else
                 (match cut_env names (dataSem_state_locals s) with
                   NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME
                   env ->
                    (let s1 = call_env args1 ss
                            (push_env env (IS_SOME handler)
                              (dec_clock s)) in if ?_clock s = 0 then
                              (SOME (Rerr (Rabort
                              Rtimeout_error)),dataSem_state_locals_fupd
                              (K LN) (?_stack_fupd (K [])
                            s1)) else (match fix_clock s1
                              (dataSem_evaluate (prog,s1)) with (SOME
                              (Rval xs),s2) ->
                              (if LENGTH xs = LENGTH ns then
                              (match pop_env s2 with NONE -> (SOME
                                (Rerr (Rabort Rtype_error)),s2) | SOME
                                s1 -> (NONE,set_vars ns xs s1)) else
                              (SOME (Rerr (Rabort Rtype_error)),s2))
                                | (SOME (Rerr (Rraise x)),s2) ->
                              (match handler with NONE -> (SOME
                                (Rerr (Rraise x)),s2) | SOME (n,h) ->
                                dataSem_evaluate (h,set_var n x s2))
                                | (NONE,s) -> (SOME (Rerr (Rabort
                                Rtype_error)),s) | res -> res)))))))`];;
hol4_overload "evaluate" "dataSem_evaluate";;

(* HOL4 ML code, not ported:
val evaluate_ind = theorem"evaluate_ind";
*)

let evaluate_safe_def = cake_define
  `evaluate_safe c s = (let (x,s1) = evaluate (c,s) in
  dataSem_state_safe_for_space s1)`;;

let evaluate_peak_def = cake_define
  `evaluate_peak c s = (let (x,s1) = evaluate (c,s) in
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
hol4_overload "initial_state" "dataSem_initial_state";;

let semantics_def = cake_define
  `dataSem_semantics init_ffi code coracle cc lims ss start =
   (let p = Call NONE (SOME start) [] NONE in
   let init = initial_state init_ffi code coracle cc T lims ss in
     if ?k. match FST (evaluate (p,init k)) with SOME (Rerr e) -> ~(e
       = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f))) |
       NONE -> T | _179 -> F then Fail else
     match some (\res.
       ?k s r outcome.
         evaluate (p,init k) = (SOME r,s) /\
         (match r with Rerr (Rabort (Rffi_error e)) -> outcome =
           FFI_outcome e | Rval _180 -> outcome = Success | _181 -> F)
           /\
         res = Terminate outcome (ffi_state_io_events (?_ffi s)))
           with SOME res -> res | NONE ->
        Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (?_ffi (SND
              (evaluate (p,init k)))))) UNIV)))`;;
hol4_overload "semantics" "dataSem_semantics";;

let data_lang_safe_for_space_def = cake_define
  `data_lang_safe_for_space init_ffi code (lims:limits) (ss:num spt)
  start =
     (!ck.
       let p = Call NONE (SOME start) [] NONE in
       let init = initial_state init_ffi code ARB ARB T lims ss in
       let (res,s) = dataSem_evaluate (p,((init
         ck):(1,'ffi)dataSem_state)) in dataSem_state_safe_for_space
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
