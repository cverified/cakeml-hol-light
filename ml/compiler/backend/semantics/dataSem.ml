(* ======================================================== *)
(*  dataSem: ported from HOL4's
    compiler/backend/semantics/dataSemScript.sml
    A definition theory, with 73 definitions, 5 datatypes and 16
    theorems.  Needed by 12 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of dataLang
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/data_live.ml";;
needs "compiler/backend/data_simp.ml";;
needs "compiler/backend/data_space.ml";;
needs "compiler/backend/data_to_word.ml";;
(* TODO: immoral, semantics shouldn't depend on compiler *)
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/word_depth.ml";;
needs "lib/comparison.ml";;
needs "lib/errorMonad.ml";;
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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "dataSem"
  ["backendProps"; "bvlSem"; "dataLang"; "data_live"; "data_simp";
   "data_space"; "data_to_word"];;

let dataSem_v_INDUCT,dataSem_v_RECURSION = define_datatype
  "dataSem_v = dataSem_Number (int) \
   // integer\n\
   | dataSem_Word64 (word64) \
   // 64-bit word\n\
   | dataSem_Block (num) (num) (dataSem_v list) \
   // cons block: timestamp, tag and payload\n\
   | dataSem_CodePtr (num) \
   // code pointer\n\
   | dataSem_RefPtr (bool) (num) \
   // pointer to ref cell";;
hol4_overload "Number" "dataSem_Number";;
hol4_overload "Word64" "dataSem_Word64";;
hol4_overload "Block" "dataSem_Block";;
hol4_overload "CodePtr" "dataSem_CodePtr";;
hol4_overload "RefPtr" "dataSem_RefPtr";;

let dataSem_Boolv_def = cake_define
  `dataSem_Boolv b = Block 0 (bool_to_tag b) []`;;
hol4_overload "Boolv" "dataSem_Boolv";;

let dataSem_Unit_def = cake_define
  `dataSem_Unit = Block 0 (tuple_tag) []`;;
hol4_overload "Unit" "dataSem_Unit";;

(* Stack frame with:
   -  A stack frame size `ss` (NONE when unbounded)
   -  The local environment `env`
   -  Possibly a `handler`

  *)
let dataSem_stack_INDUCT,dataSem_stack_RECURSION = define_datatype
  "dataSem_stack = \
   // Env  ss           env\n\
   dataSem_Env (num option) (dataSem_v spt) | \
   // Exc  ss           env        handler\n\
   dataSem_Exc (num option) (dataSem_v spt) (num)";;
hol4_overload "Env" "dataSem_Env";;
hol4_overload "Exc" "dataSem_Exc";;

let limits_FIELDS = define_record "limits"
  ["heap_limit","num";
   (* number of words in the heap *)
   "length_limit","num";
   (* length field in a Block *)
   "stack_limit","num";
   (* max stack size *)
   "arch_64_bit","bool";
   (* the arch is either 64-bit or 32-bit *)
   "has_fp_ops","bool";
   (* the arch supports float ops *)
   "has_fp_tops","bool"
   (* the arch supports float ops *)
  ];;
hol4_field_overload "stack_limit" "limits_stack_limit";;
hol4_field_overload "stack_limit_fupd" "limits_stack_limit_fupd";;
hol4_field_overload "has_fp_ops" "limits_has_fp_ops";;
hol4_field_overload "has_fp_ops_fupd" "limits_has_fp_ops_fupd";;

let dataSem_state_FIELDS = define_record "dataSem_state"
  ["locals","dataSem_v spt";
   "locals_size","num option";
   (* size of locals when pushed to stack, NONE if unbounded *)
   "stack","dataSem_stack list";
   "stack_max","num option";
   (* largest stack seen so far, NONE if unbounded *)
   "stack_frame_sizes","num spt";
   (* stack frame sizes, unbounded if unmapped *)
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
hol4_overload "state_locals" "dataSem_state_locals";;
hol4_overload "state_locals_fupd" "dataSem_state_locals_fupd";;
hol4_overload "state_locals_size" "dataSem_state_locals_size";;
hol4_overload "state_locals_size_fupd"
  "dataSem_state_locals_size_fupd";;
hol4_field_overload "stack" "dataSem_state_stack";;
hol4_field_overload "stack_fupd" "dataSem_state_stack_fupd";;
hol4_overload "state_stack_max" "dataSem_state_stack_max";;
hol4_overload "state_stack_max_fupd" "dataSem_state_stack_max_fupd";;
hol4_overload "state_global" "dataSem_state_global";;
hol4_overload "state_global_fupd" "dataSem_state_global_fupd";;
hol4_overload "state_handler" "dataSem_state_handler";;
hol4_overload "state_handler_fupd" "dataSem_state_handler_fupd";;
hol4_overload "state_refs" "dataSem_state_refs";;
hol4_overload "state_refs_fupd" "dataSem_state_refs_fupd";;
hol4_field_overload "compile" "dataSem_state_compile";;
hol4_field_overload "compile_fupd" "dataSem_state_compile_fupd";;
hol4_overload "state_clock" "dataSem_state_clock";;
hol4_overload "state_clock_fupd" "dataSem_state_clock_fupd";;
hol4_overload "state_code" "dataSem_state_code";;
hol4_overload "state_code_fupd" "dataSem_state_code_fupd";;
hol4_overload "state_ffi" "dataSem_state_ffi";;
hol4_overload "state_ffi_fupd" "dataSem_state_ffi_fupd";;
hol4_field_overload "compile_oracle" "dataSem_state_compile_oracle";;
hol4_field_overload "compile_oracle_fupd"
  "dataSem_state_compile_oracle_fupd";;

(* HOL4 dataSemScript.sml:76-77: the ML values that the definitions
   below antiquote *)

let arch_size_def = cake_define
  `arch_size lims = (if limits_arch_64_bit lims then 64 else 32:num)`;;

let check_res_def = cake_define
  `check_res r (n,refs,seen) =
     (if sptree_size refs <= sptree_size r then (n,refs,seen) else
       (n,r,seen))`;;

let check_res_IMP = prove
 (`!y. (n,r,s) = check_res t y ==> size r <= size t`,
  CHEAT_TAC);;

let small_num_def = cake_define
  `small_num arch64 (i:int) =
     (if arch64 then --(&(2 EXP 61)) <= i /\ i < (&(2 EXP 61))
       else --(&(2 EXP 29)) <= i /\ i < (&(2 EXP 29)))`;;

let bignum_digits_def = cake_define
  `bignum_digits arch64 n =
     (if n = 0 then 0 else
       let d = (if arch64 then 64 else 32) in
         1 + bignum_digits arch64 (n DIV 2 EXP d))`;;

let bignum_size_def = cake_define
  `bignum_size arch64 i =
     1 + bignum_digits arch64 (num_of_int (abs i))`;;

let _ = size_thms "dataSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 dataSemScript.sml:138-145: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let size_of_def = cake_define_list_try_tac (fun () ->
  `(inv_image (MEASURE I LEX MEASURE (list_size dataSem_v_size))
                              (\(lims,vs,refs,seen). (sptree_size
                              refs,vs)))`)
  CHEAT_TAC
  [`size_of lims [] refs seen = (0,refs,seen)`;
   `size_of lims (x :: y :: ys) refs seen =
        (let (n1,refs1,seen1) = check_res refs (size_of lims (y ::
          ys) refs seen) in
        let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
          (n1 + n2,refs2,seen2))`;
   `size_of lims [(Word64 _2:dataSem_v)] refs seen = (3,refs,seen)`;
   `size_of lims [(Number i:dataSem_v)] refs seen =
        ((if small_num (limits_arch_64_bit lims) i then 0 else
          bignum_size (limits_arch_64_bit lims) i),refs,seen)`;
   `size_of lims [(CodePtr _4:dataSem_v)] refs seen = (0,refs,seen)`;
   `size_of lims [(RefPtr _18 r:dataSem_v)] refs seen =
         (match sptree_lookup r refs with NONE -> (0,refs,seen) |
           SOME (ByteArray _19 bs) -> (LENGTH bs DIV (arch_size lims DIV
           8) + 2,delete r refs,seen) | SOME (ValueArray vs) -> (let
           (n,refs,seen) = size_of lims vs (delete r refs) seen in
                              (n + LENGTH vs + 1,refs,seen)) | SOME
                                (Thunk _20 v) -> (let (n,refs,seen) =
                                size_of lims [v] (delete r refs) seen in
                              (n + 2,refs,seen)) | SOME
                                (bvlSem_MutBlock tg fin ls c rs) ->
             (let (n,refs,seen) = size_of lims (ls ++ [c] ++ rs)
               (delete r refs) seen in
               (n + LENGTH ls + LENGTH rs + 2,refs,seen)))`;
   `(size_of lims [Block ts tag []]) refs seen = (0,refs,seen)`;
   `size_of lims [(Block ts tag vs:dataSem_v)] refs seen =
         (if IS_SOME (sptree_lookup ts seen) then (0,refs,seen) else
           let (n,refs,seen) = size_of lims vs refs (insert ts one
             seen) in
             (n + LENGTH vs + 1,refs,seen))`];;

(* [local] *)
let check_res_size_of = prove
 (`check_res refs (size_of lims vs refs seen) = size_of lims vs refs
  seen`,
  CHEAT_TAC);;

(* HOL4 dataSemScript.sml:159: a theorem that HOL4 states as the
   value of an ML expression: size_of_def *)
(* HOL4 dataSemScript.sml:160: a theorem that HOL4 states as the
   value of an ML expression: size_of_ind *)

let extract_stack_def = cake_define_list
  [`extract_stack (Env _22 env:dataSem_stack) = sptree_toList env`;
   `extract_stack (dataSem_Exc _23 env _24) = sptree_toList env`];;

let global_to_vs_def = cake_define_list
  [`global_to_vs NONE = []`;
   `global_to_vs (SOME n) = [RefPtr T n]`];;

let stack_to_vs_def = cake_define
  `stack_to_vs (s:('c,'ffi)dataSem_state) =
     sptree_toList (dataSem_state_locals s) ++ FLAT (MAP
       extract_stack (dataSem_state_stack s)) ++ global_to_vs
       (dataSem_state_global s)`;;

(* Measures the amount of space everything in a dataLang "heap" would need
   to fit in wordLang memory (over-approximation) *)
let size_of_heap_def = cake_define
  `size_of_heap (s:('c,'ffi)dataSem_state) =
     (let (n,_25,_26) = size_of (dataSem_state_limits s) (stack_to_vs
       ((s:('c,'ffi)dataSem_state))) (dataSem_state_refs
       ((s:('c,'ffi)dataSem_state))) LN in
       n)`;;

let no_thunks_in_refs_def = cake_define
  `no_thunks_in_refs refs <=> (!k e v. ~(lookup k refs = SOME (Thunk
  e v)))`;;

(* HOL4 dataSemScript.sml:189-192: the overload add_space_safe, which
   the port expands *)

(* HOL4 dataSemScript.sml:194-195: the overload heap_peak, which the
   port expands *)

let add_space_def = cake_define
  `add_space (s:('c,'ffi)dataSem_state) k =
  dataSem_state_peak_heap_length_fupd (K ((\k s. MAX
  (dataSem_state_peak_heap_length s) (size_of_heap s + k)) k s))
  (dataSem_state_safe_for_space_fupd (K ((\k s.
            dataSem_state_safe_for_space s /\
            no_thunks_in_refs (dataSem_state_refs s) /\ size_of_heap
              s + k <= limits_heap_limit (dataSem_state_limits s)) k s))
              (dataSem_state_space_fupd (K k)
     s))`;;

(* Args-aware variant: cost reflects op_args + non-arg locals as the
   GC-root set, matching wordSem's view at the op's inner Alloc.
   stack_to_vs already covers s.locals (which, when the dataLang
   evaluator hands the state to do_app, is the NARROW cut without args). *)
let size_of_heap_args_def = cake_define
  `size_of_heap_args op_args (s:('c,'ffi)dataSem_state) =
     (let (n,_27,_28) = size_of (dataSem_state_limits s) (op_args ++
       stack_to_vs ((s:('c,'ffi)dataSem_state))) (dataSem_state_refs
       ((s:('c,'ffi)dataSem_state))) LN in
       n)`;;

(* HOL4 dataSemScript.sml:214-216: the overload add_space_safe_args,
   which the port expands *)

(* HOL4 dataSemScript.sml:218-219: the overload heap_peak_args, which
   the port expands *)

let consume_space_def = cake_define
  `consume_space k (s:('c,'ffi)dataSem_state) =
     (if dataSem_state_space s < k then NONE else SOME
       (dataSem_state_space_fupd (K (dataSem_state_space s - k)) s))`;;

(* Determines which operations are safe for space *)
let allowed_op_def = cake_define
  `allowed_op op _29 = (~(op = closLang_Install) /\ (!t i. ~(op =
  closLang_MemOp (closLang_MutCons t i))))`;;

let dataSem_v_to_list_def = cake_define
  `dataSem_v_to_list x1 =
        match x1 with
          (Block ts tag []:dataSem_v) ->
        (if tag = nil_tag then SOME [] else NONE)
        | (Block ts tag [h; bt]) ->
        (if tag = cons_tag then
          (match dataSem_v_to_list bt with SOME t -> SOME (h :: t) |
            _30 -> NONE) else NONE)
        | _31 -> NONE`;;
hol4_overload "v_to_list" "dataSem_v_to_list";;

(* HOL4 dataSemScript.sml:243-247: the overload bignum_limit, which
   the port expands *)

(* Gives an upper bound to the memory consuption of an operation *)
let space_consumed_def = cake_define
  `space_consumed s x2 x3 =
        match (s,x2,x3) with
          ((s:('c,'ffi)dataSem_state),closLang_BlockOp
            (closLang_ConsExtend tag),((Block _34 _35 xs':dataSem_v) ::
            Number lower :: Number len :: Number tot :: xs)) ->
      LENGTH (xs ++ TAKE (num_of_int len) (DROP (num_of_int lower)
        xs')) + 1
        | (s,(closLang_MemOp closLang_RefArray),[Number len; _36]) ->
          num_of_int len + 1
        | (s,(closLang_MemOp (closLang_RefByte _37)),[Number len;
          _38]) -> num_of_int len DIV (arch_size (dataSem_state_limits
          s) DIV 8) + 2
        | (s,(closLang_BlockOp (closLang_FromList n)),[Number len;
          lv]) -> num_of_int len + 1
        | (s,(closLang_IntOp closLang_Add),[Number i1; Number i2]) ->
       (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
         /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) i2
            /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1
            + i2) then 0 else (\i1 i2 s.
         let il = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i2 in
           2 * il + 2 * jl) i1 i2 s)
        | (s,(closLang_IntOp closLang_Sub),[Number i1; Number i2]) ->
       (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
         /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) i2
            /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1
            - i2) then 0 else (\i1 i2 s.
         let il = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i2 in
           2 * il + 2 * jl) i1 i2 s)
        | (s,(closLang_IntOp closLang_Mult),[Number i1; Number i2])
          ->
       (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
         /\ (&0) <= i1 /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) i2
            /\ (&0) <= i2 /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1
            * i2) then 0 else (\i1 i2 s.
         let il = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i2 in
           2 * il + 2 * jl) i1 i2 s)
        | (s,(closLang_IntOp closLang_Div),[Number i1; Number i2]) ->
       (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
         /\ (&0) <= i1 /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) i2
            /\ (&0) <= i2 /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1
            / i2) then 0 else (\i1 i2 s.
         let il = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i2 in
           2 * il + 2 * jl) i1 i2 s)
        | (s,(closLang_IntOp closLang_Mod),[Number i1; Number i2]) ->
       (if small_num (limits_arch_64_bit (dataSem_state_limits s)) i1
         /\ (&0) <= i1 /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) i2
            /\ (&0) <= i2 /\
          small_num (limits_arch_64_bit (dataSem_state_limits s)) (i1
            % i2) then 0 else (\i1 i2 s.
         let il = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i1 in
         let jl = bignum_size (limits_arch_64_bit
           (dataSem_state_limits s)) i2 in
           2 * il + 2 * jl) i1 i2 s)
        | (s,(closLang_BlockOp ListAppend),[lv1; lv2]) ->
      (match v_to_list lv1 with
       SOME l -> SUC (LENGTH l) * 3 | NONE -> 0)
        | (s,(op:closLang_op),(vs:dataSem_v list)) -> (0:num)`;;

let vb_size_def = cake_define
  `vb_size x1 =
        match x1 with
          (Block ts t ls:dataSem_v) -> 1 + t + SUM (MAP vb_size ls) +
            LENGTH ls
        | _39 -> 1`;;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
(* the clauses of the source overlap -- the second one says 0 of
   every value, the Block of the first one among them -- and HOL4
   takes the first that matches, so the port writes them as a
   match, which takes the first arm (see ml/lib/define.ml, "A
   definition whose clauses overlap").  As a list of clauses they
   would be inconsistent. *)
let vs_depth_def = cake_define_list_cheat CHEAT_TAC
  [`vs_depth x1 =
         match x1 with
           (Block ts t ls:dataSem_v) -> vs_depth_list ls
         | _40 -> 0`;
   `vs_depth_list [] = 0`;
   `vs_depth_list (x :: xs) = MAX (1 + vs_depth x) (vs_depth_list
  xs)`];;

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
          (closLang_MemOp (closLang_CopyByte _41),vs) ->
       OPTION_MAP2 MAX
        (sptree_lookup ByteCopy_location sfs)
        (OPTION_MAP2 MAX
           (lookup ByteCopyAdd_location sfs)
           (lookup ByteCopySub_location sfs))
        | ((closLang_MemOp (closLang_RefByte _42)),vs) ->
       OPTION_MAP2 MAX
        (lookup RefByte_location sfs)
        (lookup Replicate_location sfs)
        | ((closLang_MemOp (closLang_RefArray)),vs) ->
       OPTION_MAP2 MAX
        (lookup RefArray_location sfs)
        (lookup Replicate_location sfs)
        | ((closLang_MemOp closLang_XorByte),vs) ->
       lookup XorLoop_location sfs
        | ((closLang_MemOp (closLang_StringCmp b cmp)),vs) ->
       lookup StringCmpLoop_location sfs
        | ((closLang_BlockOp (closLang_ConsExtend _43)),vs) ->
       lookup MemCopy_location sfs
        // MemCopy looks not always necessary. Could be refined for more precise bounds.
        | ((closLang_BlockOp (closLang_FromList _44)),vs) ->
       OPTION_MAP2 MAX
        (lookup FromList_location sfs)
        (lookup FromList1_location sfs)
        | ((closLang_BlockOp ListAppend),vs) ->
       OPTION_MAP2 MAX
        (lookup Append_location sfs)
        (OPTION_MAP2 MAX
          (lookup AppendLenLoop_location sfs)
          (lookup AppendMainLoop_location sfs))
        | ((closLang_IntOp closLang_Div),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\ (&0) <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ (&0) <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 / n2) then
         OPTION_MAP2 MAX
           (lookup LongDiv_location sfs)
           (lookup LongDiv1_location sfs) else
         OPTION_MAP2 MAX (lookup Div_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((closLang_IntOp closLang_Mod),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\ (&0) <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ (&0) <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 % n2) then
         OPTION_MAP2 MAX
           (lookup LongDiv_location sfs)
           (lookup LongDiv1_location sfs) else
         OPTION_MAP2 MAX (lookup Mod_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((closLang_IntOp closLang_Mult),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\ (&0) <= n1 /\
          small_num (limits_arch_64_bit lims) n2 /\ (&0) <= n2 /\
          small_num (limits_arch_64_bit lims) (n1 * n2) then SOME 0
            else
         OPTION_MAP2 MAX (lookup Mul_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((closLang_BlockOp closLang_Equal),[v1; v2]) ->
      (eq_code_stack_max (MIN (vs_depth v1 + 1) (vs_depth v2 + 1))
        sfs)
        | ((closLang_IntOp closLang_Sub),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\
          small_num (limits_arch_64_bit lims) n2 /\
          small_num (limits_arch_64_bit lims) (n1 - n2) then SOME 0
            else
         OPTION_MAP2 MAX (lookup Sub_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((closLang_IntOp closLang_Add),[Number n1; Number n2]) ->
       (if small_num (limits_arch_64_bit lims) n1 /\
          small_num (limits_arch_64_bit lims) n2 /\
          small_num (limits_arch_64_bit lims) (n1 + n2) then SOME 0
            else
         OPTION_MAP2 MAX (lookup Add_location sfs)
           (max_depth sfs AnyArith_call_tree))
        | ((closLang_IntOp closLang_LessEq),vs) ->
       // This is a conservative estimate --- no calls happen for smallnums
       OPTION_MAP2 MAX
        (lookup Compare_location sfs)
        (lookup Compare1_location sfs)
        | ((closLang_IntOp closLang_Less),vs) ->
       // This is a conservative estimate --- no calls happen for smallnums
       OPTION_MAP2 MAX
        (lookup Compare_location sfs)
        (lookup Compare1_location sfs)
        // TODO: add more clauses as the need arises
        | (p,vs) ->
        (if allowed_op p (LENGTH vs) then SOME 0 else NONE)`;;

(* HOL4 dataSemScript.sml:405-412: the overload do_space_safe, which
   the port expands *)

(* HOL4 dataSemScript.sml:414-417: the overload do_space_peak, which
   the port expands *)

let do_space_def = cake_define
  `do_space op vs (s:('c,'ffi)dataSem_state) =
     (if op_space_reset op then SOME
       (dataSem_state_peak_heap_length_fupd (K ((\op vs s. if
       op_space_reset op then (\k op_args s. MAX
       (dataSem_state_peak_heap_length s) (size_of_heap_args op_args s +
       k)) (space_consumed s op vs) vs s else
       dataSem_state_peak_heap_length s) op vs s))
       (dataSem_state_safe_for_space_fupd (K ((\op vs s. if
       op_space_reset op then
                    dataSem_state_safe_for_space s /\
                    no_thunks_in_refs (dataSem_state_refs s) /\
                        size_of_heap_args vs s + space_consumed s
                          op vs <= limits_heap_limit
                          (dataSem_state_limits s) else
                          dataSem_state_safe_for_space s) op vs s))
                          (dataSem_state_space_fupd (K 0) s))) else
                          if op_space_req op (LENGTH vs) = 0 then
                          SOME s else consume_space (op_space_req op
                          (LENGTH vs)) s)`;;

let size_of_stack_frame_def = cake_define_list
  [`size_of_stack_frame (Env n _46:dataSem_stack) = n`;
   `size_of_stack_frame (dataSem_Exc n _47 _48) = OPTION_MAP ((+)
  3) n`];;

let size_of_stack_def = cake_define
  `size_of_stack = FOLDR (OPTION_MAP2 (+) o size_of_stack_frame)
  (SOME 1)`;;

let do_stack_def = cake_define
  `do_stack op vs (s:('c,'ffi)dataSem_state) =
   (let new_stack = OPTION_MAP2 (+) (stack_consumed
     (dataSem_state_stack_frame_sizes s) (dataSem_state_limits s) op vs)
                       (OPTION_MAP2 (+) (size_of_stack
                         (dataSem_state_stack s))
                         (dataSem_state_locals_size s)) in
                         dataSem_state_stack_max_fupd (K (OPTION_MAP2
                         MAX (dataSem_state_stack_max s) new_stack))
                         (dataSem_state_safe_for_space_fupd (K (
                              dataSem_state_safe_for_space s /\ the F
                                (OPTION_MAP ((>) (limits_stack_limit
                                (dataSem_state_limits s))) new_stack)))
     s))`;;

let dataSem_v_to_bytes_def = cake_define
  `dataSem_v_to_bytes lv = some (\(ns:word8 list).
                     v_to_list lv = SOME (MAP (Number o (&) o w2n)
                       ns))`;;
hol4_overload "v_to_bytes" "dataSem_v_to_bytes";;

let dataSem_v_to_words_def = cake_define
  `dataSem_v_to_words lv = some (\ns. v_to_list lv = SOME (MAP Word64
  ns))`;;
hol4_overload "v_to_words" "dataSem_v_to_words";;

(* TODO: move this stuff *)
let dataSem_isClos_def = cake_define
  `dataSem_isClos t1 l1 = (((t1 = closure_tag) \/ (t1 =
  partial_app_tag)) /\ ~(l1 = []))`;;
hol4_overload "isClos" "dataSem_isClos";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
(* the clauses of the source overlap -- a later one says
   Eq_type_error of a pair that an earlier one has already given a
   value -- and HOL4 takes the first that matches, so the port
   writes them as a match, which takes the first arm (see
   ml/lib/define.ml, "A definition whose clauses overlap").  As a
   list of clauses they would be inconsistent. *)
let dataSem_do_eq_def = cake_define_list_cheat CHEAT_TAC
  [`dataSem_do_eq refs x2 x3 =
         match (x2,x3) with
           ((CodePtr _50:dataSem_v),_51) -> Eq_type_error
         | (_52,(CodePtr _53)) -> Eq_type_error
         | ((Number n1),(Number n2)) -> (Eq_val (n1 = n2))
         | ((Number _54),_55) -> Eq_type_error
         | (_56,(Number _57)) -> Eq_type_error
         | ((Word64 w1),(Word64 w2)) -> (Eq_val (w1 = w2))
         | ((Word64 _58),_59) -> Eq_type_error
         | (_60,(Word64 _61)) -> Eq_type_error
         | ((RefPtr b1 n1),(RefPtr b2 n2)) ->
        (if b1 /\ b2 then
         (match (sptree_lookup n1 refs,sptree_lookup n2 refs) with
            (SOME (ByteArray T bs1),SOME (ByteArray T bs2)) ->
              Eq_val (bs1 = bs2) | (SOME (ByteArray T bs1),_62) ->
              Eq_type_error | (_63,SOME (ByteArray T bs2)) ->
              Eq_type_error | _64 -> Eq_val (n1 = n2)) else
              Eq_type_error)
         | ((RefPtr _65 _66),_67) -> Eq_type_error
         | (_68,(RefPtr _69 _70)) -> Eq_type_error
         // TODO: How time-stamps impact equality between blocks?
         | ((Block _71 t1 l1),(Block _72 t2 l2)) ->
       (if isClos t1 l1 \/ isClos t2 l2 then if isClos t1 l1 /\
         isClos t2 l2 then Eq_val T else Eq_type_error else if (t1 =
         t2) /\ (LENGTH l1 = LENGTH l2) then dataSem_do_eq_list refs
         l1 l2 else Eq_val F)`;
   `dataSem_do_eq_list refs x2 x3 =
         match (x2,x3) with
           ([],[]) -> Eq_val T
         | ((v1 :: vs1),(v2 :: vs2)) ->
       (match dataSem_do_eq refs v1 v2 with Eq_val T ->
         dataSem_do_eq_list refs vs1 vs2 | Eq_val F -> Eq_val F | bad ->
         bad)
         | (_73,_74) -> Eq_val F`];;
hol4_overload "do_eq" "dataSem_do_eq";;
hol4_overload "do_eq_list" "dataSem_do_eq_list";;

(* HOL4 dataSemScript.sml:499-500: the overload Error, which the port
   expands *)

let dataSem_do_install_def = cake_define
  `dataSem_do_install vs (s:('c,'ffi)dataSem_state) =
       (match vs with [v1; v2; vl1; vl2] ->
            (match (v_to_bytes v1,v_to_words v2) with (SOME
              bytes,SOME data) ->
                (if ~(vl1 = Number (&(LENGTH bytes))) \/ ~(vl2 =
                  Number (&(LENGTH data))) then Rerr (Rabort
                  Rtype_error) else
                let (cfg,progs) = dataSem_state_compile_oracle s 0 in
                let new_oracle = misc_shift_seq 1
                  (dataSem_state_compile_oracle s) in
                  (match (dataSem_state_compile s cfg progs,progs)
                    with (SOME (bytes',data',cfg'),(k,prog) :: _75) ->
                       (if bytes = bytes' /\ data = data' /\ FST
                         (new_oracle 0) = cfg' then
                         let s' = dataSem_state_compile_oracle_fupd
                           (K new_oracle) (dataSem_state_code_fupd (K
                           (union (dataSem_state_code s) (fromAList
                           progs))) (dataSem_state_safe_for_space_fupd
                           (K F)
                           s)) in
                           Rval (CodePtr k,s') else Rerr (Rabort
                             Rtype_error)) | _76 -> Rerr (Rabort
                             Rtype_error))) | _77 -> Rerr (Rabort
                             Rtype_error)) | _78 -> Rerr (Rabort
                             Rtype_error))`;;
hol4_overload "do_install" "dataSem_do_install";;

let dataSem_list_to_v_def = cake_define_list
  [`dataSem_list_to_v ts t [] = t`;
   `dataSem_list_to_v ts t (h :: l) = Block ts cons_tag [h;
  dataSem_list_to_v (ts + 1) t l]`];;
hol4_overload "list_to_v" "dataSem_list_to_v";;

(* HOL4 dataSemScript.sml:534: the overload Block_nil, which the port
   expands *)

let with_fresh_ts_def = cake_define
  `with_fresh_ts (s:('c,'ffi)dataSem_state) n f = (match
  dataSem_state_tstamps s with
                            SOME ts -> f ts
                              (dataSem_state_tstamps_fupd (K (SOME
                              (ts + n))) s) | NONE -> f 0 s)`;;

let lim_safe_part_def = cake_define_list
  [`lim_safe_part lims (Con tag xs:const_part) <=> (if xs = [] then tag
  < 2 EXP (arch_size lims) DIV 16 else
                              LENGTH xs < 2 EXP limits_length_limit
                                lims /\
                              LENGTH xs < 2 EXP (arch_size lims - 4)
                                /\
                              4 * tag < 2 EXP (arch_size lims) DIV
                                16 /\
                              4 * tag < 2 EXP (arch_size lims -
                                limits_length_limit lims - 2))`;
   `lim_safe_part lims (Int i:const_part) <=>
         (if small_num (limits_arch_64_bit lims) i then T else
            let il = bignum_size (limits_arch_64_bit lims) i in
              il <= 2 EXP limits_length_limit lims)`;
   `lim_safe_part lims (closLang_Str s:const_part) <=>
         (let i = strlen s in
            i DIV (arch_size lims DIV 8) < 2 EXP (arch_size lims)
              DIV arch_size lims /\
            i DIV (arch_size lims DIV 8) + 1 < 2 EXP
              limits_length_limit lims /\
            small_num (limits_arch_64_bit lims) (&i))`;
   `lim_safe_part lims (W64 w:const_part) <=> 1 <
  limits_length_limit lims`];;

let lim_safe_def = cake_define
  `lim_safe lims x2 xs =
        match (x2,xs) with
          (closLang_BlockOp (closLang_Cons tag),xs) ->
       (if xs = [] then tag < 2 EXP (arch_size lims) DIV 16 else
         LENGTH xs < 2 EXP limits_length_limit lims /\
         LENGTH xs < 2 EXP (arch_size lims - 4) /\
         4 * tag < 2 EXP (arch_size lims) DIV 16 /\
         4 * tag < 2 EXP (arch_size lims - limits_length_limit lims -
           2))
        | ((closLang_MemOp (closLang_MutCons tag i)),xs) ->
         (LENGTH xs < 2 EXP limits_length_limit lims /\
          LENGTH xs < 2 EXP (arch_size lims - 4) /\
          4 * tag < 2 EXP (arch_size lims) DIV 16 /\
          4 * tag < 2 EXP (arch_size lims - limits_length_limit lims
            - 2))
        | ((closLang_BlockOp (closLang_FromList tag)),xs) ->
      (match xs with [len; lv] ->
         (match v_to_list lv with SOME n ->
             (if len = Number (&(LENGTH n)) then small_num
               (limits_arch_64_bit lims) (&(LENGTH n)) /\
                  LENGTH n < 2 EXP limits_length_limit lims /\
                  LENGTH n < arch_size lims DIV 16 /\
                  4 * tag < 2 EXP (arch_size lims -
                    limits_length_limit lims - 2) /\
                  4 * tag < 2 EXP (arch_size lims) DIV 16 else T) |
                    _79 -> T) | _80 -> T)
        | ((closLang_BlockOp ListAppend),[x1; x2]) ->
      (match (v_to_list x1,v_to_list x2) with (SOME xs,SOME ys) ->
           1 < limits_length_limit lims /\
           3 * (SUC (LENGTH xs)) < 2 EXP (arch_size lims) DIV 8 | _81
             -> T)
        | ((closLang_BlockOp (closLang_ConsExtend tag)),(Block _82
          _83 xs' :: Number lower :: Number len :: Number tot :: xs)) ->
           (if lower < (&0) \/ len < (&0) \/ lower + len > &(LENGTH
             xs') \/
              tot = (&0) \/ ~(tot = &(LENGTH xs) + len) then T else
                LENGTH (xs ++ TAKE (num_of_int len) (DROP (num_of_int
                lower) xs')) < 2 EXP limits_length_limit lims /\
                LENGTH (xs ++ TAKE (num_of_int len) (DROP (num_of_int
                  lower) xs')) < 2 EXP (arch_size lims) DIV 16 /\
                4 * tag < 2 EXP (arch_size lims) DIV 16 /\
                4 * tag < 2 EXP (arch_size lims - limits_length_limit
                  lims - 2))
        | ((closLang_IntOp closLang_Add),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 + i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp closLang_Sub),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\
          small_num (limits_arch_64_bit lims) i2 /\
          small_num (limits_arch_64_bit lims) (i1 - i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp closLang_Mult),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ (&0) <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ (&0) <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 * i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp closLang_Div),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ (&0) <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ (&0) <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 / i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_IntOp closLang_Mod),[Number i1; Number i2]) ->
      (if small_num (limits_arch_64_bit lims) i1 /\ (&0) <= i1 /\
          small_num (limits_arch_64_bit lims) i2 /\ (&0) <= i2 /\
          small_num (limits_arch_64_bit lims) (i1 % i2) then T else
         let il = bignum_size (limits_arch_64_bit lims) i1 in
         let jl = bignum_size (limits_arch_64_bit lims) i2 in
           il + jl <= 2 EXP limits_length_limit lims)
        | ((closLang_MemOp closLang_RefArray),[Number i; v]) ->
      ((&0) <= i /\
       num_of_int i < 2 EXP (arch_size lims) DIV 16 /\
       num_of_int i < 2 EXP limits_length_limit lims)
        | ((closLang_MemOp (closLang_RefByte _84)),(Number i :: xs))
          ->
      ((&0) <= i /\
       num_of_int i DIV (arch_size lims DIV 8) < 2 EXP (arch_size
         lims) DIV arch_size lims /\
       num_of_int i DIV (arch_size lims DIV 8) + 1 < 2 EXP
         limits_length_limit lims /\
       small_num (limits_arch_64_bit lims) i)
        | ((closLang_MemOp closLang_Ref),xs) ->
      (LENGTH xs < 2 EXP limits_length_limit lims /\
       LENGTH xs < 2 EXP arch_size lims DIV 16)
        | ((closLang_BlockOp (closLang_Build parts')),_85) ->
      EVERY (lim_safe_part lims) parts'
        | ((closLang_WordOp WordToInt),_86) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp WordFromInt),_87) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (WordOpw ast_W64 _88)),_89) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (WordShift ast_W64 _90 _91)),_92) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (WordFromWord _93)),_94) ->
      (1 < limits_length_limit lims)
        | ((closLang_WordOp (FP_cmp _95)),_96) -> has_fp_ops
      lims
        | ((closLang_WordOp (FP_uop _97)),_98) ->
      (has_fp_ops lims /\ (limits_arch_64_bit lims \/ 1 <
        limits_length_limit lims))
        | ((closLang_WordOp (FP_bop _99)),_100) ->
      (has_fp_ops lims /\ (limits_arch_64_bit lims \/ 1 <
        limits_length_limit lims))
        | ((closLang_WordOp (FP_top _101)),_102) ->
      (has_fp_ops lims /\ limits_has_fp_tops lims /\
        (limits_arch_64_bit lims \/ 1 < limits_length_limit lims))
        | (_103,_104) -> T`;;

let do_lim_safe = cake_define
  `do_lim_safe (s:('c,'ffi)dataSem_state) op vs =
  dataSem_state_safe_for_space_fupd (K (
                             lim_safe (dataSem_state_limits s) op vs
                               /\ dataSem_state_safe_for_space s))
   s`;;

let check_lim_def = cake_define
  `check_lim (s:('c,'ffi)dataSem_state) n =
  dataSem_state_safe_for_space_fupd (K (n < 2 EXP limits_length_limit
  (dataSem_state_limits s) /\ dataSem_state_safe_for_space
                              s))
      s`;;

let dataSem_do_part_def = cake_define_list
  [`dataSem_do_part m (Int i:const_part) s ts = (Number i,s,ts)`;
   `dataSem_do_part m (W64 w:const_part) s ts = (Word64 w,s,ts)`;
   `dataSem_do_part m (Con t ns:const_part) s ts =
      (if ns = [] then (Block 0 t [],s,ts) else match ts with
        NONE -> (Block 0 t (MAP m ns),s,ts) | SOME n -> (Block n t
        (MAP m ns),s,SOME (n + (1:num))))`;
   `dataSem_do_part m (closLang_Str t:const_part) s ts =
      (let ptr = (LEAST (\ptr. ~(ptr IN domain s))) in
      let bytes = MAP (n2w o ORD) (explode t) in
        (RefPtr T ptr,insert ptr (ByteArray T bytes) s,ts))`];;
hol4_overload "do_part" "dataSem_do_part";;

let dataSem_do_build_def = cake_define_list
  [`dataSem_do_build m i [] s ts = (m (i - 1),s,ts)`;
   `dataSem_do_build m i (p :: rest) s ts =
      (let (x,s1,ts1) = do_part m p s ts in
        dataSem_do_build ((i =+ x) m) (i + 1) rest s1 ts1)`];;
hol4_overload "do_build" "dataSem_do_build";;

let dataSem_do_build_const_def = cake_define
  `dataSem_do_build_const xs s ts = do_build (\x. Number (&0)) 0 xs s
  ts`;;
hol4_overload "do_build_const" "dataSem_do_build_const";;

let dataSem_do_int_app_def = cake_define
  `dataSem_do_int_app x1 x2 =
      match (x1,x2) with
        ((Const n:closLang_int_op),[]) ->
     (if small_enough_int n then SOME (Number n) else NONE)
      | ((Add),[Number n1; Number n2]) -> SOME (Number (n1 + n2))
      | ((Sub),[Number n1; Number n2]) -> SOME (Number (n1 - n2))
      | ((closLang_Mult),[Number n1; Number n2]) -> SOME (Number (n1
        * n2))
      | ((Div),[Number n1; Number n2]) ->
       (if n2 = (&0) then NONE else SOME (Number (n1 / n2)))
      | ((Mod),[Number n1; Number n2]) ->
       (if n2 = (&0) then NONE else SOME (Number (n1 % n2)))
      | ((Less),[Number n1; Number n2]) -> SOME (Boolv (n1 < n2))
      | ((closLang_LessEq),[Number n1; Number n2]) -> SOME (Boolv (n1
        <= n2))
      | ((Greater),[Number n1; Number n2]) -> SOME (Boolv (n1 > n2))
      | ((closLang_GreaterEq),[Number n1; Number n2]) -> SOME (Boolv
        (n1 >= n2))
      | ((closLang_LessConstSmall n),[Number i]) ->
         (if (&0) <= i /\ i <= (&1000000) /\ n < 1000000 then
           SOME (Boolv (i < &n)) else NONE)
      | ((op:closLang_int_op),(vs:dataSem_v list)) -> NONE`;;
hol4_overload "do_int_app" "dataSem_do_int_app";;

let dataSem_do_word_app_def = cake_define
  `dataSem_do_word_app x1 ws =
        match (x1,ws) with
          (WordOpw ast_W8 opw,[(Number n1:dataSem_v); Number n2]) ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw ast_W64 opw),[Word64 w1; Word64 w2]) ->
           SOME (Word64 (opw_lookup opw w1 w2))
        | ((WordTest ast_W8 test),[Number n1; Number n2]) ->
          (if (&0) <= n1 /\ n1 < (&256) /\ (&0) <= n2 /\ n2 < (&256)
            then
             (match test with Equal -> SOME (Boolv (n1 = n2)) |
               ast_Compare Lt -> SOME (Boolv (n1 < n2)) | ast_Compare
               ast_Leq -> SOME (Boolv (n1 <= n2)) | _105 -> NONE) else
               NONE)
        | ((WordShift ast_W8 sh n),[Number i]) ->
          (match some (\(w:word8). i = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (Number (&(w2n (shift_lookup sh w n)))))
        | ((WordShift ast_W64 sh n),[Word64 w]) ->
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
                (SOME (Word64 (fp_top_comp t_op w1 w2 w3))) | _106 ->
                  NONE)
        | ((FP_bop bop),ws) ->
           (match ws with [Word64 w1; Word64 w2] -> (SOME (Word64
             (fp_bop_comp bop w1 w2))) | _107 -> NONE)
        | ((FP_uop uop),ws) ->
           (match ws with [Word64 w] -> (SOME (Word64 (fp_uop_comp
             uop w))) | _108 -> NONE)
        | ((FP_cmp cmp),ws) ->
           (match ws with [Word64 w1; Word64 w2] -> (SOME (Boolv
             (fp_cmp_comp cmp w1 w2))) | _109 -> NONE)
        | ((op:closLang_word_op),(vs:dataSem_v list)) -> NONE`;;
hol4_overload "do_word_app" "dataSem_do_word_app";;

let dest_Boolv_def = cake_define
  `dest_Boolv x1 =
      match x1 with
        (Block _111 tag xs:dataSem_v) ->
     (if xs = [] /\ tag < 2 then SOME (tag = 1) else NONE)
      | _112 -> NONE`;;

let dataSem_dest_thunk_ret_INDUCT,dataSem_dest_thunk_ret_RECURSION =
  define_datatype
  "dataSem_dest_thunk_ret = dataSem_BadRef | dataSem_NotThunk | \
   dataSem_IsThunk (thunk_mode) (dataSem_v)";;
hol4_overload "BadRef" "dataSem_BadRef";;
hol4_overload "NotThunk" "dataSem_NotThunk";;
hol4_overload "IsThunk" "dataSem_IsThunk";;

let dataSem_dest_thunk_def = cake_define
  `dataSem_dest_thunk v refs =
      match v with
        (RefPtr b ptr:dataSem_v) ->
     (match lookup ptr refs with NONE -> BadRef | SOME (Thunk
       Evaluated v) ->
          (if b then BadRef else IsThunk Evaluated v) | SOME (Thunk
            NotEvaluated v) ->
          (if b then BadRef else IsThunk NotEvaluated v) | SOME _113
            -> NotThunk)
      | v -> NotThunk`;;
hol4_overload "dest_thunk" "dataSem_dest_thunk";;

let dataSem_bad_thunk_update_def = cake_define
  `dataSem_bad_thunk_update m v refs <=>
     m = Evaluated /\ ~(dest_thunk v refs = NotThunk)`;;
hol4_overload "bad_thunk_update" "dataSem_bad_thunk_update";;

(* mirrors bviSem$finalise_cons, but threads the timestamp counter so that
   each block produced by the finalisation gets a fresh time stamp *)
(* HOL4 dataSemScript.sml:854-858: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let dataSem_finalise_cons_def = cake_define_try_tac (fun () ->
  `MEASURE (sptree_size o FST o SND)`)
  CHEAT_TAC
  `dataSem_finalise_cons v refs ts =
        match v with
          (RefPtr b ptr:dataSem_v) ->
       (match lookup ptr refs with SOME (bvlSem_MutBlock tag
         finalised l c r) ->
           (if ~finalised then
             (match dataSem_finalise_cons c (delete ptr refs) ts with
               SOME (c',refs',ts') ->
                  SOME (Block (match ts' with NONE -> 0 | SOME n ->
                    n) tag (l ++ [c'] ++ r),
                        insert ptr (bvlSem_MutBlock tag T l c r)
                          refs',
                        OPTION_MAP SUC ts') | NONE -> NONE) else
                          NONE) | SOME res -> SOME (RefPtr b
                          ptr,refs,ts) | NONE -> NONE)
        | v -> SOME (v,refs,ts)`;;
hol4_overload "finalise_cons" "dataSem_finalise_cons";;

let dataSem_do_app_aux_def = cake_define
  `dataSem_do_app_aux op (vs:dataSem_v list) (s:('c,'ffi)dataSem_state)
  =
     (match (op,vs) with (
        // bvi part
        closLang_Label l,xs) ->
         (match xs with [] -> (if l IN domain (dataSem_state_code s)
           then
                    Rval (CodePtr l,s) else ((Rerr (Rabort
                      Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                      ,dataSem_v)semanticPrimitives_result)) | _114 ->
                      ((Rerr (Rabort
                      Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                      ,dataSem_v)semanticPrimitives_result)) |
                      (closLang_GlobOp closLang_GlobalsPtr,xs) ->
         (match xs with [] -> (match dataSem_state_global s with SOME
           p -> Rval (RefPtr T p,s) | NONE -> ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | _115 -> ((Rerr
           (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_GlobOp
           (closLang_Global n),xs) ->
         (match xs with [] -> (match dataSem_state_global s with SOME
           ptr ->
                       (match sptree_lookup ptr (dataSem_state_refs
                         s) with SOME (ValueArray xs) ->
                            (if n < LENGTH xs then Rval (EL n xs,s)
                              else ((Rerr (Rabort
                              Rtype_error)):(dataSem_v#('c
                              ,'ffi)dataSem_state
                              ,dataSem_v)semanticPrimitives_result)) |
                              _116 -> ((Rerr (Rabort
                              Rtype_error)):(dataSem_v#('c
                              ,'ffi)dataSem_state
                              ,dataSem_v)semanticPrimitives_result)) |
                              NONE -> ((Rerr (Rabort
                              Rtype_error)):(dataSem_v#('c
                              ,'ffi)dataSem_state
                              ,dataSem_v)semanticPrimitives_result)) |
                              _117 -> ((Rerr (Rabort
                              Rtype_error)):(dataSem_v#('c
                              ,'ffi)dataSem_state
                              ,dataSem_v)semanticPrimitives_result)) |
                              (closLang_GlobOp (closLang_SetGlobal
                              n),xs) ->
         (match xs with [x] -> (match dataSem_state_global s with
           SOME ptr ->
                        (match lookup ptr (dataSem_state_refs s) with
                          SOME (ValueArray xs) ->
                             (if n < LENGTH xs then Rval
                               (Unit,dataSem_state_refs_fupd (K (insert
                               ptr
                              (ValueArray (LUPDATE x n xs))
                                (dataSem_state_refs s))) s) else ((Rerr
                                (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                _118 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                NONE -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                _119 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                (closLang_GlobOp
                                (closLang_SetGlobalsPtr),xs) ->
         (match xs with [RefPtr T p] -> Rval
           (Unit,dataSem_state_global_fupd (K (SOME p)) s) | _120 ->
           ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           (closLang_FromList n),xs) ->
         (match xs with [len; lv] ->
             (match v_to_list lv with SOME [] -> (if len = Number
               (&0) then Rval (Block 0 n [],s) else ((Rerr (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
               ,dataSem_v)semanticPrimitives_result)) | SOME vs -> (if
               len = Number (&(LENGTH vs)) then with_fresh_ts s 1
                             (\ts s'. Rval (Block ts n vs,
                              check_lim (s') (LENGTH vs))) else
                                ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                _121 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                _122 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                (closLang_MemOp (closLang_RefByte f),xs)
                                ->
         (match xs with [Number i; Number b] ->
             (if (&0) <= i /\ (?(w:word8). b = &(w2n w)) then
               let ptr = (LEAST (\ptr. ~(ptr IN domain
                 (dataSem_state_refs s)))) in
                 Rval (RefPtr T ptr,dataSem_state_refs_fupd (K
                   (insert ptr
                   (ByteArray f (REPLICATE (num_of_int i) (i2w b)))
                     (dataSem_state_refs s))) s) else Rerr (Rabort
                     Rtype_error)) | _123 -> Rerr (Rabort Rtype_error))
                     | (closLang_GlobOp closLang_AllocGlobal,_124) ->
                     Rerr (Rabort Rtype_error) | (closLang_MemOp
                     closLang_FromListByte,_125) -> Rerr (Rabort
                     Rtype_error) | (closLang_MemOp
                     closLang_ConcatByteVec,_126) -> Rerr (Rabort
                     Rtype_error) | (closLang_MemOp (closLang_CopyByte
                     T),_127) -> Rerr (Rabort Rtype_error) | (
        // bvl part
        closLang_BlockOp (closLang_Build parts'),[]) ->
         (match do_build_const parts' (dataSem_state_refs s)
           (dataSem_state_tstamps s) with (v,s1,ts1) -> Rval
           (v,dataSem_state_tstamps_fupd (K ts1)
           (dataSem_state_refs_fupd (K s1) s))) | (closLang_BlockOp
           (closLang_Cons tag),xs) -> (if xs = [] then Rval (Block 0 tag
           [],s) else with_fresh_ts s 1
                              (\ts s'. Rval (Block ts tag xs,
                              check_lim s' (LENGTH xs)))) |
                                (closLang_BlockOp (closLang_ConsExtend
                                tag),Block x y xs' :: Number lower ::
                                Number len :: Number tot :: xs) ->
         (if lower < (&0) \/ len < (&0) \/ lower + len > &(LENGTH
           xs') \/
            tot = (&0) \/ ~(tot = &(LENGTH xs) + len) then
           ((Rerr (Rabort
             Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
             ,dataSem_v)semanticPrimitives_result) else with_fresh_ts s
             1
                            (\ts s'.
                              let l = (xs ++ TAKE (num_of_int len)
                                (DROP (num_of_int lower) xs')) in Rval
                                (Block ts tag l,
                              check_lim s' (LENGTH l)))) |
                                (closLang_BlockOp (closLang_ConsExtend
                                tag),_128) -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result) |
                                (closLang_MemOp closLang_El,[Block _129
                                tag xs; Number i]) ->
         (if (&0) <= i /\ num_of_int i < LENGTH xs then Rval (EL
           (num_of_int i) xs,s) else ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_El,[RefPtr _130 ptr; Number i]) ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (ValueArray xs) ->
             (if (&0) <= i /\ i < &(LENGTH xs) then Rval (EL
               (num_of_int i) xs,s) else ((Rerr (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
               ,dataSem_v)semanticPrimitives_result)) | _131 -> ((Rerr
               (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
               ,dataSem_v)semanticPrimitives_result)) |
               (closLang_BlockOp (closLang_ElemAt n),[Block _132 tag
               xs]) ->
         (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           (closLang_ElemAt n),[RefPtr _133 ptr]) ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (ValueArray xs) ->
             (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
               (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
               ,dataSem_v)semanticPrimitives_result)) | _134 -> ((Rerr
               (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
               ,dataSem_v)semanticPrimitives_result)) |
               (closLang_BlockOp (closLang_BoolTest test),[v1; v2]) ->
         (match (dest_Boolv v1,dest_Boolv v2) with (SOME b1,SOME b2)
           -> Rval (Boolv (b1 = b2),s) | _135 -> ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           closLang_BoolNot,[v1]) ->
         (match dest_Boolv v1 with SOME b1 -> Rval (Boolv (~b1),s) |
           _136 -> ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           ListAppend,[x1; x2]) ->
         (match (v_to_list x1,v_to_list x2) with (SOME xs,SOME ys) ->
              with_fresh_ts ((s:('c,'ffi)dataSem_state)) (LENGTH xs)
              (\ts s'. Rval (list_to_v ts x2 xs,
                            check_lim (s') 2)) | _137 -> ((Rerr
                              (Rabort
                              Rtype_error)):(dataSem_v#('c
                              ,'ffi)dataSem_state
                              ,dataSem_v)semanticPrimitives_result)) |
                              (closLang_BlockOp
                              closLang_LengthBlock,[Block _138 tag xs])
                              ->
         Rval (Number (&(LENGTH xs)),s) | (closLang_MemOp
           closLang_Length,[RefPtr _139 ptr]) ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (ValueArray xs) ->
               Rval (Number (&(LENGTH xs)),s) | _140 -> ((Rerr
                 (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                 ,dataSem_v)semanticPrimitives_result)) |
                 (closLang_MemOp closLang_LengthByte,[RefPtr _141 ptr])
                 ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (ByteArray _142 xs) ->
               Rval (Number (&(LENGTH xs)),s) | _143 -> ((Rerr
                 (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                 ,dataSem_v)semanticPrimitives_result)) |
                 (closLang_MemOp closLang_RefArray,[Number i; v]) ->
         (if (&0) <= i then
           let ptr = (LEAST (\ptr. ~(ptr IN domain
             (dataSem_state_refs s)))) in
             Rval (RefPtr T ptr,dataSem_state_refs_fupd (K (insert
               ptr
                              (ValueArray (REPLICATE (num_of_int i)
                                v)) (dataSem_state_refs s)))
                   s) else ((Rerr (Rabort
                     Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                     ,dataSem_v)semanticPrimitives_result)) |
                     (closLang_MemOp closLang_DerefByte,[RefPtr _144
                     ptr; Number i]) ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (ByteArray _145 ws) ->
             (if (&0) <= i /\ i < &(LENGTH ws) then Rval (Number
               (&(w2n (EL (num_of_int i) ws))),s) else ((Rerr (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
               ,dataSem_v)semanticPrimitives_result)) | _146 -> ((Rerr
               (Rabort
               Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
               ,dataSem_v)semanticPrimitives_result)) | (closLang_MemOp
               closLang_UpdateByte,[RefPtr _147 ptr; Number i; Number
               b]) ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (ByteArray f bs) ->
             (if (&0) <= i /\ i < &(LENGTH bs) /\ (?(w:word8). b =
               &(w2n w)) then
                Rval (Unit,dataSem_state_refs_fupd (K (insert ptr
                  (ByteArray f (LUPDATE (i2w b) (num_of_int i) bs))
                    (dataSem_state_refs s))) s) else ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                    ,dataSem_v)semanticPrimitives_result)) | _148 ->
                    ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                    ,dataSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp closLang_XorByte,[RefPtr _149 dst;
                    RefPtr _150 src]) ->
         (match (lookup src (dataSem_state_refs s),lookup dst
           (dataSem_state_refs s)) with (SOME (ByteArray _151 ws),SOME
           (ByteArray f ds)) ->
            (match xor_bytes ws ds with SOME ds1 -> Rval
              (Unit,dataSem_state_refs_fupd (K (insert dst (ByteArray f
              ds1) (dataSem_state_refs s))) s) | NONE -> ((Rerr (Rabort
              Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
              ,dataSem_v)semanticPrimitives_result)) | _152 -> ((Rerr
              (Rabort
              Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
              ,dataSem_v)semanticPrimitives_result)) | (closLang_MemOp
              (closLang_StringCmp b cmp),[RefPtr _153 s1; RefPtr _154
              s2]) ->
         (match (lookup s1 (dataSem_state_refs s),lookup s2
           (dataSem_state_refs s)) with (SOME (ByteArray _155 ws1),SOME
           (ByteArray _156 ws2)) ->
              (let s1 = implode (MAP (CHR o w2n) ws1) in
               let s2 = implode (MAP (CHR o w2n) ws2) in
                 Rval (Boolv (str_cmp b cmp s1 s2),s)) | _157 ->
                   ((Rerr (Rabort
                   Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                   ,dataSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp (closLang_CopyByte F),[RefPtr _158
                   src; Number srcoff; Number len; RefPtr _159 dst;
                   Number dstoff]) ->
         (match (lookup src (dataSem_state_refs s),lookup dst
           (dataSem_state_refs s)) with (SOME (ByteArray _160 ws),SOME
           (ByteArray fl ds)) ->
            (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
               // no time-stamp
               SOME ds -> Rval (Unit,dataSem_state_refs_fupd (K
                 (insert dst (ByteArray fl ds) (dataSem_state_refs s)))
                 s) | NONE -> ((Rerr (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                 ,dataSem_v)semanticPrimitives_result)) | _161 -> ((Rerr
                 (Rabort
                 Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                 ,dataSem_v)semanticPrimitives_result)) |
                 (closLang_BlockOp (closLang_TagEq n),[Block _162 tag
                 xs]) ->
         Rval (Boolv (tag = n),s) | (closLang_BlockOp (closLang_LenEq
           l),[Block _163 tag xs]) ->
         Rval (Boolv (LENGTH xs = l),s) | (closLang_BlockOp
           (closLang_TagLenEq n l),[Block _164 tag xs]) ->
         Rval (Boolv (tag = n /\ LENGTH xs = l),s) |
           (closLang_BlockOp (closLang_EqualConst p),[x1]) ->
         (match p with Int i -> (match x1 with Number j -> Rval
           (Boolv (i = j),s) | _165 -> ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | W64 i -> (match x1
           with Word64 j -> Rval (Boolv (i = j),s) | _166 -> ((Rerr
           (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | closLang_Str i ->
           (match x1 with RefPtr _167 p ->
                        (match lookup p (dataSem_state_refs s) with
                          SOME (ByteArray T j) ->
                           Rval (Boolv (j = MAP (n2w o ORD) (explode
                             i)),s) | _168 -> ((Rerr (Rabort
                             Rtype_error)):(dataSem_v#('c
                             ,'ffi)dataSem_state
                             ,dataSem_v)semanticPrimitives_result)) |
                             _169 -> ((Rerr (Rabort
                             Rtype_error)):(dataSem_v#('c
                             ,'ffi)dataSem_state
                             ,dataSem_v)semanticPrimitives_result)) |
                             _170 -> ((Rerr (Rabort
                             Rtype_error)):(dataSem_v#('c
                             ,'ffi)dataSem_state
                             ,dataSem_v)semanticPrimitives_result)) |
                             (closLang_BlockOp closLang_Equal,[x1; x2])
                             ->
         (match do_eq (dataSem_state_refs s) x1 x2 with Eq_val b ->
           Rval (Boolv b,s) | _171 -> ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_Ref,xs) ->
         (let ptr = (LEAST (\ptr. ~(ptr IN domain (dataSem_state_refs
           s)))) in
           Rval (RefPtr T ptr,dataSem_state_refs_fupd (K (insert ptr
             (ValueArray xs) (dataSem_state_refs s))) s)) |
             (closLang_MemOp closLang_Update,[RefPtr _172 ptr; Number i;
             x]) ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (ValueArray xs) ->
             (if (&0) <= i /\ i < &(LENGTH xs) then Rval
               (Unit,dataSem_state_refs_fupd (K (insert ptr
                              (ValueArray (LUPDATE x (num_of_int i)
                                xs)) (dataSem_state_refs s))) s) else
                                ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                _173 -> ((Rerr (Rabort
                                Rtype_error)):(dataSem_v#('c
                                ,'ffi)dataSem_state
                                ,dataSem_v)semanticPrimitives_result)) |
                                (closLang_MemOp (closLang_MutCons tag
                                i),xs) ->
         (let ptr = (LEAST (\ptr. ~(ptr IN domain (dataSem_state_refs
           s)))) in
            if i >= LENGTH xs then ((Rerr (Rabort
              Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
              ,dataSem_v)semanticPrimitives_result) else
              let l = TAKE i xs in
              let c = EL i xs in
              let r = DROP (i + 1) xs in
                Rval (RefPtr F ptr,dataSem_state_refs_fupd (K (insert
                  ptr (bvlSem_MutBlock tag F l c r) (dataSem_state_refs
                  s)))
                      s)) | (closLang_MemOp
                        closLang_UpdateCons,[RefPtr _174 ptr; Number i;
                        x]) ->
         (match lookup ptr (dataSem_state_refs s) with SOME
           (bvlSem_MutBlock tag finalised l c r) ->
              (if ~(i = &(LENGTH l)) \/ finalised then ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                ,dataSem_v)semanticPrimitives_result) else
                Rval (Unit,dataSem_state_refs_fupd (K (insert ptr
                  (bvlSem_MutBlock tag F l x r) (dataSem_state_refs s)))
                  s)) | _175 -> ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                  ,dataSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp closLang_FinaliseCons,[x]) ->
         (match dataSem_finalise_cons x (dataSem_state_refs s)
           (dataSem_state_tstamps s) with SOME (v,refs',ts') ->
              Rval (v,dataSem_state_tstamps_fupd (K ts')
                (dataSem_state_refs_fupd (K refs') s)) | NONE -> ((Rerr
                (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                ,dataSem_v)semanticPrimitives_result)) | (closLang_IntOp
                intop,vs) ->
         (match do_int_app intop vs with SOME res -> Rval (res,s) |
           _176 -> ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (closLang_WordOp
           wordop,vs) ->
         (match do_word_app wordop vs with SOME res -> Rval (res,s) |
           _177 -> ((Rerr (Rabort
           Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
           ,dataSem_v)semanticPrimitives_result)) | (FFI n,[RefPtr _178
           cptr; RefPtr _179 ptr]) ->
         (match (lookup cptr (dataSem_state_refs s),lookup ptr
           (dataSem_state_refs s)) with (SOME (ByteArray T cws),SOME
           (ByteArray F ws)) ->
            (match call_FFI (dataSem_state_ffi s) (ffi_ExtCall n) cws
              ws with FFI_return ffi' ws' ->
                 Rval (Unit,dataSem_state_ffi_fupd (K ffi')
                   (dataSem_state_refs_fupd (K (insert ptr (ByteArray F
                   ws') (dataSem_state_refs s)))
                       s)) | FFI_final outcome ->
                 Rerr (Rabort (Rffi_error outcome))) | _180 -> ((Rerr
                   (Rabort
                   Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                   ,dataSem_v)semanticPrimitives_result)) |
                   (closLang_BlockOp closLang_BoundsCheckBlock,xs) ->
         (match xs with [Block _181 tag ys; Number i] ->
                Rval (Boolv ((&0) <= i /\ i < &(LENGTH ys)),s) | _182
                  -> ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                  ,dataSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp (closLang_BoundsCheckByte loose),xs)
                  ->
         (match xs with [RefPtr _183 ptr; Number i] ->
           (match lookup ptr (dataSem_state_refs s) with SOME
             (ByteArray _184 ws) ->
                Rval (Boolv ((&0) <= i /\ (if loose then (<=) else
                  (<)) i (&(LENGTH ws))),s) | _185 -> ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                  ,dataSem_v)semanticPrimitives_result)) | _186 ->
                  ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                  ,dataSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp closLang_BoundsCheckArray,xs) ->
         (match xs with [RefPtr _187 ptr; Number i] ->
           (match lookup ptr (dataSem_state_refs s) with SOME
             (ValueArray ws) ->
                Rval (Boolv ((&0) <= i /\ i < &(LENGTH ws)),s) | _188
                  -> ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                  ,dataSem_v)semanticPrimitives_result)) | _189 ->
                  ((Rerr (Rabort
                  Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                  ,dataSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp ConfigGC,[Number _190; Number _191])
                  -> (Rval (Unit,s)) | (ThunkOp th_op,vs) ->
         (match (th_op,vs) with (AllocThunk m,[v]) ->
              (if bad_thunk_update m v (dataSem_state_refs s) then
                ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                ,dataSem_v)semanticPrimitives_result) else
               let ptr = (LEAST (\ptr. ~(ptr IN domain
                 (dataSem_state_refs s)))) in
                 Rval (RefPtr F ptr,dataSem_state_refs_fupd (K
                   (insert ptr (Thunk m v) (dataSem_state_refs s)))
                       s)) | (UpdateThunk m,[RefPtr F ptr; v]) ->
              (if bad_thunk_update m v (dataSem_state_refs s) then
                ((Rerr (Rabort
                Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                ,dataSem_v)semanticPrimitives_result) else
               match lookup ptr (dataSem_state_refs s) with SOME
                 (Thunk NotEvaluated _192) ->
                  Rval (Unit,dataSem_state_refs_fupd (K (insert
                    ptr (Thunk m v) (dataSem_state_refs s))) s) |
                    _193 -> ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                    ,dataSem_v)semanticPrimitives_result)) | _194 ->
                    ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                    ,dataSem_v)semanticPrimitives_result)) | _195 ->
                    ((Rerr (Rabort
                    Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
                    ,dataSem_v)semanticPrimitives_result))`;;
hol4_overload "do_app_aux" "dataSem_do_app_aux";;

(* HOL4 dataSemScript.sml:1149-1156: the overload do_app_safe, which
   the port expands *)

(* HOL4 dataSemScript.sml:1158-1162: the overload do_app_peak, which
   the port expands *)

let dataSem_do_app_def = cake_define
  `dataSem_do_app op vs (s:('c,'ffi)dataSem_state) =
     (if op = Install then do_install vs
       (dataSem_state_stack_frame_sizes_fupd (K LN)
       (dataSem_state_stack_max_fupd (K NONE) s)) else
     if MEM op [closLang_IntOp Greater; closLang_IntOp
       closLang_GreaterEq] then ((Rerr (Rabort
       Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
       ,dataSem_v)semanticPrimitives_result) else
     match do_space op vs s with NONE -> ((Rerr (Rabort
       Rtype_error)):(dataSem_v#('c,'ffi)dataSem_state
       ,dataSem_v)semanticPrimitives_result) | SOME s1 ->
       dataSem_do_app_aux op vs (do_stack op vs (do_lim_safe s1 op
       vs)))`;;
hol4_overload "do_app" "dataSem_do_app";;

let dataSem_get_var_def = cake_define
  `dataSem_get_var v = sptree_lookup v`;;
hol4_overload "get_var" "dataSem_get_var";;

let get_vars_def = cake_define_list
  [`dataSem_get_vars [] s = SOME []`;
   `dataSem_get_vars (v :: vs) s =
         (match get_var v s with NONE -> NONE | SOME x ->
           (match dataSem_get_vars vs s with NONE -> NONE | SOME xs
           -> SOME (x :: xs)))`];;
hol4_overload "get_vars" "dataSem_get_vars";;

let set_var_def = cake_define
  `dataSem_set_var v x s = (dataSem_state_locals_fupd (K (insert v x
  (dataSem_state_locals s))) s)`;;
hol4_overload "set_var" "dataSem_set_var";;

let dataSem_dec_clock_def = cake_define
  `dataSem_dec_clock s = state_clock_fupd (K (state_clock s - 1)) s`;;
hol4_overload "dec_clock" "dataSem_dec_clock";;

let dataSem_fix_clock_def = cake_define
  `dataSem_fix_clock s (res,s1) = (res,state_clock_fupd (K (MIN
  (state_clock s) (state_clock s1))) s1)`;;
hol4_overload "fix_clock" "dataSem_fix_clock";;

(* fix_clock_IMP[local] *)
let dataSem_fix_clock_IMP = prove
 (`fix_clock s x = (res,s1) ==> state_clock s1 <= state_clock s`,
  CHEAT_TAC);;

(* LESS_EQ_dec_clock[local] *)
let dataSem_LESS_EQ_dec_clock = prove
 (`state_clock
     r <= state_clock (dec_clock s) ==> state_clock r <=
       state_clock s`,
  CHEAT_TAC);;

let flush_state_def = cake_define_list
  [`dataSem_flush_state T (s:('c,'ffi)dataSem_state) =
  dataSem_state_locals_size_fupd (K (SOME 0)) (stack_fupd (K [])
  (dataSem_state_locals_fupd (K LN) s))`;
   `dataSem_flush_state F (s:('c,'ffi)dataSem_state) =
  dataSem_state_locals_size_fupd (K (SOME 0))
  (dataSem_state_locals_fupd (K LN) s)`];;
hol4_overload "flush_state" "dataSem_flush_state";;

let call_env_def = cake_define
  `dataSem_call_env args size' (s:('c,'ffi)dataSem_state) =
     (let new_stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max s)
                              (OPTION_MAP2 (+) (size_of_stack
                                (dataSem_state_stack s)) size') in let
         stack_safe = the F (OPTION_MAP ((>) (limits_stack_limit
           (dataSem_state_limits s))) new_stack_max) in
           dataSem_state_safe_for_space_fupd (K
           (dataSem_state_safe_for_space s /\ stack_safe))
           (dataSem_state_stack_max_fupd (K new_stack_max)
           (dataSem_state_locals_size_fupd (K size')
           (dataSem_state_locals_fupd (K (fromList args))
       s))))`;;
hol4_overload "call_env" "dataSem_call_env";;

let push_env_def = cake_define_list
  [`dataSem_push_env env F (s:('c,'ffi)dataSem_state) =
        (let stack' = Env (dataSem_state_locals_size s) env :: stack
          s in let
            stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max s)
              (size_of_stack stack') in let
            stack_safe = the F (OPTION_MAP ((>)
              (limits_stack_limit (dataSem_state_limits s)))
              stack_max) in dataSem_state_safe_for_space_fupd (K
              (dataSem_state_safe_for_space s /\ stack_safe))
              (dataSem_state_stack_max_fupd (K stack_max) (stack_fupd
              (K stack') s)))`;
   `dataSem_push_env env T (s:('c,'ffi)dataSem_state) =
       (let stack' = dataSem_Exc (dataSem_state_locals_size s) env
         (dataSem_state_handler s) :: stack s in let
           stack_max = OPTION_MAP2 MAX (dataSem_state_stack_max s)
             (size_of_stack stack') in let
           stack_safe = the F (OPTION_MAP ((>)
             (limits_stack_limit (dataSem_state_limits s)))
             stack_max) in dataSem_state_safe_for_space_fupd (K
             (dataSem_state_safe_for_space s /\ stack_safe))
             (dataSem_state_handler_fupd (K (LENGTH (stack s)))
             (dataSem_state_stack_max_fupd (K stack_max)
             (stack_fupd (K stack') s))))`];;
hol4_overload "push_env" "dataSem_push_env";;

let pop_env_def = cake_define
  `dataSem_pop_env (s:('c,'ffi)dataSem_state) =
     (match dataSem_state_stack s with (Env ss e :: xs) ->
         SOME (dataSem_state_locals_size_fupd (K ss)
           (dataSem_state_stack_fupd (K xs) (dataSem_state_locals_fupd
           (K e) s))) | (dataSem_Exc ss e n :: xs) ->
         SOME (dataSem_state_handler_fupd (K n)
           (dataSem_state_locals_size_fupd (K ss)
           (dataSem_state_stack_fupd (K xs)
           (dataSem_state_locals_fupd (K e) s)))) | _196 -> NONE)`;;
hol4_overload "pop_env" "dataSem_pop_env";;

let jump_exc_def = cake_define
  `dataSem_jump_exc (s:('c,'ffi)dataSem_state) =
     (if dataSem_state_handler s < LENGTH (dataSem_state_stack s)
       then
       match LASTN (dataSem_state_handler s + 1) (dataSem_state_stack
         s) with dataSem_Exc ss e n :: xs ->
           SOME (dataSem_state_locals_size_fupd (K ss)
             (dataSem_state_stack_fupd (K xs)
             (dataSem_state_locals_fupd (K e)
             (dataSem_state_handler_fupd (K n) s)))) | _197 -> NONE
             else NONE)`;;
hol4_overload "jump_exc" "dataSem_jump_exc";;

let cut_env_def = cake_define
  `dataSem_cut_env (name_set:1 spt) env =
     (if domain name_set SUBSET domain env then SOME (mk_wf (inter
       env name_set)) else NONE)`;;
hol4_overload "cut_env" "dataSem_cut_env";;

let cut_state_def = cake_define
  `dataSem_cut_state names (s:('c,'ffi)dataSem_state) =
     (match dataSem_cut_env names (dataSem_state_locals s) with
       NONE -> NONE | SOME env -> SOME (dataSem_state_locals_fupd (K
       env) s))`;;
hol4_overload "cut_state" "dataSem_cut_state";;

let cut_state_opt_def = cake_define
  `dataSem_cut_state_opt names s =
     (match names with NONE -> SOME s | SOME names ->
       dataSem_cut_state names s)`;;
hol4_overload "cut_state_opt" "dataSem_cut_state_opt";;

(* [local] *)
let pop_env_clock = prove
 (`(dataSem_pop_env s = SOME s1) ==> (state_clock s1 = state_clock s)`,
  CHEAT_TAC);;

(* [local] *)
let push_env_clock = prove
 (`state_clock
     (dataSem_push_env env b s) = state_clock s`,
  CHEAT_TAC);;

let dataSem_find_code_def = cake_define_list
  [`dataSem_find_code (SOME p) args code ssize =
         (match sptree_lookup p code with NONE -> NONE | SOME
           (arity,exp) ->
            (if LENGTH args = arity then SOME (args,exp,lookup p
              ssize) else NONE))`;
   `dataSem_find_code NONE args code ssize =
         (if args = [] then NONE else
           match LAST args with CodePtr loc ->
               (match sptree_lookup loc code with NONE -> NONE |
                 SOME (arity,exp) ->
                   (if LENGTH args = arity + 1 then SOME (FRONT
                     args,exp,lookup loc ssize) else NONE)) | other
                     -> NONE)`];;
hol4_overload "find_code" "dataSem_find_code";;

let isBool_def = cake_define
  `isBool b x2 =
      match x2 with
        (Block _199 tag []:dataSem_v) -> (bool_to_tag b = tag)
      | _200 -> F`;;

let install_sfs_def = cake_define
  `install_sfs op (s:('c,'ffi)dataSem_state) =
  dataSem_state_safe_for_space_fupd (K (~(op = closLang_Install) /\
  dataSem_state_safe_for_space s)) s`;;

let set_vars_def = cake_define
  `dataSem_set_vars ns vs s = (dataSem_state_locals_fupd (K (union
  (fromAList (ZIP ns vs)) (dataSem_state_locals s))) s)`;;
hol4_overload "set_vars" "dataSem_set_vars";;

let dataSem_fix_clock_IMP =
  try prove
   (`!s x res s1. dataSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; dataSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "dataSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "dataSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\ndataSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl dataSem_fix_clock_IMP <> `T` then
  cake_term_facts := dataSem_fix_clock_IMP :: (!cake_term_facts);;

let _ = size_thms "dataLang_prog";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 dataSemScript.sml:1486-1495: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let dataSem_evaluate_def = cake_define_list_try_tac (fun () ->
  `(inv_image (MEASURE I LEX MEASURE dataLang_prog_size)
                              (\(xs,s). (state_clock s,xs)))`)
  CHEAT_TAC
  [`dataSem_evaluate
  ((Skip:dataLang_prog),(s:('c,'ffi)dataSem_state)) = (NONE,s)`;
   `dataSem_evaluate ((Move dest src:dataLang_prog),s) =
         (match get_var src (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME v ->
           (NONE,dataSem_set_var dest v s))`;
   `dataSem_evaluate ((Assign dest op args names_opt:dataLang_prog),s) =
         (if op_requires_names op = IS_NONE names_opt then
           (SOME (Rerr (Rabort Rtype_error)),s) else
           match dataSem_get_vars args (dataSem_state_locals s) with
             NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs ->
               (match dataSem_cut_state_opt names_opt s with NONE ->
                 (SOME (Rerr (Rabort Rtype_error)),s) | SOME s ->
                   (match do_app op xs s with Rerr e -> (SOME (Rerr
                     e),dataSem_flush_state T (install_sfs op s)) | Rval
                     (v,s) ->
                       (NONE,dataSem_set_var dest v (install_sfs
                         op s)))))`;
   `dataSem_evaluate ((Tick:dataLang_prog),s) =
         (if state_clock s = 0 then (SOME (Rerr (Rabort
           Rtimeout_error)),dataSem_flush_state T s) else
           (NONE,dec_clock s))`;
   `dataSem_evaluate (dataLang_MakeSpace k names,s) =
         (match dataSem_cut_env names (dataSem_state_locals s)
           with NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME
           env -> (NONE,add_space (dataSem_state_locals_fupd (K env)
           s) k))`;
   `dataSem_evaluate ((Raise n:dataLang_prog),s) =
         (match get_var n (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME x ->
           (match dataSem_jump_exc s with NONE -> (SOME (Rerr
             (Rabort Rtype_error)),s) | SOME s -> (SOME (Rerr (Rraise
             x)),s)))`;
   `dataSem_evaluate ((Return ns:dataLang_prog),s) =
         (match dataSem_get_vars ns (dataSem_state_locals s) with
           NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs ->
           (SOME (Rval xs),dataSem_flush_state F s))`;
   `dataSem_evaluate ((Seq c1 c2:dataLang_prog),s) =
         (let (res,s1) = fix_clock s (dataSem_evaluate (c1,s)) in
           if res = NONE then dataSem_evaluate (c2,s1) else
             (res,s1))`;
   `dataSem_evaluate ((If n c1 c2:dataLang_prog),s) =
         (match get_var n (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) |
           // no time stamp
           SOME x -> (if isBool T x then dataSem_evaluate (c1,s)
             else
                     if isBool F x then dataSem_evaluate (c2,s) else
                       (SOME (Rerr (Rabort Rtype_error)),s)))`;
   `dataSem_evaluate ((Force ret loc src:dataLang_prog),s) =
         (match get_var src (dataSem_state_locals s) with NONE ->
           (SOME (Rerr (Rabort Rtype_error)),s) | SOME thunk_v ->
           (match dest_thunk thunk_v (state_refs s) with BadRef ->
             (SOME (Rerr (Rabort Rtype_error)),s) | NotThunk -> (SOME
             (Rerr (Rabort Rtype_error)),s) | IsThunk Evaluated v ->
              (match ret with NONE -> (SOME (Rval
                [v]),dataSem_flush_state F s) | SOME (dest,names) ->
                 (match dataSem_cut_env names (dataSem_state_locals
                   s) with NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                   | SOME env -> (NONE,dataSem_set_var dest v
                   (dataSem_state_locals_fupd (K env) s)))) | IsThunk
                   NotEvaluated f ->
               (match find_code (SOME loc) [thunk_v; f] (state_code
                 s) (dataSem_state_stack_frame_sizes s) with NONE ->
                 (SOME (Rerr (Rabort Rtype_error)),s) | SOME
                 (args1,prog,ss) ->
                  (match ret with NONE ->
                      (if state_clock s = 0 then
                         (SOME (Rerr (Rabort
                           Rtimeout_error)),dataSem_state_locals_fupd (K
                           LN) (stack_fupd (K [])
                              s)) else
                         (match dataSem_evaluate
                           (prog,dataSem_call_env args1 ss (dec_clock
                           s)) with (NONE,s) -> (SOME (Rerr (Rabort
                           Rtype_error)),s) | (SOME res,s) -> (SOME
                           res,s))) | SOME (dest,names) ->
                     (match dataSem_cut_env names
                       (dataSem_state_locals s) with NONE -> (SOME (Rerr
                       (Rabort Rtype_error)),s) | SOME env ->
                          (let s1 = dataSem_call_env args1 ss
                            (dataSem_push_env env F (dec_clock s)) in
                            if state_clock s = 0 then
                              (SOME (Rerr (Rabort
                                Rtimeout_error))
                                ,dataSem_state_locals_fupd (K LN)
                                (stack_fupd (K [])
                              s1)) else
                              (match fix_clock s1 (dataSem_evaluate
                                (prog,s1)) with (SOME (Rval xs),s2) ->
                              (if LENGTH xs = 1 then
                              match dataSem_pop_env s2 with NONE ->
                                (SOME (Rerr (Rabort Rtype_error)),s2) |
                                SOME s1 -> (NONE,dataSem_set_var dest
                                (HD xs) s1) else
                              (SOME (Rerr (Rabort
                                Rtype_error)),s2)) | (NONE,s) ->
                                (SOME (Rerr (Rabort Rtype_error)),s)
                                | res -> res)))))))`;
   `dataSem_evaluate ((Call ret dest args handler:dataLang_prog),s) =
         (match dataSem_get_vars args (dataSem_state_locals s) with
           NONE -> (SOME (Rerr (Rabort Rtype_error)),s) | SOME xs ->
           (match find_code dest xs (state_code s)
             (dataSem_state_stack_frame_sizes s) with NONE -> (SOME
             (Rerr (Rabort Rtype_error)),s) | SOME (args1,prog,ss) ->
              (match ret with NONE ->
                 // tail call
                 (if handler = NONE then
                   if state_clock s = 0 then (SOME (Rerr (Rabort
                     Rtimeout_error)),
                         dataSem_flush_state T s) else
                     (match dataSem_evaluate (prog,dataSem_call_env
                       args1 ss (dec_clock s)) with (NONE,s) -> (SOME
                       (Rerr (Rabort Rtype_error)),s) | (SOME res,s) ->
                       (SOME res,s)) else (SOME (Rerr (Rabort
                       Rtype_error)),s)) | SOME (ns,names) ->
                 // returning call, returns into var n
                 (if ~(ALL_DISTINCT ns) then (SOME (Rerr (Rabort
                   Rtype_error)),s) else
                 (match dataSem_cut_env names (dataSem_state_locals
                   s) with NONE -> (SOME (Rerr (Rabort Rtype_error)),s)
                   | SOME env ->
                    (let s1 = dataSem_call_env args1 ss
                            (dataSem_push_env env (IS_SOME handler)
                              (dec_clock s)) in if state_clock s = 0
                              then (SOME (Rerr (Rabort
                              Rtimeout_error)),dataSem_state_locals_fupd
                              (K LN) (stack_fupd (K [])
                            s1)) else (match fix_clock s1
                              (dataSem_evaluate (prog,s1)) with (SOME
                              (Rval xs),s2) ->
                              (if LENGTH xs = LENGTH ns then
                              (match dataSem_pop_env s2 with NONE ->
                                (SOME (Rerr (Rabort Rtype_error)),s2) |
                                SOME s1 -> (NONE,dataSem_set_vars ns xs
                                s1)) else
                              (SOME (Rerr (Rabort Rtype_error)),s2))
                                | (SOME (Rerr (Rraise x)),s2) ->
                              (
                              // if handler is present, then handle exc
                              match handler with NONE -> (SOME
                                (Rerr (Rraise x)),s2) | SOME (n,h)
                                -> dataSem_evaluate
                                (h,dataSem_set_var n x s2)) |
                                (NONE,s) -> (SOME (Rerr (Rabort
                                Rtype_error)),s) | res ->
                                res)))))))`];;
hol4_overload "evaluate" "dataSem_evaluate";;

(* HOL4 dataSemScript.sml:1497: ML code, not ported *)

let evaluate_safe_def = cake_define
  `evaluate_safe c s = (let (x,s1) = evaluate (c,s) in
  dataSem_state_safe_for_space s1)`;;

let evaluate_peak_def = cake_define
  `evaluate_peak c s = (let (x,s1) = evaluate (c,s) in
  dataSem_state_peak_heap_length s1)`;;

(* We prove that the clock never increases. *)

(* HOL4 dataSemScript.sml:1511-1517: a theorem that HOL4 states as
   the value of an ML expression: case_eq_thms *)

let do_stack_clock = prove
 (`state_clock
      (do_stack op args s1) = state_clock s1`,
  CHEAT_TAC);;

let do_app_clock = prove
 (`(dataSem_do_app op args s1 = Rval (res,s2)) ==> state_clock s2 <=
  state_clock s1`,
  CHEAT_TAC);;

(* [local,simp] *)
let set_vars_clock = prove
 (`state_clock
     (dataSem_set_vars ns vs s) = state_clock s`,
  CHEAT_TAC);;

(* evaluate_clock *)
let dataSem_evaluate_clock = prove
 (`!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> state_clock s2 <=
  state_clock s1`,
  CHEAT_TAC);;

(* fix_clock_evaluate *)
let dataSem_fix_clock_evaluate = prove
 (`fix_clock s (evaluate (xs,s)) = evaluate (xs,s)`,
  CHEAT_TAC);;

(* Finally, we remove fix_clock from the induction and definition theorems. *)

(* HOL4 dataSemScript.sml:1583-1584: a theorem that HOL4 states as
   the value of an ML expression: evaluate_def *)

(* HOL4 dataSemScript.sml:1586-1587: a theorem that HOL4 states as
   the value of an ML expression: evaluate_ind *)

(* observational semantics *)

let dataSem_initial_state_def = cake_define
  `dataSem_initial_state ffi code coracle cc stamps lims ss k =
  mk_dataSem_state LN (SOME 0) [] (SOME 1) ss NONE 0 LN cc k code ffi
  0 (if stamps then SOME 0 else NONE) lims (if stamps then T else F)
  0 coracle`;;
hol4_overload "initial_state" "dataSem_initial_state";;

let dataSem_semantics_def = cake_define
  `dataSem_semantics init_ffi code coracle cc lims ss start' =
   (let p = Call NONE (SOME start') [] NONE in
   let init = initial_state init_ffi code coracle cc T lims ss in
     if ?k. match FST (evaluate (p,init k)) with SOME (Rerr e) -> ~(e
       = Rabort Rtimeout_error) /\ (!f. ~(e = Rabort (Rffi_error f))) |
       NONE -> T | _201 -> F then Fail else
     match some (\res.
       ?k s r outcome.
         evaluate (p,init k) = (SOME r,s) /\
         (match r with Rerr (Rabort (Rffi_error e)) -> outcome =
           ffi_FFI_outcome e | Rval _202 -> outcome = ffi_Success | _203
           -> F) /\
         res = ffi_Terminate outcome (ffi_state_io_events (state_ffi
           s))) with SOME res -> res | NONE ->
        ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (state_ffi
              (SND (evaluate (p,init k)))))) UNIV)))`;;
hol4_overload "semantics" "dataSem_semantics";;

let data_lang_safe_for_space_def = cake_define
  `data_lang_safe_for_space init_ffi code (lims:limits) (ss:num spt)
  start' =
     (!ck.
       let p = Call NONE (SOME start') [] NONE in
       let init = initial_state init_ffi code ARB ARB T lims ss in
       let (res,s) = dataSem_evaluate (p,((init
         ck):(1,'ffi)dataSem_state)) in dataSem_state_safe_for_space
         s)`;;

let compute_limits_def = cake_define
  `compute_limits len_bits a64 fpops fptops stack_heap_limit =
      mk_limits (SND stack_heap_limit) len_bits (FST
        stack_heap_limit) a64 fpops fptops`;;

(* clean up *)

(* HOL4 dataSemScript.sml:1660: ML code, not ported *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
