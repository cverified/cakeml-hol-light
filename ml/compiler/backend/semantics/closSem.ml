(* ======================================================== *)
(*  closSem: ported from HOL4's
    compiler/backend/semantics/closSemScript.sml
    A definition theory, with 30 definitions, 5 datatypes and 14
    theorems.  Needed by 36 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of closLang
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/flatLang.ml";;
needs "lib/comparison.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
(* for opw_lookup_def and others *)
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "closSem"
  ["backend_common"; "closLang"; "flatLang";
   "semanticPrimitivesProps"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["compile","backend_compile";
   "compile","bvi_let_compile";
   "compile","bvi_to_data_compile";
   "compile","bvl_const_compile";
   "compile","bvl_handle_compile";
   "compile","bvl_to_bvi_compile";
   "compile","clos_annotate_compile";
   "compile","clos_call_compile";
   "compile","clos_fvs_compile";
   "compile","clos_known_compile";
   "compile","clos_mti_compile";
   "compile","clos_to_bvl_compile";
   "compile","data_live_compile";
   "compile","data_space_compile";
   "compile","data_to_word_compile";
   "compile","flat_to_clos_compile";
   "compile","lab_to_target_compile";
   "compile","source_to_flat_compile";
   "compile","source_to_source_compile";
   "compile","stack_alloc_compile";
   "compile","stack_names_compile";
   "compile","stack_rawcall_compile";
   "compile","stack_remove_compile";
   "compile","stack_to_lab_compile";
   "compile","word_bignum_compile";
   "compile","word_to_stack_compile";
   "compile","word_to_word_compile"];;

(* differs from store_v by removing the single value Refv,
   also, adds flag to ByteArray for equality semantics *)
let closSem_ref_INDUCT,closSem_ref_RECURSION = define_datatype
  "closSem_ref = closSem_ValueArray ('a list) | closSem_ByteArray \
   (word8 list) | closSem_Thunk (thunk_mode) ('a)";;
hol4_overload "ValueArray" "closSem_ValueArray";;
hol4_overload "ByteArray" "closSem_ByteArray";;
hol4_overload "Thunk" "closSem_Thunk";;

(* --- Semantics of ClosLang --- *)

let closSem_v_INDUCT,closSem_v_RECURSION = define_datatype
  "closSem_v = closSem_Number (int) | closSem_Word64 (word64) | \
   closSem_Block (num) (closSem_v list) | closSem_ByteVector (word8 \
   list) | closSem_RefPtr (bool) (num) | closSem_Closure (num option) \
   (closSem_v list) (closSem_v list) (num) (closLang_exp) | \
   closSem_Recclosure (num option) (closSem_v list) (closSem_v list) \
   ((num#closLang_exp) list) (num)";;
hol4_overload "Number" "closSem_Number";;
hol4_overload "Word64" "closSem_Word64";;
hol4_overload "Block" "closSem_Block";;
hol4_overload "ByteVector" "closSem_ByteVector";;
hol4_overload "RefPtr" "closSem_RefPtr";;
hol4_overload "Closure" "closSem_Closure";;
hol4_overload "Recclosure" "closSem_Recclosure";;

(* HOL4 closSemScript.sml:32: the type abbreviation clos_co, which
   the port expands *)

let closSem_state_FIELDS = define_record "closSem_state"
  ["globals","(closSem_v option) list";
   "refs","(num,closSem_v closSem_ref)fmap";
   "ffi","'ffi ffi_state";
   "clock","num";
   "compile","'c->closLang_exp list#(num#num#closLang_exp) \
   list->(word8 list#word64 list#'c) option";
   "compile_oracle","num->'c#closLang_exp list#(num#num#closLang_exp) \
   list";
   "code","(num,num#closLang_exp)fmap";
   "max_app","num"];;
hol4_overload "state_globals" "closSem_state_globals";;
hol4_overload "state_globals_fupd" "closSem_state_globals_fupd";;
hol4_overload "state_refs" "closSem_state_refs";;
hol4_overload "state_refs_fupd" "closSem_state_refs_fupd";;
hol4_overload "state_ffi" "closSem_state_ffi";;
hol4_overload "state_ffi_fupd" "closSem_state_ffi_fupd";;
hol4_overload "state_clock" "closSem_state_clock";;
hol4_overload "state_clock_fupd" "closSem_state_clock_fupd";;
hol4_field_overload "compile" "closSem_state_compile";;
hol4_field_overload "compile_fupd" "closSem_state_compile_fupd";;
hol4_field_overload "compile_oracle" "closSem_state_compile_oracle";;
hol4_field_overload "compile_oracle_fupd"
  "closSem_state_compile_oracle_fupd";;
hol4_overload "state_code" "closSem_state_code";;
hol4_overload "state_code_fupd" "closSem_state_code_fupd";;

(* helper functions *)

let get_global_def = new_definition
  `get_global n globals =
     (if n < LENGTH globals then SOME (EL n globals) else NONE)`;;

let closSem_Boolv_def = new_definition
  `(closSem_Boolv b = closSem_Block (if b then true_tag else
  false_tag) [])`;;
hol4_overload "Boolv" "closSem_Boolv";;

let _ = size_thms "closSem_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
(* the clauses of do_eq_list overlap -- the last one says Eq_val F
   of the two lists that the first two have already given a value
   -- and HOL4 takes the first that matches, so the port writes
   them as a match, which takes the first arm (see ml/lib/define.ml,
   "A definition whose clauses overlap").  As a list of clauses they
   would be inconsistent. *)
let closSem_do_eq_def = define_mutual_wf
  `MEASURE (sum_measure (\(x0,x1). closSem_v_size x0 + closSem_v_size
  x1) (\(x0,x1). closSem_v_size1 x0 + closSem_v_size1 x1))`
  [`closSem_do_eq x y =
         (match x with closSem_Number i ->
             (match y with closSem_Number j -> Eq_val (i = j) | _3
               -> Eq_type_error) | Word64 v ->
             (match y with Word64 w -> Eq_val (v = w) | _4 ->
               Eq_type_error) | closSem_Block t1 xs ->
             (match y with closSem_Block t2 ys -> (if (t1 = t2) /\
               (LENGTH xs = LENGTH ys) then
                              closSem_do_eq_list xs ys else Eq_val
                                F) | _5 -> Eq_type_error) |
                                closSem_ByteVector cs ->
             (match y with closSem_ByteVector ds -> Eq_val (cs = ds)
               | _6 -> Eq_type_error) | closSem_RefPtr bi i ->
             (match y with closSem_RefPtr bj j -> (if bi /\ bj then
               Eq_val (i = j) else Eq_type_error) | _7 -> Eq_type_error)
               | _8 ->
             (match y with closSem_Number _9 -> Eq_type_error |
               Word64 _10 -> Eq_type_error | closSem_Block _11 _12 ->
               Eq_type_error | closSem_ByteVector _13 ->
               Eq_type_error | closSem_RefPtr _14 _15 ->
               Eq_type_error | _16 -> Eq_val T))`;
   `closSem_do_eq_list x1 x2 =
         match (x1,x2) with
           ([],[]) -> Eq_val T
         | ((x :: xs),(y :: ys)) ->
         (match closSem_do_eq x y with Eq_val T ->
           closSem_do_eq_list xs ys | res -> res)
         | (_1,_2) -> Eq_val F`];;
hol4_overload "do_eq" "closSem_do_eq";;
hol4_overload "do_eq_list" "closSem_do_eq_list";;

let _ = size_thms "closSem_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let closSem_v_to_list_def,closSem_v_to_list_ind = define_wf
  `MEASURE (\x0. closSem_v_size x0)`
  [`closSem_v_to_list x1 =
        match x1 with
          (closSem_Block tag []:closSem_v) ->
        (if tag = nil_tag then SOME [] else NONE)
        | (closSem_Block tag [h; bt]) ->
        (if tag = cons_tag then
          (match closSem_v_to_list bt with SOME t -> SOME (h :: t) |
            _17 -> NONE) else NONE)
        | _18 -> NONE`];;
hol4_overload "v_to_list" "closSem_v_to_list";;

let closSem_list_to_v_def,closSem_list_to_v_ind = define_rec
  [`closSem_list_to_v [] = closSem_Block nil_tag []`;
   `closSem_list_to_v (x :: xs) = closSem_Block cons_tag [x;
  closSem_list_to_v xs]`];;
hol4_overload "list_to_v" "closSem_list_to_v";;

let closSem_Unit_def = new_definition
  `closSem_Unit = closSem_Block tuple_tag []`;;
hol4_overload "Unit" "closSem_Unit";;

(* HOL4 closSemScript.sml:120-121: the overload Error, which the port
   expands *)

let v_to_bytes_def = new_definition
  `closSem_v_to_bytes lv = some (\(ns:word8 list).
                     v_to_list lv = SOME (MAP (closSem_Number o
                       (&) o w2n) ns))`;;
hol4_overload "v_to_bytes" "closSem_v_to_bytes";;

let v_to_words_def = new_definition
  `closSem_v_to_words lv = some (\ns. v_to_list lv = SOME (MAP Word64
  ns))`;;
hol4_overload "v_to_words" "closSem_v_to_words";;

(* HOL4 closSemScript.sml:132: the ML values that the definitions
   below antiquote *)

let do_install_def = new_definition
  `closSem_do_install vs (s:('c,'ffi)closSem_state) =
       (match vs with [v1; v2] ->
            (match (closSem_v_to_bytes v1,closSem_v_to_words v2) with
              (SOME bytes,SOME data) ->
                (let (cfg,progs) = closSem_state_compile_oracle s 0
                  in
                let new_oracle = misc_shift_seq 1
                  (closSem_state_compile_oracle s) in
                 (if DISJOINT (FDOM (closSem_state_code s))
                   (set_of_list (MAP FST (SND progs))) /\
                     ALL_DISTINCT (MAP FST (SND progs)) then
                  (match (closSem_state_compile s cfg progs,progs)
                    with (SOME (bytes',data',cfg'),(exps,aux)) ->
                       (if bytes = bytes' /\ data = data' /\
                          FST (new_oracle 0) = cfg' /\ ~(exps = [])
                            then
                        (let s' = closSem_state_clock_fupd (K
                          (closSem_state_clock s - 1))
                          (closSem_state_compile_oracle_fupd (K
                          new_oracle) (closSem_state_code_fupd (K
                          (closSem_state_code s |++ aux))
                           s)) in
                           if closSem_state_clock s = 0 then (Rerr
                             (Rabort Rtimeout_error),s') else (Rval
                             exps,s')) else ((Rerr (Rabort
                             Rtype_error):(closLang_exp
                             list
                             ,closSem_v)semanticPrimitives_result)
                             ,s)) | _19 -> (Rerr (Rabort
                             Rtype_error),s)) else (Rerr (Rabort
                             Rtype_error),s))) | _20 -> (Rerr (Rabort
                             Rtype_error),s)) | _21 -> (Rerr (Rabort
                             Rtype_error),s))`;;
hol4_overload "do_install" "closSem_do_install";;

let _ = size_thms "const";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closSemScript.sml:170-175: the tactic that proves the
   termination *)
let make_const_def,make_const_ind = define_shaped_wf
  "nested"
  `MEASURE const_size`
  [`make_const (ConstInt i) = closSem_Number i`;
   `make_const (ConstStr s) = closSem_ByteVector (MAP (n2w o ORD)
  (explode s))`;
   `make_const (ConstWord64 w) = Word64 w`;
   `make_const (ConstCons t cs) = closSem_Block t (MAP make_const
  cs)`];;

let do_int_app_def = new_definition
  `closSem_do_int_app x1 x2 =
      match (x1,x2) with
        ((closLang_Const n:closLang_int_op),[]) -> SOME
          (closSem_Number n)
      | ((Add),[closSem_Number n1; closSem_Number n2]) -> SOME
        (closSem_Number (n1 + n2))
      | ((Sub),[closSem_Number n1; closSem_Number n2]) -> SOME
        (closSem_Number (n1 - n2))
      | ((closLang_Mult),[closSem_Number n1; closSem_Number n2]) ->
        SOME (closSem_Number (n1 * n2))
      | ((Div),[closSem_Number n1; closSem_Number n2]) ->
       (if n2 = (&0) then NONE else SOME (closSem_Number (n1 / n2)))
      | ((Mod),[closSem_Number n1; closSem_Number n2]) ->
       (if n2 = (&0) then NONE else SOME (closSem_Number (n1 % n2)))
      | ((Less),[closSem_Number n1; closSem_Number n2]) -> SOME
        (Boolv (n1 < n2))
      | ((closLang_LessEq),[closSem_Number n1; closSem_Number n2]) ->
        SOME (Boolv (n1 <= n2))
      | ((Greater),[closSem_Number n1; closSem_Number n2]) -> SOME
        (Boolv (n1 > n2))
      | ((closLang_GreaterEq),[closSem_Number n1; closSem_Number n2])
        -> SOME (Boolv (n1 >= n2))
      | ((closLang_LessConstSmall n),[closSem_Number i]) ->
         (if (&0) <= i /\ i <= (&1000000) /\ n < 1000000 then
           SOME (Boolv (i < &n)) else NONE)
      | ((op:closLang_int_op),(vs:closSem_v list)) -> NONE`;;
hol4_overload "do_int_app" "closSem_do_int_app";;

let opw_lookup_def = define_general
  [`opw_lookup backend_common_Andw = word_and`;
   `opw_lookup backend_common_Orw = word_or`;
   `opw_lookup (Xor:opw) = word_xor`;
   `opw_lookup (Add:opw) = word_add`;
   `opw_lookup (Sub:opw) = word_sub`];;

let do_word_app_def = new_definition
  `closSem_do_word_app x1 ws =
        match (x1,ws) with
          (WordOpw ast_W8 opw,[(closSem_Number n1:closSem_v);
            closSem_Number n2]) ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (closSem_Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw ast_W64 opw),[Word64 w1; Word64 w2]) ->
           SOME (Word64 (opw_lookup opw w1 w2))
        | ((WordTest ast_W8 test),[closSem_Number n1; closSem_Number
          n2]) ->
          (if (&0) <= n1 /\ n1 < (&256) /\ (&0) <= n2 /\ n2 < (&256)
            then
             (match test with Equal -> SOME (Boolv (n1 = n2)) |
               ast_Compare cmp -> SOME (Boolv
               (semanticPrimitives_int_cmp cmp n1 n2)) | _22 -> NONE)
               else NONE)
        | ((WordShift ast_W8 sh n),[closSem_Number i]) ->
          (match some (\(w:word8). i = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (closSem_Number (&(w2n (shift_lookup sh w
            n)))))
        | ((WordShift ast_W64 sh n),[Word64 w]) ->
          SOME (Word64 (shift_lookup sh w n))
        | ((WordFromInt),[closSem_Number i]) ->
          SOME (Word64 (i2w i))
        | (WordToInt,[Word64 w]) ->
          SOME (closSem_Number (&(w2n w)))
        | ((WordFromWord T),[Word64 w]) ->
          SOME (closSem_Number (&(w2n ((w2w:word64->word8) w))))
        | ((WordFromWord F),[closSem_Number n]) ->
          (match some (\(w:word8). n = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (Word64 (w2w w)))
        | ((FP_top t_op),ws) ->
           (match ws with [Word64 w1; Word64 w2; Word64 w3] ->
                (SOME (Word64 (fp_top_comp t_op w1 w2 w3))) | _23 ->
                  NONE)
        | ((FP_bop bop),ws) ->
           (match ws with [Word64 w1; Word64 w2] -> (SOME (Word64
             (fp_bop_comp bop w1 w2))) | _24 -> NONE)
        | ((FP_uop uop),ws) ->
           (match ws with [Word64 w] -> (SOME (Word64 (fp_uop_comp
             uop w))) | _25 -> NONE)
        | ((FP_cmp cmp),ws) ->
           (match ws with [Word64 w1; Word64 w2] -> (SOME (Boolv
             (fp_cmp_comp cmp w1 w2))) | _26 -> NONE)
        | ((op:closLang_word_op),(vs:closSem_v list)) -> NONE`;;
hol4_overload "do_word_app" "closSem_do_word_app";;

let closSem_dest_thunk_ret_INDUCT,closSem_dest_thunk_ret_RECURSION =
  define_datatype
  "closSem_dest_thunk_ret = closSem_BadRef | closSem_NotThunk | \
   closSem_IsThunk (thunk_mode) (closSem_v)";;
hol4_overload "BadRef" "closSem_BadRef";;
hol4_overload "NotThunk" "closSem_NotThunk";;
hol4_overload "IsThunk" "closSem_IsThunk";;

let closSem_dest_thunk_def = new_definition
  `closSem_dest_thunk vs refs =
      match vs with
        [(closSem_RefPtr b ptr:closSem_v)] ->
     (match FLOOKUP refs ptr with NONE -> BadRef | SOME (Thunk
       Evaluated v) ->
          (if b then BadRef else IsThunk Evaluated v) | SOME (Thunk
            NotEvaluated v) ->
          (if b then BadRef else IsThunk NotEvaluated v) | SOME _27
            -> NotThunk)
      | vs -> NotThunk`;;
hol4_overload "dest_thunk" "closSem_dest_thunk";;

let store_thunk_def = new_definition
  `store_thunk ptr v refs =
     (match FLOOKUP refs ptr with SOME (Thunk NotEvaluated _28) ->
       SOME (refs |+ (ptr,v)) | _29 -> NONE)`;;

let closSem_update_thunk_def = new_definition
  `closSem_update_thunk x1 refs x3 =
      match (x1,x3) with
        ([(closSem_RefPtr F ptr:closSem_v)],[v]) ->
     (match dest_thunk [v] refs with NotThunk -> store_thunk ptr
       (Thunk Evaluated v) refs | _30 -> NONE)
      | (_31,_32) -> NONE`;;
hol4_overload "update_thunk" "closSem_update_thunk";;

let closSem_bad_thunk_update_def = new_definition
  `closSem_bad_thunk_update m v refs <=>
     m = Evaluated /\ ~(dest_thunk [v] refs = NotThunk)`;;
hol4_overload "bad_thunk_update" "closSem_bad_thunk_update";;

let closSem_do_app_def = new_definition
  `closSem_do_app (op:closLang_op) (vs:closSem_v list)
  (s:('c,'ffi)closSem_state) =
     (match (op,vs) with (closLang_GlobOp (closLang_Global
       n),([]:closSem_v list)) ->
         (match get_global n (closSem_state_globals s) with SOME
           (SOME v) -> (Rval (v,s)) | _33 -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_GlobOp
           (closLang_Global _34),[closSem_Number i]) ->
         (if i < (&0) then ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result) else
          match get_global (num_of_int i) (closSem_state_globals s)
            with SOME (SOME v) -> (Rval (v,s)) | _35 -> ((Rerr (Rabort
            Rtype_error)):(closSem_v#('c,'ffi)closSem_state
            ,closSem_v)semanticPrimitives_result)) | (closLang_GlobOp
            (closLang_SetGlobal n),[v]) ->
         (match get_global n (closSem_state_globals s) with SOME NONE
           -> Rval (closSem_Unit,closSem_state_globals_fupd (K (LUPDATE
           (SOME v) n (closSem_state_globals s)))
              s) | _36 -> ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) |
                (closLang_GlobOp closLang_AllocGlobal,[closSem_Number
                i]) ->
         (if i < (&0) then ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result) else Rval
           (closSem_Unit,closSem_state_globals_fupd (K
           (closSem_state_globals s ++ REPLICATE (num_of_int i) NONE))
           s)) | (closLang_BlockOp (closLang_Constant c),[]) -> Rval
           (make_const c,s) | (closLang_BlockOp (closLang_Cons tag),xs)
           -> Rval (closSem_Block tag xs,s) | (closLang_BlockOp
           (closLang_ConsExtend tag),closSem_Block _37 xs' ::
           closSem_Number lower :: closSem_Number len :: closSem_Number
           tot :: xs) ->
         (if lower < (&0) \/ len < (&0) \/ &(LENGTH xs') < lower +
           len \/
            tot = (&0) \/ ~(tot = &(LENGTH xs) + len) then
           ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) else
           Rval (closSem_Block tag (xs ++ TAKE (num_of_int len) (DROP
             (num_of_int lower) xs')),s)) | (closLang_BlockOp
             (closLang_ConsExtend tag),_38) -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) | (closLang_MemOp
             closLang_El,[closSem_Block tag xs; closSem_Number i]) ->
         (if (&0) <= i /\ num_of_int i < LENGTH xs then Rval (EL
           (num_of_int i) xs,s) else ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_El,[closSem_RefPtr _39 ptr; closSem_Number i]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ValueArray xs) ->
             (if (&0) <= i /\ i < &(LENGTH xs) then Rval (EL
               (num_of_int i) xs,s) else ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | _40 -> ((Rerr
               (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) |
               (closLang_BlockOp (closLang_BoolTest test),[v1; v2]) ->
         (if (~(v1 = Boolv T) /\ ~(v1 = Boolv F)) then ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result) else
          if (~(v2 = Boolv T) /\ ~(v2 = Boolv F)) then ((Rerr (Rabort
            Rtype_error)):(closSem_v#('c,'ffi)closSem_state
            ,closSem_v)semanticPrimitives_result) else
            Rval (Boolv (v1 = v2),s)) | (closLang_BlockOp
              closLang_BoolNot,[v1]) ->
         (if v1 = Boolv T then Rval (Boolv F,s) else
          if v1 = Boolv F then Rval (Boolv T,s) else ((Rerr (Rabort
            Rtype_error)):(closSem_v#('c,'ffi)closSem_state
            ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
            (closLang_ElemAt n),[closSem_Block tag xs]) ->
         (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           ListAppend,[x1; x2]) ->
         (match (v_to_list x1,v_to_list x2) with (SOME xs,SOME ys) ->
           Rval (list_to_v (xs ++ ys),s) | _41 -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           closLang_LengthBlock,[closSem_Block tag xs]) ->
         Rval (closSem_Number (&(LENGTH xs)),s) | (closLang_MemOp
           closLang_Length,[closSem_RefPtr _42 ptr]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ValueArray xs) ->
               Rval (closSem_Number (&(LENGTH xs)),s) | _43 -> ((Rerr
                 (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) |
                 (closLang_MemOp closLang_LengthByte,[closSem_RefPtr _44
                 ptr]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ByteArray xs) ->
               Rval (closSem_Number (&(LENGTH xs)),s) | _45 -> ((Rerr
                 (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) |
                 (closLang_MemOp (closLang_RefByte F),[closSem_Number i;
                 closSem_Number b]) ->
          (if (&0) <= i /\ (?(w:word8). b = &(w2n w)) then
            let ptr = (LEAST (\ptr. ~(ptr IN FDOM (closSem_state_refs
              s)))) in
              Rval (closSem_RefPtr T ptr,closSem_state_refs_fupd (K
                (closSem_state_refs s |+
                (ptr,closSem_ByteArray (REPLICATE (num_of_int i) (i2w
                  b))))) s) else ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp closLang_RefArray,[closSem_Number i;
                  v]) ->
         (if (&0) <= i then
           let ptr = (LEAST (\ptr. ~(ptr IN FDOM (closSem_state_refs
             s)))) in
             Rval (closSem_RefPtr T ptr,closSem_state_refs_fupd (K
               (closSem_state_refs s |+
               (ptr,closSem_ValueArray (REPLICATE (num_of_int i)
                 v)))) s) else ((Rerr (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) |
                 (closLang_MemOp closLang_DerefByte,[closSem_RefPtr _46
                 ptr; closSem_Number i]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ByteArray ws) ->
             (if (&0) <= i /\ i < &(LENGTH ws) then Rval
               (closSem_Number (&(w2n (EL (num_of_int i) ws))),s) else
               ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | _47 -> ((Rerr
               (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
               closLang_UpdateByte,[closSem_RefPtr _48 ptr;
               closSem_Number i; closSem_Number b]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ByteArray bs) ->
             (if (&0) <= i /\ i < &(LENGTH bs) /\ (?(w:word8). b =
               &(w2n w)) then
                Rval (closSem_Unit,closSem_state_refs_fupd (K
                  (closSem_state_refs s |+
                  (ptr,closSem_ByteArray (LUPDATE (i2w b) (num_of_int
                    i) bs)))) s) else ((Rerr (Rabort
                    Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                    ,closSem_v)semanticPrimitives_result)) | _49 ->
                    ((Rerr (Rabort
                    Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                    ,closSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp closLang_ConcatByteVec,[lv]) ->
         (match (some (\wss. v_to_list lv = SOME (MAP
           closSem_ByteVector wss))) with SOME wss -> Rval
           (closSem_ByteVector (FLAT wss),s) | _50 -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           (closLang_FromList n),[lv]) ->
         (match v_to_list lv with SOME vs -> Rval (closSem_Block n
           vs,s) | _51 -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_FromListByte,[lv]) ->
         (match some (\ns. v_to_list lv = SOME (MAP (closSem_Number o
           (&)) ns) /\ EVERY (\n. n < 256) ns) with SOME ns -> Rval
           (closSem_ByteVector (MAP n2w ns),s) | NONE -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_ToListByte,[closSem_ByteVector bs]) ->
         (Rval (list_to_v (MAP (\b. closSem_Number (&(w2n b)))
           bs),s)) | (closLang_MemOp
           closLang_LengthByteVec,[closSem_ByteVector bs]) ->
         (Rval (closSem_Number (&(LENGTH bs)),s)) | (closLang_MemOp
           closLang_DerefByteVec,[closSem_ByteVector bs; closSem_Number
           i]) ->
         (if (&0) <= i /\ i < &(LENGTH bs) then
            Rval (closSem_Number (&(w2n (EL (num_of_int i) bs))),s)
              else ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
              (closLang_CopyByte F),[closSem_ByteVector ws;
              closSem_Number srcoff; closSem_Number len; closSem_RefPtr
              _52 dst; closSem_Number dstoff]) ->
         (match FLOOKUP (closSem_state_refs s) dst with SOME
           (closSem_ByteArray ds) ->
            (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
              SOME ds -> Rval (closSem_Unit,closSem_state_refs_fupd (K
              (closSem_state_refs s |+ (dst,closSem_ByteArray ds))) s) |
              NONE -> ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | _53 -> ((Rerr
              (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
              (closLang_CopyByte F),[closSem_RefPtr _54 src;
              closSem_Number srcoff; closSem_Number len; closSem_RefPtr
              _55 dst; closSem_Number dstoff]) ->
         (match (FLOOKUP (closSem_state_refs s) src,FLOOKUP
           (closSem_state_refs s) dst) with (SOME (closSem_ByteArray
           ws),SOME (closSem_ByteArray ds)) ->
            (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
              SOME ds -> Rval (closSem_Unit,closSem_state_refs_fupd (K
              (closSem_state_refs s |+ (dst,closSem_ByteArray ds))) s) |
              NONE -> ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | _56 -> ((Rerr
              (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
              (closLang_CopyByte T),[closSem_ByteVector ws;
              closSem_Number srcoff; closSem_Number len]) ->
        (match copy_array (ws,srcoff) len NONE with SOME ds -> Rval
          (closSem_ByteVector ds,s) | _57 -> ((Rerr (Rabort
          Rtype_error)):(closSem_v#('c,'ffi)closSem_state
          ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
          (closLang_CopyByte T),[closSem_RefPtr _58 src; closSem_Number
          srcoff; closSem_Number len]) ->
        (match FLOOKUP (closSem_state_refs s) src with SOME
          (closSem_ByteArray ws) ->
           (match copy_array (ws,srcoff) len NONE with SOME ds ->
             Rval (closSem_ByteVector ds,s) | _59 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | _60 -> ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
             closLang_XorByte,[closSem_RefPtr _61 dst;
             closSem_ByteVector ws]) ->
        (match FLOOKUP (closSem_state_refs s) dst with SOME
          (closSem_ByteArray ds) ->
           (match xor_bytes ws ds with SOME ds1 -> Rval
             (closSem_Unit,closSem_state_refs_fupd (K
             (closSem_state_refs s |+ (dst,closSem_ByteArray ds1))) s) |
             _62 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | _63 -> ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
             (closLang_StringCmp b cmp),[closSem_ByteVector b1;
             closSem_ByteVector b2]) ->
        (let s1 = implode (MAP (CHR o w2n) b1) in
         let s2 = implode (MAP (CHR o w2n) b2) in
           Rval (Boolv (str_cmp b cmp s1 s2),s)) | (closLang_BlockOp
             (closLang_TagEq n),[closSem_Block tag xs]) ->
         Rval (Boolv (tag = n),s) | (closLang_BlockOp (closLang_LenEq
           l),[closSem_Block tag xs]) ->
         Rval (Boolv (LENGTH xs = l),s) | (closLang_BlockOp
           (closLang_TagLenEq n l),[closSem_Block tag xs]) ->
         Rval (Boolv (tag = n /\ LENGTH xs = l),s) |
           (closLang_BlockOp (closLang_EqualConst p),[x1]) ->
         (match p with closLang_Int i -> (match x1 with
           closSem_Number j -> Rval (Boolv (i = j),s) | _64 -> ((Rerr
           (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | W64 i -> (match x1
           with Word64 j -> Rval (Boolv (i = j),s) | _65 -> ((Rerr
           (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | closLang_Str i ->
           (match x1 with closSem_ByteVector j -> Rval (Boolv (j = MAP
           (n2w o ORD) (explode i)),s) | _66 -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | _67 -> ((Rerr
           (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           closLang_Equal,[x1; x2]) ->
         (match do_eq x1 x2 with Eq_val b -> Rval (Boolv b,s) | _68
           -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_Ref,xs) ->
         (let ptr = (LEAST (\ptr. ~(ptr IN FDOM (closSem_state_refs
           s)))) in
           Rval (closSem_RefPtr T ptr,closSem_state_refs_fupd (K
             (closSem_state_refs s |+ (ptr,closSem_ValueArray xs))) s))
             | (closLang_MemOp closLang_Update,[closSem_RefPtr _69 ptr;
             closSem_Number i; x]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ValueArray xs) ->
             (if (&0) <= i /\ i < &(LENGTH xs) then Rval
               (closSem_Unit,closSem_state_refs_fupd (K
               (closSem_state_refs s |+
                              (ptr,closSem_ValueArray (LUPDATE x
                                (num_of_int i) xs)))) s) else ((Rerr
                                (Rabort
                                Rtype_error)):(closSem_v#('c
                                ,'ffi)closSem_state
                                ,closSem_v)semanticPrimitives_result)) |
                                _70 -> ((Rerr (Rabort
                                Rtype_error)):(closSem_v#('c
                                ,'ffi)closSem_state
                                ,closSem_v)semanticPrimitives_result)) |
                                (closLang_IntOp int_op',vs) ->
         (match closSem_do_int_app int_op' vs with SOME res -> Rval
           (res,s) | _71 -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (closLang_WordOp
           word_op',vs) ->
         (match closSem_do_word_app word_op' vs with SOME res -> Rval
           (res,s) | _72 -> ((Rerr (Rabort
           Rtype_error)):(closSem_v#('c,'ffi)closSem_state
           ,closSem_v)semanticPrimitives_result)) | (FFI
           n,[closSem_ByteVector conf; closSem_RefPtr _73 ptr]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ByteArray ws) ->
            (match call_FFI (closSem_state_ffi s) (ffi_ExtCall n)
              conf ws with FFI_return ffi' ws' ->
                 Rval (closSem_Unit,closSem_state_ffi_fupd (K ffi')
                   (closSem_state_refs_fupd (K (closSem_state_refs s |+
                   (ptr,closSem_ByteArray ws')))
                       s)) | FFI_final outcome ->
                 Rerr (Rabort (Rffi_error outcome))) | _74 -> ((Rerr
                   (Rabort
                   Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                   ,closSem_v)semanticPrimitives_result)) |
                   (closLang_BlockOp
                   closLang_BoundsCheckBlock,[closSem_Block tag ys;
                   closSem_Number i]) ->
         Rval (Boolv ((&0) <= i /\ i < &(LENGTH ys)),s) |
           (closLang_MemOp (closLang_BoundsCheckByte
           loose),[closSem_ByteVector bs; closSem_Number i]) ->
         Rval (Boolv ((&0) <= i /\ (if loose then (<=) else (<)) i
           (&(LENGTH bs))),s) | (closLang_MemOp
           (closLang_BoundsCheckByte loose),[closSem_RefPtr _75 ptr;
           closSem_Number i]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ByteArray ws) ->
              Rval (Boolv ((&0) <= i /\ (if loose then (<=) else (<))
                i (&(LENGTH ws))),s) | _76 -> ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
                closLang_BoundsCheckArray,[closSem_RefPtr _77 ptr;
                closSem_Number i]) ->
         (match FLOOKUP (closSem_state_refs s) ptr with SOME
           (closSem_ValueArray ws) ->
              Rval (Boolv ((&0) <= i /\ i < &(LENGTH ws)),s) | _78 ->
                ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
                ConfigGC,[closSem_Number _79; closSem_Number _80]) ->
                (Rval (closSem_Unit,s)) | (ThunkOp th_op,vs) ->
         (match (th_op,vs) with (AllocThunk m,[v]) ->
              (if bad_thunk_update m v (closSem_state_refs s) then
                ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result) else
               let ptr = (LEAST (\ptr. ~(ptr IN FDOM
                 (closSem_state_refs s)))) in
                 Rval (closSem_RefPtr F ptr,closSem_state_refs_fupd
                   (K (closSem_state_refs s |+ (ptr,Thunk m v))) s)) |
                   (UpdateThunk m,[closSem_RefPtr F ptr; v]) ->
              (if bad_thunk_update m v (closSem_state_refs s) then
                ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result) else
               match FLOOKUP (closSem_state_refs s) ptr with SOME
                 (Thunk NotEvaluated _81) ->
                  Rval (closSem_Unit,closSem_state_refs_fupd (K
                    (closSem_state_refs s |+ (ptr,Thunk m v))) s) |
                    _82 -> ((Rerr (Rabort
                    Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                    ,closSem_v)semanticPrimitives_result)) | _83 ->
                    ((Rerr (Rabort
                    Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                    ,closSem_v)semanticPrimitives_result)) | _84 ->
                    ((Rerr (Rabort
                    Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                    ,closSem_v)semanticPrimitives_result))`;;
hol4_overload "do_app" "closSem_do_app";;

let closSem_dec_clock_def = new_definition
  `closSem_dec_clock n (s:('c,'ffi)closSem_state) =
  closSem_state_clock_fupd (K (closSem_state_clock s - n)) s`;;
hol4_overload "dec_clock" "closSem_dec_clock";;

(* [local] *)
let LESS_EQ_dec_clock = prove
 (`closSem_state_clock
     (r:('c,'ffi)closSem_state) <= state_clock (closSem_dec_clock n
       s) ==> closSem_state_clock r <= state_clock s`,
  CHEAT_TAC);;

let find_code_def = new_definition
  `closSem_find_code p args code =
     (match FLOOKUP code p with NONE -> NONE | SOME (arity,exp) ->
       (if LENGTH args = arity then SOME (args,exp) else NONE))`;;
hol4_overload "find_code" "closSem_find_code";;

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

(* Proving termination of the evaluator directly is tricky. We make
   our life simpler by forcing the clock to stay good using
   fix_clock. At the bottom of this file, we remove all occurrences
   of fix_clock. *)

let closSem_fix_clock_def = new_definition
  `closSem_fix_clock s (res,s1) = (res,state_clock_fupd (K (MIN
  (state_clock s) (state_clock s1))) s1)`;;
hol4_overload "fix_clock" "closSem_fix_clock";;

(* fix_clock_IMP[local] *)
let closSem_fix_clock_IMP = prove
 (`closSem_fix_clock s x = (res,s1) ==> state_clock s1 <= state_clock
  s`,
  CHEAT_TAC);;

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of clos_exp expressions. *)

let check_loc_def = define_cases
  [`check_loc (max_app:num) NONE loc num_params num_args so_far <=>
        num_args <= max_app`;
   `check_loc (max_app:num) (SOME p) loc num_params num_args so_far <=>
        num_params = num_args /\ so_far = (0:num) /\ SOME p =
          loc`];;

let app_kind_INDUCT,app_kind_RECURSION = define_datatype
  "app_kind = Partial_app (closSem_v) | Full_app (closLang_exp) \
   (closSem_v list) (closSem_v list)";;

let dest_closure_def = new_definition
  `dest_closure max_app loc_opt f args =
     (match f with Closure loc arg_env clo_env num_args exp ->
         (if check_loc max_app loc_opt loc num_args (LENGTH args)
           (LENGTH arg_env) /\ LENGTH arg_env < num_args then
           if ~(LENGTH args + LENGTH arg_env < num_args) then
             SOME (Full_app exp
                            (REVERSE (TAKE (num_args - LENGTH
                              arg_env) (REVERSE args)) ++
                             arg_env ++ clo_env)
                            (REVERSE (DROP (num_args - LENGTH
                              arg_env) (REVERSE args)))) else
             SOME (Partial_app (closSem_Closure loc (args ++ arg_env)
               clo_env num_args exp)) else
           NONE) | Recclosure loc arg_env clo_env fns i ->
         (let (num_args,exp) = EL i fns in
           if LENGTH fns <= i \/
              ~(check_loc max_app
                         loc_opt
                         (OPTION_MAP ((+) (2 * i)) loc) num_args
                         (LENGTH args)
                         (LENGTH arg_env)) \/
              ~(LENGTH arg_env < num_args) then NONE else
             let rs = GENLIST (Recclosure loc [] clo_env fns) (LENGTH
               fns) in
               if ~(LENGTH args + LENGTH arg_env < num_args) then
                 SOME (Full_app exp
                              (REVERSE (TAKE (num_args - LENGTH
                                arg_env) (REVERSE args)) ++
                              arg_env ++ rs ++ clo_env)
                              (REVERSE (DROP (num_args - LENGTH
                                arg_env) (REVERSE args)))) else
                 SOME (Partial_app (closSem_Recclosure loc (args
                   ++ arg_env) clo_env fns i))) | _85 -> NONE)`;;

let dest_closure_length = prove
 (`!max_app loc_opt f args exp args1 args2 so_far.
     dest_closure max_app loc_opt f args = SOME (Full_app exp args1
       args2) ==>
     LENGTH args2 < LENGTH args`,
  CHEAT_TAC);;

let clos_env_def = new_definition
  `clos_env restrict names env =
     (if restrict then lookup_vars names env else SOME env)`;;

let build_recc_def = new_definition
  `build_recc restrict loc env names fns =
     (match clos_env restrict names env with SOME env1 -> SOME
       (GENLIST (Recclosure loc [] env1 fns) (LENGTH fns)) | NONE ->
       NONE)`;;

(* HOL4 closSemScript.sml:639-649: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

let do_install_clock = prove
 (`closSem_do_install vs s = (Rval e,s') ==> 0 < state_clock s /\
  state_clock s' = state_clock s - 1`,
  CHEAT_TAC);;

let do_install_clock_less_eq = prove
 (`closSem_do_install vs s = (res,s') ==> state_clock s' <=
  state_clock s`,
  CHEAT_TAC);;

let AppUnit_def = new_definition
  `closSem_AppUnit x = closLang_App backend_common_None NONE x
  [closLang_Op backend_common_None (closLang_BlockOp (closLang_Cons
  0)) []]`;;
hol4_overload "AppUnit" "closSem_AppUnit";;

let _ = size_thms "closLang_op";;
let _ = size_thms "mlstring";;
let _ = size_thms "tra";;
let exp_alt_size_def = define_mutual_rec
  [`closSem_exp_alt_size (Var a0 a1:closLang_exp) = 1 + (tra_size a0
  + a1)`;
   `closSem_exp_alt_size (If a0 a1 a2 a3:closLang_exp) =
    1 + (tra_size a0 + (closSem_exp_alt_size a1 +
      (closSem_exp_alt_size a2 + closSem_exp_alt_size a3)))`;
   `closSem_exp_alt_size (Let a0 a1 a2:closLang_exp) =
    1 + (tra_size a0 + (closSem_exp3_alt_size a1 +
      closSem_exp_alt_size a2))`;
   `closSem_exp_alt_size (Raise a0 a1:closLang_exp) = 1 + (tra_size
  a0 + closSem_exp_alt_size a1)`;
   `closSem_exp_alt_size (Handle a0 a1 a2:closLang_exp) =
    1 + (tra_size a0 + (closSem_exp_alt_size a1 +
      closSem_exp_alt_size a2))`;
   `closSem_exp_alt_size (closLang_Tick a0 a1:closLang_exp) = 1 +
  (tra_size a0 + closSem_exp_alt_size a1)`;
   `closSem_exp_alt_size (closLang_Call a0 a1 a2 a3:closLang_exp) =
    1 + (tra_size a0 + (a1 + (a2 + closSem_exp3_alt_size a3)))`;
   `closSem_exp_alt_size (App a0 a1 a2 a3:closLang_exp) =
    1 +
    (tra_size a0 + (option_size (\x. x) a1 +
      (closSem_exp_alt_size a2 + closSem_exp3_alt_size a3)))`;
   `closSem_exp_alt_size (closLang_Fn a0 a1 a2 a3 a4) =
    1 +
    (mlstring_size a0 +
     (option_size (\x. x) a1 +
      (option_size (list_size (\x. x)) a2 + (a3 +
        closSem_exp_alt_size a4))))`;
   `closSem_exp_alt_size (Letrec a0 a1 a2 a3 a4:closLang_exp) =
    1 +
    (list_size mlstring_size a0 +
     (option_size (\x. x) a1 +
      (option_size (list_size (\x. x)) a2 +
        (closSem_exp1_alt_size a3 + closSem_exp_alt_size a4))))`;
   `closSem_exp_alt_size (closLang_Op a0 a1 a2:closLang_exp) =
      1 + (tra_size a0 + (closLang_op_size a1 +
        closSem_exp3_alt_size a2)) + (if a1 = ThunkOp ForceThunk then
        100 else 0)`;
   `closSem_exp1_alt_size [] = 0`;
   `closSem_exp1_alt_size (a0 :: a1) = 1 + (closSem_exp2_alt_size a0
  + closSem_exp1_alt_size a1)`;
   `closSem_exp2_alt_size (a0,a1) = 1 + (a0 + closSem_exp_alt_size
  a1)`;
   `closSem_exp3_alt_size [] = 0`;
   `closSem_exp3_alt_size (a0 :: a1) = 1 + (closSem_exp_alt_size a0
  + closSem_exp3_alt_size a1)`];;
hol4_overload "exp1_alt_size" "closSem_exp1_alt_size";;
hol4_overload "exp2_alt_size" "closSem_exp2_alt_size";;
hol4_overload "exp3_alt_size" "closSem_exp3_alt_size";;
hol4_overload "exp_alt_size" "closSem_exp_alt_size";;

(* [local,simp] *)
let exp3_alt_size = prove
 (`closSem_exp3_alt_size xs = list_size closSem_exp_alt_size xs`,
  CHEAT_TAC);;

let closSem_fix_clock_IMP =
  try prove
   (`!s x res s1. closSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; closSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "closSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "closSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nclosSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl closSem_fix_clock_IMP <> `T` then
  cake_term_facts := closSem_fix_clock_IMP :: (!cake_term_facts);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 closSemScript.sml:828-843: the tactic that proves the
   termination *)
let closSem_evaluate_def = define_mutual_wf
  `(inv_image (MEASURE I LEX MEASURE I LEX MEASURE I)
                   (\x. match x with INL (xs,env,s) -> (state_clock
                     s,list_size closSem_exp_alt_size xs,0) | INR
                     (l,f,args,s) -> (state_clock s,0,LENGTH args)))`
  [`closSem_evaluate ([],(env:closSem_v
  list),(s:('c,'ffi)closSem_state)) = (Rval [],s)`;
   `closSem_evaluate (x :: y :: xs,env,s) =
         (match closSem_fix_clock s (closSem_evaluate ([x],env,s))
           with (Rval v1,s1) ->
             (match closSem_evaluate (y :: xs,env,s1) with (Rval
               vs,s2) -> (Rval (HD v1 :: vs),s2) | res -> res) | res
               -> res)`;
   `closSem_evaluate ([(Var _87 n:closLang_exp)],env,s) =
         (if n < LENGTH env then (Rval [EL n env],s) else (Rerr
           (Rabort Rtype_error),s))`;
   `closSem_evaluate ([(If _89 x1 x2 x3:closLang_exp)],env,s) =
         (match closSem_fix_clock s (closSem_evaluate ([x1],env,s))
           with (Rval vs,s1) ->
              (if Boolv T = HD vs then closSem_evaluate
                ([x2],env,s1) else
              if Boolv F = HD vs then closSem_evaluate ([x3],env,s1)
                else
                (Rerr (Rabort Rtype_error),s1)) | res -> res)`;
   `closSem_evaluate ([(Let _91 xs x2:closLang_exp)],env,s) =
         (match closSem_fix_clock s (closSem_evaluate (xs,env,s))
           with (Rval vs,s1) -> closSem_evaluate ([x2],vs ++ env,s1)
           | res -> res)`;
   `closSem_evaluate ([(Raise _93 x1:closLang_exp)],env,s) =
         (match closSem_evaluate ([x1],env,s) with (Rval vs,s) ->
           (Rerr (Rraise (HD vs)),s) | res -> res)`;
   `closSem_evaluate ([(Handle _95 x1 x2:closLang_exp)],env,s1) =
         (match closSem_fix_clock s1 (closSem_evaluate
           ([x1],env,s1)) with (Rerr (Rraise v),s) ->
           closSem_evaluate ([x2],v :: env,s) | res -> res)`;
   `closSem_evaluate ([(closLang_Op _97 op xs:closLang_exp)],env,s) =
         (match closSem_fix_clock s (closSem_evaluate (xs,env,s))
           with (Rval vs,s) ->
           (if op = closLang_Install then
           (match closSem_do_install (REVERSE vs) s with (Rval es,s)
             ->
                (match closSem_evaluate (es,[],s) with (Rval vs,s)
                  -> (Rval [LAST vs],s) | res -> res) | (Rerr err,s) ->
                  (Rerr err,s)) else if op = ThunkOp ForceThunk then
             (match dest_thunk vs (state_refs s) with BadRef ->
               (Rerr (Rabort Rtype_error),s) | NotThunk -> (Rerr (Rabort
               Rtype_error),s) | IsThunk Evaluated v -> (Rval [v],s) |
               IsThunk NotEvaluated f ->
                 (match closSem_evaluate ([closSem_AppUnit (Var
                   backend_common_None 0)],[f],s) with (Rval vs2,s) ->
                     (match update_thunk vs (state_refs s) vs2 with
                       NONE -> (Rerr (Rabort Rtype_error),s) | SOME refs
                       -> (Rval vs2,state_refs_fupd (K refs) s)) | (Rerr
                       e,s) -> (Rerr e,s))) else
           (match do_app op (REVERSE vs) s with Rerr err -> (Rerr
             err,s) | Rval (v,s) -> (Rval [v],s))) | res -> res)`;
   `closSem_evaluate ([closLang_Fn _98 loc vsopt num_args exp],env,s) =
         (if num_args <= closSem_state_max_app s /\ ~(num_args = 0)
           then
           match vsopt with NONE -> (Rval [Closure loc [] env
             num_args exp],s) | SOME vs ->
               (match lookup_vars vs env with NONE -> (Rerr (Rabort
                 Rtype_error),s) | SOME env' -> (Rval [Closure loc []
                 env' num_args exp],s)) else
           (Rerr (Rabort Rtype_error),s))`;
   `closSem_evaluate ([(Letrec _100 loc namesopt fns
  exp:closLang_exp)],env,s) =
         (if EVERY (\(num_args,e). num_args <= closSem_state_max_app
           s /\ ~(num_args = 0)) fns then
           let
             build_rc = (\e. GENLIST (Recclosure loc [] e fns)
               (LENGTH fns)) in
           let
             envdelta =
               (match namesopt with NONE -> SOME (build_rc env) |
                 SOME names -> OPTION_MAP build_rc (lookup_vars names
                 env)) in
             match envdelta with
                 NONE -> (Rerr (Rabort Rtype_error),s) | SOME ed ->
                   closSem_evaluate ([exp],ed ++ env,s) else
           (Rerr (Rabort Rtype_error),s))`;
   `closSem_evaluate ([(App _102 loc_opt x1 args:closLang_exp)],env,s) =
         (if LENGTH args > 0 then
           (match closSem_fix_clock s (closSem_evaluate
             (args,env,s)) with (Rval y2,s1) ->
              (match closSem_fix_clock s1 (closSem_evaluate
                ([x1],env,s1)) with (Rval y1,s2) -> evaluate_app loc_opt
                (HD y1) y2 s2 | res -> res) | res -> res) else
           (Rerr (Rabort Rtype_error),s))`;
   `closSem_evaluate ([(closLang_Tick _104 x:closLang_exp)],env,s) =
         (if state_clock s = 0 then (Rerr (Rabort
           Rtimeout_error),s) else closSem_evaluate
           ([x],env,closSem_dec_clock 1 s))`;
   `closSem_evaluate ([(closLang_Call _106 ticks dest
  xs:closLang_exp)],env,s1) =
         (match closSem_fix_clock s1 (closSem_evaluate (xs,env,s1))
           with (Rval vs,s) ->
             (match closSem_find_code dest vs (closSem_state_code s)
               with NONE -> (Rerr (Rabort Rtype_error),s) | SOME
               (args,exp) ->
                  (if (state_clock s < ticks + 1) then (Rerr (Rabort
                    Rtimeout_error),state_clock_fupd (K 0) s) else
                      closSem_evaluate
                        ([exp],args,closSem_dec_clock (ticks + 1)
                        s))) | res -> res)`;
   `evaluate_app loc_opt f [] (s:('c,'ffi)closSem_state) = (Rval
  [f],s)`;
   `evaluate_app loc_opt f args (s:('c,'ffi)closSem_state) =
         (match dest_closure (closSem_state_max_app s) loc_opt f
           args with NONE -> (Rerr (Rabort Rtype_error),s) | SOME
           (Partial_app v) ->
             (if state_clock s < LENGTH args then (Rerr (Rabort
               Rtimeout_error),state_clock_fupd (K 0) s) else (Rval
               [v],closSem_dec_clock (LENGTH args) s)) | SOME (Full_app
               exp env rest_args) ->
             (if state_clock s < (LENGTH args - LENGTH rest_args)
               then (Rerr (Rabort Rtimeout_error),state_clock_fupd (K 0)
               s) else
                 match closSem_fix_clock (closSem_dec_clock (LENGTH
                   args - LENGTH rest_args) s)
                        (closSem_evaluate
                          ([exp],env,closSem_dec_clock (LENGTH args -
                          LENGTH rest_args) s)) with (Rval [v],s1) ->
                   evaluate_app loc_opt v rest_args s1 | res ->
                     res))`];;
hol4_overload "evaluate" "closSem_evaluate";;

(* HOL4 closSemScript.sml:845-846: a theorem that HOL4 states as the
   value of an ML expression: evaluate_app_NIL *)

(* We prove that the clock never increases. *)

let do_app_const = prove
 (`(do_app op args s1 = Rval (res,s2)) ==>
    (state_clock s2 = state_clock s1) /\
    (closSem_state_max_app s2 = closSem_state_max_app s1) /\
    (closSem_state_code s2 = closSem_state_code s1) /\
    (closSem_state_compile_oracle s2 = closSem_state_compile_oracle
      s1) /\
    (closSem_state_compile s2 = closSem_state_compile s1)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_clock_help = prove
 (`(!tup vs (s2:('c,'ffi)closSem_state).
       (closSem_evaluate tup = (vs,s2)) ==> closSem_state_clock s2 <=
         state_clock (SND (SND tup))) /\
     (!loc_opt f args (s1:('c,'ffi)closSem_state) vs s2.
       (evaluate_app loc_opt f args s1 = (vs,s2)) ==>
         closSem_state_clock s2 <= closSem_state_clock s1)`,
  CHEAT_TAC);;

(* evaluate_clock *)
let closSem_evaluate_clock = prove
 (`(!xs env s1 vs s2.
        (closSem_evaluate (xs,env,s1) = (vs,s2)) ==> state_clock s2
          <= state_clock s1) /\
      (!loc_opt f args s1 vs s2.
        (evaluate_app loc_opt f args s1 = (vs,s2)) ==> state_clock
          s2 <= state_clock s1)`,
  CHEAT_TAC);;

(* fix_clock_evaluate *)
let closSem_fix_clock_evaluate = prove
 (`closSem_fix_clock s (closSem_evaluate (xs,env,s)) =
  closSem_evaluate (xs,env,s)`,
  CHEAT_TAC);;

(* Finally, we remove fix_clock from the induction and definition theorems. *)

(* HOL4 closSemScript.sml:900-901: a theorem that HOL4 states as the
   value of an ML expression: evaluate_def *)

(* HOL4 closSemScript.sml:903-904: a theorem that HOL4 states as the
   value of an ML expression: evaluate_ind *)

(* observational semantics *)

let initial_state_def = new_definition
  `closSem_initial_state ffi ma code co cc k = mk_closSem_state []
  FEMPTY ffi k cc co code ma`;;
hol4_overload "initial_state" "closSem_initial_state";;

let semantics_def = new_definition
  `closSem_semantics ffi ma code co cc es =
     (let st = closSem_initial_state ffi ma code co cc in
       if ?k. FST (closSem_evaluate (es,[],st k)) = Rerr (Rabort
         Rtype_error) then ffi_Fail else
       match some (\res.
         ?k r s outcome.
           closSem_evaluate (es,[],st k) = (r,s) /\
           (match r with Rerr (Rabort Rtimeout_error) -> F | Rerr
             (Rabort (Rffi_error e)) -> outcome = ffi_FFI_outcome e |
             _107 -> outcome = ffi_Success) /\
           res = ffi_Terminate outcome (ffi_state_io_events
             (state_ffi s))) with SOME res -> res | NONE ->
          ffi_Diverge
            (build_lprefix_lub
              (IMAGE (\k. fromList (ffi_state_io_events (state_ffi
                 (SND (closSem_evaluate (es,[],st k)))))) UNIV)))`;;
hol4_overload "semantics" "closSem_semantics";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
