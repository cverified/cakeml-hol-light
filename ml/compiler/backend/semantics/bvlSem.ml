(* ======================================================== *)
(*  bvlSem: ported from HOL4's
    compiler/backend/semantics/bvlSemScript.sml
    A definition theory, with 23 definitions, 4 datatypes and 10
    theorems.  Needed by 11 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of BVL
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
(* for closure_tag and num_added_globals *)
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvlSem"
  ["backendProps"; "bvl"; "closSem"; "clos_to_bvl"];;

let _ = do_list hide_constant ["str"];;

(* --- Semantics of BVL --- *)

let bvlSem_ref_INDUCT,bvlSem_ref_RECURSION = define_datatype
  "bvlSem_ref =
     bvlSem_ValueArray ('a list)
   | bvlSem_ByteArray bool (word8 list)
     // T = compare-by-contents, immutable
     // F = compare-by-pointer, mutable
     // in closLang all are ByteArray F,
     // ByteArray T introduced in BVL to implement ByteVector
   | bvlSem_Thunk thunk_mode ('a)
   | bvlSem_MutBlock num bool ('a list) ('a) ('a list)";;

(* these parts are shared by bytecode and, if bytecode is to be supported, need
   to move to a common ancestor *)

let bvlSem_v_INDUCT,bvlSem_v_RECURSION = define_datatype
  "bvlSem_v =
     bvlSem_Number int
     // integer
   | bvlSem_Word64 word64
     // 64-bit word
   | bvlSem_Block num (bvlSem_v list)
     // cons block: tag and payload
   | bvlSem_CodePtr num
     // code pointer
   | bvlSem_RefPtr bool num
     // pointer to ref cell, bool is T if Eq test is allows
  ";;

let bvlSem_Boolv_def = new_definition
  `bvlSem_Boolv b = bvlSem_Block (bool_to_tag b) []`;;

let bvlSem_Unit_def = new_definition
  `bvlSem_Unit = bvlSem_Block (tuple_tag) []`;;

(* -- *)

let bvlSem_state_FIELDS = define_record "bvlSem_state"
  ["globals","(bvlSem_v option) list";
   "refs","(num,bvlSem_v bvlSem_ref)fmap";
   "clock","num";
   "compile","'c->(num#num#bvl_exp) list->(word8 list#word64 list#'c) \
   option";
   "compile_oracle","num->'c#(num#num#bvl_exp) list";
   "code","(num#bvl_exp) spt";
   "ffi","'ffi ffi_state"];;

let _ = size_thms "bvlSem_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let bvlSem_v_to_list_def,bvlSem_v_to_list_ind = define_wf
  `MEASURE (\x0. bvlSem_v_size x0)`
  [`bvlSem_v_to_list x1 =
        match x1 with
          (bvlSem_Block tag []:bvlSem_v) ->
        (if tag = nil_tag then SOME [] else NONE)
        | (bvlSem_Block tag [h; bt]) ->
        (if tag = cons_tag then
          (match bvlSem_v_to_list bt with SOME t -> SOME (CONS h t)
            | _1 -> NONE) else NONE)
        | _2 -> NONE`];;

let bvlSem_list_to_v_def,bvlSem_list_to_v_ind = define_rec
  [`bvlSem_list_to_v [] = bvlSem_Block nil_tag []`;
   `bvlSem_list_to_v (CONS v vs) = bvlSem_Block cons_tag [v;
    bvlSem_list_to_v vs]`];;

let isClos_def = new_definition
  `bvlSem_isClos t1 l1 = (((t1 = closure_tag) \/ (t1 =
  partial_app_tag)) /\ ~(l1 = []))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
(* the clauses of the source overlap -- a later one says
   Eq_type_error of a pair that an earlier one has already given a
   value -- and HOL4 takes the first that matches, so the port
   writes them as a match, which takes the first arm (see
   ml/lib/define.ml, "A definition whose clauses overlap").  As a
   list of clauses they would be inconsistent. *)
let bvlSem_do_eq_def,bvlSem_do_eq_ind = define_wf
  `MEASURE (sum_measure (\(x0,x1,x2). (\x. 0) x0 + bvlSem_v_size x1 +
  bvlSem_v_size x2) (\(x0,x1,x2). (\x. 0) x0 + bvlSem_v_size1 x1 +
  bvlSem_v_size1 x2))`
  [`bvlSem_do_eq refs x2 x3 =
         match (x2,x3) with
           ((bvlSem_CodePtr _4:bvlSem_v),_5) -> Eq_type_error
         | (_6,(bvlSem_CodePtr _7)) -> Eq_type_error
         | ((bvlSem_Number n1),(bvlSem_Number n2)) -> (Eq_val (n1 =
             n2))
         | ((bvlSem_Number _8),_9) -> Eq_type_error
         | (_10,(bvlSem_Number _11)) -> Eq_type_error
         | ((bvlSem_Word64 w1),(bvlSem_Word64 w2)) -> (Eq_val (w1 =
             w2))
         | ((bvlSem_Word64 _12),_13) -> Eq_type_error
         | (_14,(bvlSem_Word64 _15)) -> Eq_type_error
         | ((bvlSem_RefPtr b1 n1),(bvlSem_RefPtr b2 n2)) ->
        (if b1 /\ b2 then
         (match (FLOOKUP refs n1,FLOOKUP refs n2) with
            (SOME (bvlSem_ByteArray T bs1),SOME (bvlSem_ByteArray T
                bs2)) -> Eq_val (bs1 = bs2) | (SOME (bvlSem_ByteArray T
                bs1),_16) -> Eq_type_error | (_17,SOME (bvlSem_ByteArray
                T bs2)) -> Eq_type_error | _18 -> Eq_val (n1 = n2)) else
                Eq_type_error)
         | ((bvlSem_RefPtr _19 _20),_21) -> Eq_type_error
         | (_22,(bvlSem_RefPtr _23 _24)) -> Eq_type_error
         | ((bvlSem_Block t1 l1),(bvlSem_Block t2 l2)) ->
       (if bvlSem_isClos t1 l1 \/ bvlSem_isClos t2 l2 then if
           bvlSem_isClos t1 l1 /\ bvlSem_isClos t2 l2 then Eq_val T
           else Eq_type_error else if (t1 = t2) /\ (LENGTH l1 =
           LENGTH l2) then bvlSem_do_eq_list refs l1 l2 else Eq_val
           F)`;
   `bvlSem_do_eq_list refs x2 x3 =
         match (x2,x3) with
           ([],[]) -> Eq_val T
         | ((CONS v1 vs1),(CONS v2 vs2)) ->
       (match bvlSem_do_eq refs v1 v2 with Eq_val T ->
           bvlSem_do_eq_list refs vs1 vs2 | Eq_val F -> Eq_val F | bad
           -> bad)
         | (_25,_26) -> Eq_val F`];;
add_simp bvlSem_do_eq_def;;

(* HOL4 bvlSemScript.sml:116: the overload Error, which the port
   expands *)

let bvlSem_v_to_bytes_def = new_definition
  `bvlSem_v_to_bytes lv = some (\(ns:word8 list).
                     bvlSem_v_to_list lv = SOME (MAP
                       (bvlSem_Number o (&) o w2n) ns))`;;

let bvlSem_v_to_words_def = new_definition
  `bvlSem_v_to_words lv = some (\ns. bvlSem_v_to_list lv = SOME (MAP
  bvlSem_Word64 ns))`;;

(* HOL4 bvlSemScript.sml:127: the ML values that the definitions
   below antiquote *)

let bvlSem_do_install_def = new_definition
  `bvlSem_do_install vs (s:('c,'ffi)bvlSem_state) =
       (match vs with [v1; v2] ->
            (match (bvlSem_v_to_bytes v1,bvlSem_v_to_words v2) with
              (SOME bytes,SOME data) ->
                (let (cfg,progs) = bvlSem_state_compile_oracle s 0 in
                let new_oracle = misc_shift_seq 1
                  (bvlSem_state_compile_oracle s) in
                 (if DISJOINT (domain (bvlSem_state_code s))
                   (set_of_list (MAP FST progs)) /\
                     ALL_DISTINCT (MAP FST progs) then
                  (match (bvlSem_state_compile s cfg progs,progs)
                    with (SOME (bytes',data',cfg'),CONS (k,prog) _27) ->
                       (if bytes = bytes' /\ data = data' /\ FST
                         (new_oracle 0) = cfg' then
                         let s' = bvlSem_state_compile_oracle_fupd (K
                           new_oracle) (bvlSem_state_code_fupd (K
                           (sptree_union (bvlSem_state_code s)
                           (fromAList progs)))
                           s) in
                           Rval (bvlSem_CodePtr k,s') else Rerr
                             (Rabort Rtype_error)) | _28 -> Rerr
                             (Rabort Rtype_error)) else Rerr (Rabort
                             Rtype_error))) | _29 -> Rerr (Rabort
                             Rtype_error)) | _30 -> Rerr (Rabort
                             Rtype_error))`;;

let do_part_def = define_cases
  [`bvlSem_do_part m (closLang_Int i:const_part) refs =
    (bvlSem_Number i,refs)`;
   `bvlSem_do_part m (closLang_W64 w:const_part) refs =
    (bvlSem_Word64 w,refs)`;
   `bvlSem_do_part m (closLang_Con t ns:const_part) refs =
    (bvlSem_Block t (MAP m ns),refs)`;
   `bvlSem_do_part m (closLang_Str t:const_part) refs =
      (let ptr = (minimal ptr. ~(ptr IN FDOM refs)) in
      let bytes = MAP (n2w o ORD) (explode t) in
        (bvlSem_RefPtr T ptr,refs |+ (ptr,((bvlSem_ByteArray T
            bytes):bvlSem_v bvlSem_ref))))`];;

let do_build_def,do_build_ind = define_rec
  [`bvlSem_do_build m i [] refs = (m (i - 1),refs)`;
   `bvlSem_do_build m i (CONS p rest) refs =
      (let (x,refs1) = bvlSem_do_part m p refs in
        bvlSem_do_build ((i =+ x) m) (i + 1) rest refs1)`];;

let do_build_const_def = new_definition
  `bvlSem_do_build_const xs refs = bvlSem_do_build (\x. bvlSem_Number
  (&0)) 0 xs refs`;;
(* same as closSem$do_int_app *)
let bvlSem_do_int_app_def = new_definition
  `bvlSem_do_int_app x1 x2 =
      match (x1,x2) with
        ((closLang_Const n:closLang_int_op),[]) -> SOME
          (bvlSem_Number n)
      | ((closLang_Add),[bvlSem_Number n1; bvlSem_Number n2]) -> SOME
        (bvlSem_Number (n1 + n2))
      | ((closLang_Sub),[bvlSem_Number n1; bvlSem_Number n2]) -> SOME
        (bvlSem_Number (n1 - n2))
      | ((closLang_Mult),[bvlSem_Number n1; bvlSem_Number n2]) ->
        SOME (bvlSem_Number (n1 * n2))
      | ((closLang_Div),[bvlSem_Number n1; bvlSem_Number n2]) ->
       (if n2 = (&0) then NONE else SOME (bvlSem_Number (n1 / n2)))
      | ((closLang_Mod),[bvlSem_Number n1; bvlSem_Number n2]) ->
       (if n2 = (&0) then NONE else SOME (bvlSem_Number (n1 % n2)))
      | ((closLang_Less),[bvlSem_Number n1; bvlSem_Number n2]) ->
        SOME (bvlSem_Boolv (n1 < n2))
      | ((closLang_LessEq),[bvlSem_Number n1; bvlSem_Number n2]) ->
        SOME (bvlSem_Boolv (n1 <= n2))
      | ((closLang_Greater),[bvlSem_Number n1; bvlSem_Number n2]) ->
        SOME (bvlSem_Boolv (n1 > n2))
      | ((closLang_GreaterEq),[bvlSem_Number n1; bvlSem_Number n2])
        -> SOME (bvlSem_Boolv (n1 >= n2))
      | ((closLang_LessConstSmall n),[bvlSem_Number i]) ->
         (if (&0) <= i /\ i <= (&1000000) /\ n < 1000000 then
           SOME (bvlSem_Boolv (i < &n)) else NONE)
      | ((op:closLang_int_op),(vs:bvlSem_v list)) -> NONE`;;

let do_int_app_eq_some = prove
 (`(!n. bvlSem_do_int_app (closLang_Const n) vs = SOME res ==>
     vs = [] /\ res = bvlSem_Number n) /\
   (bvlSem_do_int_app (closLang_Add) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ res =
       bvlSem_Number (n1 + n2))) /\
   (bvlSem_do_int_app (closLang_Sub) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ res =
       bvlSem_Number (n1 - n2))) /\
   (bvlSem_do_int_app (closLang_Mult) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ res =
       bvlSem_Number (n1 * n2))) /\
   (bvlSem_do_int_app (closLang_Div) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ ~(n2 =
       (&0)) /\ res = bvlSem_Number (n1 / n2))) /\
   (bvlSem_do_int_app (closLang_Mod) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ ~(n2 =
       (&0)) /\ res = bvlSem_Number (n1 % n2))) /\
   (bvlSem_do_int_app (closLang_Less) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ res =
       bvlSem_Boolv (n1 < n2))) /\
   (bvlSem_do_int_app (closLang_LessEq) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ res =
       bvlSem_Boolv (n1 <= n2))) /\
   (bvlSem_do_int_app (closLang_Greater) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ res =
       bvlSem_Boolv (n1 > n2))) /\
   (bvlSem_do_int_app (closLang_GreaterEq) vs = SOME res ==>
     (?n1 n2. vs = [bvlSem_Number n1; bvlSem_Number n2] /\ res =
       bvlSem_Boolv (n1 >= n2))) /\
   (!n. bvlSem_do_int_app (closLang_LessConstSmall n) vs = SOME res
     ==>
     (?i. vs = [bvlSem_Number i] /\ (&0) <= i /\ i <= (&1000000) /\
       n < 1000000 /\ res = bvlSem_Boolv (i < &n)))`,
  CHEAT_TAC);;

(* same as closSem$do_word_app *)
let bvlSem_do_word_app_def = new_definition
  `bvlSem_do_word_app x1 ws =
        match (x1,ws) with
          (WordOpw ast_W8 opw,[(bvlSem_Number n1:bvlSem_v);
            bvlSem_Number n2]) ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (bvlSem_Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw ast_W64 opw),[bvlSem_Word64 w1; bvlSem_Word64
          w2]) ->
           SOME (bvlSem_Word64 (opw_lookup opw w1 w2))
        | ((WordTest ast_W8 test),[bvlSem_Number n1; bvlSem_Number
          n2]) ->
          (if (&0) <= n1 /\ n1 < (&256) /\ (&0) <= n2 /\ n2 < (&256)
            then
             (match test with ast_Equal -> SOME (bvlSem_Boolv (n1 =
               n2)) | ast_Compare cmp -> SOME (bvlSem_Boolv
               (semanticPrimitives_int_cmp cmp n1 n2)) | _31 -> NONE)
               else NONE)
        | ((WordShift ast_W8 sh n),[bvlSem_Number i]) ->
          (match some (\(w:word8). i = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (bvlSem_Number (&(w2n (shift_lookup sh w
            n)))))
        | ((WordShift ast_W64 sh n),[bvlSem_Word64 w]) ->
          SOME (bvlSem_Word64 (shift_lookup sh w n))
        | ((WordFromInt),[bvlSem_Number i]) ->
          SOME (bvlSem_Word64 (i2w i))
        | (WordToInt,[bvlSem_Word64 w]) ->
          SOME (bvlSem_Number (&(w2n w)))
        | ((WordFromWord T),[bvlSem_Word64 w]) ->
          SOME (bvlSem_Number (&(w2n ((w2w:word64->word8) w))))
        | ((WordFromWord F),[bvlSem_Number n]) ->
          (match some (\(w:word8). n = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (bvlSem_Word64 (w2w w)))
        | ((FP_top t_op),ws) ->
           (match ws with [bvlSem_Word64 w1; bvlSem_Word64 w2;
             bvlSem_Word64 w3] ->
                (SOME (bvlSem_Word64 (fp_top_comp t_op w1 w2 w3))) |
                  _32 -> NONE)
        | ((FP_bop bop),ws) ->
           (match ws with [bvlSem_Word64 w1; bvlSem_Word64 w2] ->
             (SOME (bvlSem_Word64 (fp_bop_comp bop w1 w2))) | _33 ->
             NONE)
        | ((FP_uop uop),ws) ->
           (match ws with [bvlSem_Word64 w] -> (SOME (bvlSem_Word64
             (fp_uop_comp uop w))) | _34 -> NONE)
        | ((FP_cmp cmp),ws) ->
           (match ws with [bvlSem_Word64 w1; bvlSem_Word64 w2] ->
             (SOME (bvlSem_Boolv (fp_cmp_comp cmp w1 w2))) | _35 ->
             NONE)
        | ((op:closLang_word_op),(vs:bvlSem_v list)) -> NONE`;;

let bvlSem_dest_thunk_ret_INDUCT,bvlSem_dest_thunk_ret_RECURSION =
  define_datatype
  "bvlSem_dest_thunk_ret =
     bvlSem_BadRef
   | bvlSem_NotThunk
   | bvlSem_IsThunk thunk_mode bvlSem_v";;

let bvlSem_dest_thunk_def = new_definition
  `bvlSem_dest_thunk x1 refs =
      match x1 with
        (bvlSem_RefPtr b ptr:bvlSem_v) ->
     (match FLOOKUP refs ptr with NONE -> bvlSem_BadRef | SOME
       (bvlSem_Thunk Evaluated v) ->
          (if b then bvlSem_BadRef else bvlSem_IsThunk Evaluated v) |
            SOME (bvlSem_Thunk NotEvaluated v) ->
          (if b then bvlSem_BadRef else bvlSem_IsThunk NotEvaluated
            v) | SOME _36 -> bvlSem_NotThunk)
      | _37 -> bvlSem_NotThunk`;;

let bvlSem_bad_thunk_update_def = new_definition
  `bvlSem_bad_thunk_update m v refs <=>
     m = Evaluated /\ ~(bvlSem_dest_thunk v refs =
       bvlSem_NotThunk)`;;

(* same as closSem$do_app, except:
    - LengthByteVec and DerefByteVec are removed
    - FromListByte, ToListByte, String, ConcatByteVec, and
      CopyByte work on ByteArrays rather than ByteVectors
    - Build now has full semantics, i.e. can handle all cases
    - Label is added *)

let bvlSem_do_app_def = new_definition
  `bvlSem_do_app op vs (s:('c,'ffi)bvlSem_state) =
     (match (op,vs) with (closLang_GlobOp (closLang_Global n),[]) ->
         (match get_global n (bvlSem_state_globals s) with SOME (SOME
           v) -> Rval (v,s) | _38 -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_GlobOp
           (closLang_Global _39),[bvlSem_Number i]) ->
         (if i < (&0) then ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result) else
          match get_global (num_of_int i + num_added_globals)
            (bvlSem_state_globals s) with SOME (SOME v) -> Rval (v,s) |
            _40 -> ((Rerr (Rabort
            Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
            ,bvlSem_v)semanticPrimitives_result)) | (closLang_GlobOp
            (closLang_SetGlobal n),[v]) ->
         (match get_global n (bvlSem_state_globals s) with SOME _41
           -> Rval (bvlSem_Unit,bvlSem_state_globals_fupd (K (LUPDATE
           (SOME v) n (bvlSem_state_globals s)))
              s) | _42 -> ((Rerr (Rabort
                Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                ,bvlSem_v)semanticPrimitives_result)) | (closLang_GlobOp
                closLang_AllocGlobal,[bvlSem_Number i]) ->
         (if i < (&0) then ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result) else Rval
           (bvlSem_Unit,bvlSem_state_globals_fupd (K (APPEND
           (bvlSem_state_globals s) (REPLICATE (num_of_int i) NONE)))
           s)) | (closLang_Install,vs) -> bvlSem_do_install vs s |
           (closLang_BlockOp (closLang_Cons tag),xs) -> Rval
           (bvlSem_Block tag xs,s) | (closLang_BlockOp
           (closLang_BoolTest test),[v1; v2]) ->
         (if (~(v1 = bvlSem_Boolv T) /\ ~(v1 = bvlSem_Boolv F)) then
           ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result) else
          if (~(v2 = bvlSem_Boolv T) /\ ~(v2 = bvlSem_Boolv F)) then
            ((Rerr (Rabort
            Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
            ,bvlSem_v)semanticPrimitives_result) else
            Rval (bvlSem_Boolv (v1 = v2),s)) | (closLang_BlockOp
              closLang_BoolNot,[v1]) ->
         (if v1 = bvlSem_Boolv T then Rval (bvlSem_Boolv F,s) else
          if v1 = bvlSem_Boolv F then Rval (bvlSem_Boolv T,s) else
            ((Rerr (Rabort
            Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
            ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
            (closLang_Build parts'),[]) ->
         (let (v,rs) = bvlSem_do_build_const parts'
           (bvlSem_state_refs s) in Rval (v,bvlSem_state_refs_fupd (K
           rs) s)) | (closLang_BlockOp (closLang_ConsExtend tag),CONS
           (bvlSem_Block _43 xs') (CONS (bvlSem_Number lower) (CONS
           (bvlSem_Number len) (CONS (bvlSem_Number tot) xs)))) ->
         (if lower < (&0) \/ len < (&0) \/ lower + len > &(LENGTH
           xs') \/
            tot = (&0) \/ ~(tot = &(LENGTH xs) + len) then
           ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result) else
           Rval (bvlSem_Block tag (APPEND xs (TAKE (num_of_int len)
             (DROP (num_of_int lower) xs'))),s)) | (closLang_BlockOp
             (closLang_ConsExtend tag),_44) -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result) | (closLang_MemOp
             closLang_El,[bvlSem_Block tag xs; bvlSem_Number i]) ->
         (if (&0) <= i /\ num_of_int i < LENGTH xs then Rval (EL
           (num_of_int i) xs,s) else ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_El,[bvlSem_RefPtr _45 ptr; bvlSem_Number i]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ValueArray xs) ->
             (if (&0) <= i /\ i < &(LENGTH xs) then Rval (EL
               (num_of_int i) xs,s) else ((Rerr (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result)) | _46 -> ((Rerr
               (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
               (closLang_ElemAt n),[bvlSem_Block tag xs]) ->
         (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           (closLang_ElemAt n),[bvlSem_RefPtr _47 ptr]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ValueArray xs) ->
             (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
               (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result)) | _48 -> ((Rerr
               (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
               closLang_ListAppend,[x1; x2]) ->
         (match (bvlSem_v_to_list x1,bvlSem_v_to_list x2) with (SOME
           xs,SOME ys) -> Rval (bvlSem_list_to_v (APPEND xs ys),s) | _49
           -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
           closLang_LengthBlock,[bvlSem_Block tag xs]) ->
         Rval (bvlSem_Number (&(LENGTH xs)),s) | (closLang_MemOp
           closLang_Length,[bvlSem_RefPtr _50 ptr]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ValueArray xs) ->
               Rval (bvlSem_Number (&(LENGTH xs)),s) | _51 -> ((Rerr
                 (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                 closLang_LengthByte,[bvlSem_RefPtr _52 ptr]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ByteArray _53 xs) ->
               Rval (bvlSem_Number (&(LENGTH xs)),s) | _54 -> ((Rerr
                 (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                 (closLang_RefByte F),[bvlSem_Number i; bvlSem_Number
                 b]) ->
          (if (&0) <= i /\ (?(w:word8). b = &(w2n w)) then
            let ptr = (minimal ptr. ~(ptr IN FDOM (bvlSem_state_refs
              s))) in
              Rval (bvlSem_RefPtr T ptr,bvlSem_state_refs_fupd (K
                (bvlSem_state_refs s |+
                (ptr,bvlSem_ByteArray F (REPLICATE (num_of_int i)
                  (i2w b))))) s) else ((Rerr (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp closLang_RefArray,[bvlSem_Number i;
                  v]) ->
         (if (&0) <= i then
           let ptr = (minimal ptr. ~(ptr IN FDOM (bvlSem_state_refs
             s))) in
             Rval (bvlSem_RefPtr T ptr,bvlSem_state_refs_fupd (K
               (bvlSem_state_refs s |+
               (ptr,bvlSem_ValueArray (REPLICATE (num_of_int i) v))))
                 s) else ((Rerr (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                 closLang_DerefByte,[bvlSem_RefPtr _55 ptr;
                 bvlSem_Number i]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ByteArray _56 ws) ->
             (if (&0) <= i /\ i < &(LENGTH ws) then Rval
               (bvlSem_Number (&(w2n (EL (num_of_int i) ws))),s) else
               ((Rerr (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result)) | _57 -> ((Rerr
               (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
               closLang_UpdateByte,[bvlSem_RefPtr _58 ptr; bvlSem_Number
               i; bvlSem_Number b]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ByteArray f bs) ->
             (if (&0) <= i /\ i < &(LENGTH bs) /\ (?(w:word8). b =
               &(w2n w)) then
                Rval (bvlSem_Unit,bvlSem_state_refs_fupd (K
                  (bvlSem_state_refs s |+
                  (ptr,bvlSem_ByteArray f (LUPDATE (i2w b)
                    (num_of_int i) bs)))) s) else ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) | _59 ->
                    ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp closLang_ConcatByteVec,[lv]) ->
          (match
             (some (\wss. ?ps.
               bvlSem_v_to_list lv = SOME (MAP (bvlSem_RefPtr T) ps)
                 /\
               MAP (FLOOKUP (bvlSem_state_refs s)) ps = MAP (SOME o
                 closSem_ByteArray T) wss)) with SOME wss ->
             (let ptr = (minimal ptr. ~(ptr IN FDOM
               (bvlSem_state_refs s))) in
               Rval (bvlSem_RefPtr T ptr,bvlSem_state_refs_fupd (K
                 (bvlSem_state_refs s |+
                        (ptr,bvlSem_ByteArray T (FLAT wss)))) s)) |
                          _60 -> ((Rerr (Rabort
                          Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                          ,bvlSem_v)semanticPrimitives_result)) |
                          (closLang_BlockOp (closLang_FromList n),[lv])
                          ->
         (match bvlSem_v_to_list lv with SOME vs -> Rval
           (bvlSem_Block n vs,s) | _61 -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_FromListByte,[lv]) ->
         (match some (\ns. bvlSem_v_to_list lv = SOME (MAP
           (bvlSem_Number o (&)) ns) /\ ALL (\n. n < 256) ns) with SOME
           ns -> (let ptr = (minimal ptr. ~(ptr IN FDOM
           (bvlSem_state_refs s))) in
                          Rval (bvlSem_RefPtr T
                            ptr,bvlSem_state_refs_fupd (K
                            (bvlSem_state_refs s |+
                            (ptr,bvlSem_ByteArray T (MAP n2w ns))))
                              s)) | NONE -> ((Rerr (Rabort
                              Rtype_error)):(bvlSem_v#('c
                              ,'ffi)bvlSem_state
                              ,bvlSem_v)semanticPrimitives_result)) |
                              (closLang_MemOp
                              closLang_ToListByte,[bvlSem_RefPtr _62
                              ptr]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ByteArray f bs) ->
             (Rval (bvlSem_list_to_v (MAP (\b. bvlSem_Number (&(w2n
               b))) bs),s)) | _63 -> ((Rerr (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
               (closLang_CopyByte F),[bvlSem_RefPtr _64 src;
               bvlSem_Number srcoff; bvlSem_Number len; bvlSem_RefPtr
               _65 dst; bvlSem_Number dstoff]) ->
         (match (FLOOKUP (bvlSem_state_refs s) src,FLOOKUP
           (bvlSem_state_refs s) dst) with (SOME (bvlSem_ByteArray _66
           ws),SOME (bvlSem_ByteArray fl ds)) ->
            (match copy_array (ws,srcoff) len (SOME (ds,dstoff)) with
              SOME ds -> Rval (bvlSem_Unit,bvlSem_state_refs_fupd (K
              (bvlSem_state_refs s |+ (dst,bvlSem_ByteArray fl ds))) s)
              | NONE -> ((Rerr (Rabort
              Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
              ,bvlSem_v)semanticPrimitives_result)) | _67 -> ((Rerr
              (Rabort
              Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
              ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
              (closLang_CopyByte T),[bvlSem_RefPtr _68 src;
              bvlSem_Number srcoff; bvlSem_Number len]) ->
        (match (FLOOKUP (bvlSem_state_refs s) src) with SOME
          (bvlSem_ByteArray _69 ws) ->
            (match copy_array (ws,srcoff) len NONE with SOME ds ->
               (let ptr = (minimal ptr. ~(ptr IN FDOM
                 (bvlSem_state_refs s))) in
               Rval (bvlSem_RefPtr T ptr,bvlSem_state_refs_fupd (K
                 (bvlSem_state_refs s |+ (ptr,bvlSem_ByteArray T ds)))
                 s)) | _70 -> ((Rerr (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | _71 -> ((Rerr
                 (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                 closLang_XorByte,[bvlSem_RefPtr _72 dst; bvlSem_RefPtr
                 _73 src]) ->
         (match (FLOOKUP (bvlSem_state_refs s) src,FLOOKUP
           (bvlSem_state_refs s) dst) with (SOME (bvlSem_ByteArray _74
           ws),SOME (bvlSem_ByteArray fl ds)) ->
            (match xor_bytes ws ds with SOME ds1 -> Rval
              (bvlSem_Unit,bvlSem_state_refs_fupd (K (bvlSem_state_refs
              s |+ (dst,bvlSem_ByteArray fl ds1))) s) | NONE -> ((Rerr
              (Rabort
              Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
              ,bvlSem_v)semanticPrimitives_result)) | _75 -> ((Rerr
              (Rabort
              Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
              ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
              (closLang_StringCmp b cmp),[bvlSem_RefPtr _76 s1;
              bvlSem_RefPtr _77 s2]) ->
         (match (FLOOKUP (bvlSem_state_refs s) s1,FLOOKUP
           (bvlSem_state_refs s) s2) with (SOME (bvlSem_ByteArray _78
           ws1),SOME (bvlSem_ByteArray _79 ws2)) ->
              (let s1 = implode (MAP (CHR o w2n) ws1) in
               let s2 = implode (MAP (CHR o w2n) ws2) in
                 Rval (bvlSem_Boolv (str_cmp b cmp s1 s2),s)) | _80
                   -> ((Rerr (Rabort
                   Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                   ,bvlSem_v)semanticPrimitives_result)) |
                   (closLang_BlockOp (closLang_TagEq n),[bvlSem_Block
                   tag xs]) ->
         Rval (bvlSem_Boolv (tag = n),s) | (closLang_BlockOp
           (closLang_LenEq l),[bvlSem_Block tag xs]) ->
         Rval (bvlSem_Boolv (LENGTH xs = l),s) | (closLang_BlockOp
           (closLang_TagLenEq n l),[bvlSem_Block tag xs]) ->
         Rval (bvlSem_Boolv (tag = n /\ LENGTH xs = l),s) |
           (closLang_BlockOp (closLang_EqualConst p),[x1]) ->
         (match p with closLang_Int i -> (match x1 with bvlSem_Number
           j -> Rval (bvlSem_Boolv (i = j),s) | _81 -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | closLang_W64 i ->
           (match x1 with bvlSem_Word64 j -> Rval (bvlSem_Boolv (i =
           j),s) | _82 -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | closLang_Str i ->
           (match x1 with bvlSem_RefPtr _83 p ->
                        (match FLOOKUP (bvlSem_state_refs s) p with
                          SOME (bvlSem_ByteArray T j) ->
                           Rval (bvlSem_Boolv (j = MAP (n2w o ORD)
                             (explode i)),s) | _84 -> ((Rerr (Rabort
                             Rtype_error)):(bvlSem_v#('c
                             ,'ffi)bvlSem_state
                             ,bvlSem_v)semanticPrimitives_result)) | _85
                             -> ((Rerr (Rabort
                             Rtype_error)):(bvlSem_v#('c
                             ,'ffi)bvlSem_state
                             ,bvlSem_v)semanticPrimitives_result)) | _86
                             -> ((Rerr (Rabort
                             Rtype_error)):(bvlSem_v#('c
                             ,'ffi)bvlSem_state
                             ,bvlSem_v)semanticPrimitives_result)) |
                             (closLang_BlockOp closLang_Equal,[x1; x2])
                             ->
         (match bvlSem_do_eq (bvlSem_state_refs s) x1 x2 with Eq_val
           b -> Rval (bvlSem_Boolv b,s) | _87 -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
           closLang_Ref,xs) ->
         (let ptr = (minimal ptr. ~(ptr IN FDOM (bvlSem_state_refs
           s))) in
           Rval (bvlSem_RefPtr T ptr,bvlSem_state_refs_fupd (K
             (bvlSem_state_refs s |+ (ptr,bvlSem_ValueArray xs))) s)) |
             (closLang_MemOp closLang_Update,[bvlSem_RefPtr _88 ptr;
             bvlSem_Number i; x]) ->
         (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
           (bvlSem_ValueArray xs) ->
             (if (&0) <= i /\ i < &(LENGTH xs) then Rval
               (bvlSem_Unit,bvlSem_state_refs_fupd (K (bvlSem_state_refs
               s |+
                              (ptr,bvlSem_ValueArray (LUPDATE x
                                (num_of_int i) xs)))) s) else ((Rerr
                                (Rabort
                                Rtype_error)):(bvlSem_v#('c
                                ,'ffi)bvlSem_state
                                ,bvlSem_v)semanticPrimitives_result)) |
                                _89 -> ((Rerr (Rabort
                                Rtype_error)):(bvlSem_v#('c
                                ,'ffi)bvlSem_state
                                ,bvlSem_v)semanticPrimitives_result)) |
                                (closLang_Label n,[]) ->
         (if n IN domain (bvlSem_state_code s) then Rval
           (bvlSem_CodePtr n,s) else ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_IntOp
           intop,vs) ->
         (match bvlSem_do_int_app intop vs with SOME res -> Rval
           (res,s) | _90 -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_WordOp
           wordop,vs) ->
         (match bvlSem_do_word_app wordop vs with SOME res -> Rval
           (res,s) | _91 -> ((Rerr (Rabort
           Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
           ,bvlSem_v)semanticPrimitives_result)) | (closLang_FFI
           n,[bvlSem_RefPtr _92 cptr; bvlSem_RefPtr _93 ptr]) ->
         (match (FLOOKUP (bvlSem_state_refs s) cptr,FLOOKUP
           (bvlSem_state_refs s) ptr) with (SOME (bvlSem_ByteArray T
           cws),SOME (bvlSem_ByteArray F ws)) ->
            (match call_FFI (bvlSem_state_ffi s) (ffi_ExtCall n) cws
              ws with FFI_return ffi' ws' ->
                 Rval (bvlSem_Unit,bvlSem_state_ffi_fupd (K ffi')
                   (bvlSem_state_refs_fupd (K (bvlSem_state_refs s |+
                   (ptr,bvlSem_ByteArray F ws')))
                       s)) | FFI_final outcome ->
                 Rerr (Rabort (Rffi_error outcome))) | _94 -> ((Rerr
                   (Rabort
                   Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                   ,bvlSem_v)semanticPrimitives_result)) |
                   (closLang_BlockOp closLang_BoundsCheckBlock,xs) ->
         (match xs with [bvlSem_Block tag ys; bvlSem_Number i] ->
                Rval (bvlSem_Boolv ((&0) <= i /\ i < &(LENGTH ys)),s)
                  | _95 -> ((Rerr (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp (closLang_BoundsCheckByte loose),xs)
                  ->
         (match xs with [bvlSem_RefPtr _96 ptr; bvlSem_Number i] ->
           (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
             (bvlSem_ByteArray _97 ws) ->
                Rval (bvlSem_Boolv ((&0) <= i /\ (if loose then (<=)
                  else (<)) i (&(LENGTH ws))),s) | _98 -> ((Rerr (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result)) | _99 -> ((Rerr
                  (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp closLang_BoundsCheckArray,xs) ->
         (match xs with [bvlSem_RefPtr _100 ptr; bvlSem_Number i] ->
           (match FLOOKUP (bvlSem_state_refs s) ptr with SOME
             (bvlSem_ValueArray ws) ->
                Rval (bvlSem_Boolv ((&0) <= i /\ i < &(LENGTH ws)),s)
                  | _101 -> ((Rerr (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result)) | _102 -> ((Rerr
                  (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp closLang_ConfigGC,[bvlSem_Number _103;
                  bvlSem_Number _104]) -> (Rval (bvlSem_Unit,s)) |
                  (closLang_ThunkOp th_op,vs) ->
         (match (th_op,vs) with (AllocThunk m,[v]) ->
              (if bvlSem_bad_thunk_update m v (bvlSem_state_refs s)
                then ((Rerr (Rabort
                Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                ,bvlSem_v)semanticPrimitives_result) else
               let ptr = (minimal ptr. ~(ptr IN FDOM
                 (bvlSem_state_refs s))) in
                 Rval (bvlSem_RefPtr F ptr,bvlSem_state_refs_fupd (K
                   (bvlSem_state_refs s |+ (ptr,bvlSem_Thunk m v))) s))
                   | (UpdateThunk m,[bvlSem_RefPtr F ptr; v]) ->
              (if bvlSem_bad_thunk_update m v (bvlSem_state_refs s)
                then ((Rerr (Rabort
                Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                ,bvlSem_v)semanticPrimitives_result) else
               match FLOOKUP (bvlSem_state_refs s) ptr with SOME
                 (bvlSem_Thunk NotEvaluated _105) ->
                  Rval (bvlSem_Unit,bvlSem_state_refs_fupd (K
                    (bvlSem_state_refs s |+ (ptr,bvlSem_Thunk m v)))
                    s) | _106 -> ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) | _107 ->
                    ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) | _108 ->
                    ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result))`;;

let bvlSem_dec_clock_def = new_definition
  `bvlSem_dec_clock n s = bvlSem_state_clock_fupd (K
  (bvlSem_state_clock s - n)) s`;;

(* Functions for looking up function definitions *)

let bvlSem_find_code_def = define_cases
  [`bvlSem_find_code (SOME p) args code =
         (match sptree_lookup p code with NONE -> NONE | SOME
             (arity,exp) -> (if LENGTH args = arity then SOME
             (args,exp) else NONE))`;
   `bvlSem_find_code NONE args code =
         (if args = [] then NONE else
           match LAST args with bvlSem_CodePtr loc ->
               (match sptree_lookup loc code with NONE -> NONE
                   | SOME (arity,exp) -> (if LENGTH args = arity +
                   1 then SOME (BUTLAST args,exp) else NONE)) |
                   other -> NONE)`];;

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

(* Proving termination of the evaluator directly is tricky. We make
   our life simpler by forcing the clock to stay good using
   fix_clock. At the bottom of this file, we remove all occurrences
   of fix_clock. *)

let bvlSem_fix_clock_def = new_definition
  `bvlSem_fix_clock s (res,s1) = (res,bvlSem_state_clock_fupd (K (MIN
  (bvlSem_state_clock s) (bvlSem_state_clock s1))) s1)`;;

(* fix_clock_IMP[local] *)
let bvlSem_fix_clock_IMP = prove
 (`bvlSem_fix_clock s x = (res,s1) ==> bvlSem_state_clock s1 <=
  bvlSem_state_clock s`,
  CHEAT_TAC);;

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of exp expressions. *)

let bvlSem_fix_clock_IMP =
  try prove
   (`!s x res s1. bvlSem_fix_clock s x = (res,s1)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; bvlSem_fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "bvlSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "bvlSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nbvlSem_fix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl bvlSem_fix_clock_IMP <> `T` then
  cake_term_facts := bvlSem_fix_clock_IMP :: (!cake_term_facts);;

let bvlSem_evaluate_def,bvlSem_evaluate_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`(bvlSem_evaluate ([],env,(s:('c,'ffi)bvlSem_state)) = (Rval [],s))
  /\
   (bvlSem_evaluate (CONS x (CONS y xs),env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate ([x],env,s)) with
        (Rval v1,s1) ->
          (match bvlSem_evaluate (CONS y xs,env,s1) with (Rval
            vs,s2) -> (Rval (CONS (HD v1) vs),s2) | res -> res) | res
            -> res)) /\
   (bvlSem_evaluate ([bvl_Var n],env,s) =
      (if n < LENGTH env then (Rval [EL n env],s) else (Rerr (Rabort
        Rtype_error),s))) /\
   (bvlSem_evaluate ([bvl_If x1 x2 x3],env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate ([x1],env,s)) with
        (Rval vs,s1) ->
           (if bvlSem_Boolv T = HD vs then bvlSem_evaluate
             ([x2],env,s1) else
           if bvlSem_Boolv F = HD vs then bvlSem_evaluate
             ([x3],env,s1) else
             (Rerr (Rabort Rtype_error),s1)) | res -> res)) /\
   (bvlSem_evaluate ([bvl_Let xs x2],env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate (xs,env,s)) with
        (Rval vs,s1) -> bvlSem_evaluate ([x2],APPEND vs env,s1) | res
        -> res)) /\
   (bvlSem_evaluate ([bvl_Raise x1],env,s) =
      (match bvlSem_evaluate ([x1],env,s) with (Rval vs,s) -> (Rerr
        (Rraise (HD vs)),s) | res -> res)) /\
   (bvlSem_evaluate ([bvl_Handle x1 x2],env,s1) =
      (match bvlSem_fix_clock s1 (bvlSem_evaluate ([x1],env,s1))
        with (Rerr (Rraise v),s) -> bvlSem_evaluate ([x2],CONS v env,s)
        | res -> res)) /\
   (bvlSem_evaluate ([bvl_Op op xs],env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate (xs,env,s)) with
        (Rval vs,s) ->
          (match bvlSem_do_app op (REVERSE vs) s with Rerr err ->
            (Rerr err,s) | Rval (v,s) -> (Rval [v],s)) | res -> res))
            /\
   (bvlSem_evaluate ([bvl_Tick x],env,s) =
      (if bvlSem_state_clock s = 0 then (Rerr (Rabort
        Rtimeout_error),s) else bvlSem_evaluate
        ([x],env,bvlSem_dec_clock 1 s))) /\
   (bvlSem_evaluate ([bvl_Force force_loc n],env,s) =
      (if ~(n < LENGTH env) then (Rerr (Rabort Rtype_error),s) else
        let thunk_v = EL n env in
          match bvlSem_dest_thunk thunk_v (bvlSem_state_refs s) with
            bvlSem_BadRef -> (Rerr (Rabort Rtype_error),s) |
            bvlSem_NotThunk -> (Rerr (Rabort Rtype_error),s) |
            bvlSem_IsThunk Evaluated v -> (Rval [v],s) | bvlSem_IsThunk
            NotEvaluated f ->
              (match bvlSem_find_code (SOME force_loc) [thunk_v; f]
                (bvlSem_state_code s) with NONE -> (Rerr (Rabort
                Rtype_error),s) | SOME (args,exp) ->
                   (if bvlSem_state_clock s = 0 then
                     (Rerr (Rabort
                       Rtimeout_error),bvlSem_state_clock_fupd (K 0) s)
                       else
                     bvlSem_evaluate ([exp],args,bvlSem_dec_clock 1
                       s))))) /\
   (bvlSem_evaluate ([bvl_Call ticks dest xs],env,s1) =
      (match bvlSem_fix_clock s1 (bvlSem_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match bvlSem_find_code dest vs (bvlSem_state_code s) with
            NONE -> (Rerr (Rabort Rtype_error),s) | SOME (args,exp) ->
               (if bvlSem_state_clock s < ticks + 1 then (Rerr
                 (Rabort Rtimeout_error),bvlSem_state_clock_fupd (K 0)
                 s) else
                   bvlSem_evaluate ([exp],args,bvlSem_dec_clock
                     (ticks + 1) s))) | res -> res))`];;

(* HOL4 bvlSemScript.sml:670: ML code, not ported *)

(* We prove that the clock never increases. *)

(* HOL4 bvlSemScript.sml:674-681: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

(* do_app_const *)
let bvlSem_do_app_const = prove
 (`(bvlSem_do_app op args s1 = Rval (res,s2)) ==>
    (bvlSem_state_clock s2 = bvlSem_state_clock s1) /\
    (~(op = closLang_Install) ==> bvlSem_state_code s2 =
      bvlSem_state_code s1 /\ bvlSem_state_compile
                       s2 = bvlSem_state_compile s1 /\
                         bvlSem_state_compile_oracle
                       s2 = bvlSem_state_compile_oracle s1)`,
  CHEAT_TAC);;

let bvl_do_app_Ref = prove
 (`bvlSem_do_app (closLang_MemOp closLang_Ref) vs s = Rval
     (bvlSem_RefPtr T (minimal ptr. ~(ptr IN FDOM (bvlSem_state_refs
       s))),bvlSem_state_refs_fupd (K (bvlSem_state_refs
        s |+ ((minimal ptr. ~(ptr IN FDOM (bvlSem_state_refs
          s))),bvlSem_ValueArray vs)))
      s)`,
  CHEAT_TAC);;
add_simp bvl_do_app_Ref;;

let bvl_do_app_Cons = prove
 (`bvlSem_do_app (closLang_BlockOp (closLang_Cons tag)) vs s = Rval
  (bvlSem_Block tag vs,s)`,
  CHEAT_TAC);;
add_simp bvl_do_app_Cons;;

(* evaluate_clock *)
let bvlSem_evaluate_clock = prove
 (`!xs env s1 vs s2.
     (bvlSem_evaluate (xs,env,s1) = (vs,s2)) ==> bvlSem_state_clock
       s2 <= bvlSem_state_clock s1`,
  CHEAT_TAC);;

(* fix_clock_evaluate *)
let bvlSem_fix_clock_evaluate = prove
 (`bvlSem_fix_clock s (bvlSem_evaluate (xs,env,s)) = bvlSem_evaluate
  (xs,env,s)`,
  CHEAT_TAC);;

(* Finally, we remove fix_clock from the induction and definition theorems. *)

(* HOL4 bvlSemScript.sml:729-730: a theorem that HOL4 states as the
   value of an ML expression: evaluate_def *)

(* HOL4 bvlSemScript.sml:732-733: a theorem that HOL4 states as the
   value of an ML expression: evaluate_ind *)

(* observational semantics *)

let bvlSem_initial_state_def = new_definition
  `bvlSem_initial_state ffi code co cc k = mk_bvlSem_state [] FEMPTY
  k cc co code ffi`;;

let bvlSem_semantics_def = new_definition
  `bvlSem_semantics init_ffi code co cc start' =
   (let es = [bvl_Call 0 (SOME start') []] in
   let init = bvlSem_initial_state init_ffi code co cc in
     if ?k. FST (bvlSem_evaluate (es,[],init k)) = Rerr (Rabort
       Rtype_error) then ffi_Fail else
     match some (\res.
       ?k s r outcome.
         bvlSem_evaluate (es,[],init k) = (r,s) /\
         (match r with Rerr (Rabort Rtimeout_error) -> F | Rerr
           (Rabort (Rffi_error e)) -> outcome = ffi_FFI_outcome e | _109
           -> outcome = ffi_Success) /\
         res = ffi_Terminate outcome (ffi_state_io_events
           (bvlSem_state_ffi s))) with SOME res -> res | NONE ->
        ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events
              (bvlSem_state_ffi
               (SND (bvlSem_evaluate (es,[],init k)))))) UNIV)))`;;

(* clean up *)

(* HOL4 bvlSemScript.sml:774: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["str"];;
