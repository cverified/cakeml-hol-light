(* ======================================================== *)
(*  bvlSem: ported from HOL4's
    compiler/backend/semantics/bvlSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of BVL
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_to_bvl.ml";;
needs "compiler/backend/dataLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/reg_alloc/reg_alloc.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "lib/ternaryComparisons.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
(* HOL4 ancestors outside the port: (* for closure_tag and
   num_added_globals *) backendProps *)

(* --- Semantics of BVL --- *)

let bvlSem_ref_INDUCT,bvlSem_ref_RECURSION = define_datatype
  "bvlSem_ref = bvlSem_ValueArray ('a list) | bvlSem_ByteArray (bool) \
   (word8 list) | bvlSem_Thunk (thunk_mode) ('a) | bvlSem_MutBlock \
   (num) (bool) ('a list) ('a) ('a list)";;

(* these parts are shared by bytecode and, if bytecode is to be
   supported, need
   to move to a common ancestor *)

let bvlSem_v_INDUCT,bvlSem_v_RECURSION = define_datatype
  "bvlSem_v = bvlSem_Number (int) | bvlSem_Word64 (word64) | \
   bvlSem_Block (num) (bvlSem_v list) | bvlSem_CodePtr (num) | \
   bvlSem_RefPtr (bool) (num)";;

let boolv_def = cake_define
  `bvlSem_Boolv b = bvlSem_Block (bool_to_tag b) []`;;

let unit_def = cake_define
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

let v_to_list_def = cake_define
  `bvlSem_v_to_list x1 =
        match x1 with
          (bvlSem_Block tag []) ->
        if tag = nil_tag then SOME [] else NONE
        | (bvlSem_Block tag [h; bt]) ->
        if tag = cons_tag then
          (match bvlSem_v_to_list bt with SOME t -> SOME (h :: t) |
            _1 -> NONE) else NONE
        | _2 -> NONE`;;

let list_to_v_def = cake_define
  `bvlSem_list_to_v [] = bvlSem_Block nil_tag [] /\
   bvlSem_list_to_v (bvlSem_v :: vs) = bvlSem_Block cons_tag
     [bvlSem_v; bvlSem_list_to_v vs]`;;

let isClos_def = cake_define
  `bvlSem_isClos t1 l1 = (((t1 = closure_tag) \/ (t1 =
  partial_app_tag)) /\ ~(l1 = []))`;;

let do_eq_def = cake_define
  `bvlSem_do_eq refs x2 x3 =
        match (x2,x3) with
          ((bvlSem_CodePtr _3),_4) -> Eq_type_error
        | (_5,(bvlSem_CodePtr _6)) -> Eq_type_error
        | ((bvlSem_Number n1),(bvlSem_Number n2)) -> (Eq_val (n1 =
          n2))
        | ((bvlSem_Number _7),_8) -> Eq_type_error
        | (_9,(bvlSem_Number _10)) -> Eq_type_error
        | ((bvlSem_Word64 w1),(bvlSem_Word64 w2)) -> (Eq_val (w1 =
          w2))
        | ((bvlSem_Word64 _11),_12) -> Eq_type_error
        | (_13,(bvlSem_Word64 _14)) -> Eq_type_error
        | ((bvlSem_RefPtr b1 n1),(bvlSem_RefPtr b2 n2)) ->
       if b1 /\ b2 then
        (match (FLOOKUP refs n1,FLOOKUP refs n2) with
           (SOME (bvlSem_ByteArray T bs1),SOME (bvlSem_ByteArray T
             bs2)) -> Eq_val (bs1 = bs2) | (SOME (bvlSem_ByteArray T
             bs1),_15) -> Eq_type_error | (_16,SOME (bvlSem_ByteArray T
             bs2)) -> Eq_type_error | _17 -> Eq_val (n1 = n2)) else
             Eq_type_error
        | ((bvlSem_RefPtr _18 _19),_20) -> Eq_type_error
        | (_21,(bvlSem_RefPtr _22 _23)) -> Eq_type_error
        | ((bvlSem_Block t1 l1),(bvlSem_Block t2 l2)) ->
      if bvlSem_isClos t1 l1 \/ bvlSem_isClos t2 l2 then if
        bvlSem_isClos t1 l1 /\ bvlSem_isClos t2 l2 then Eq_val T else
        Eq_type_error else if (t1 = t2) /\ (LENGTH l1 = LENGTH l2) then
        bvlSem_do_eq_list refs l1 l2 else Eq_val F
        | ([],[]) -> Eq_val T
        | ((v1 :: vs1),(v2 :: vs2)) ->
      match bvlSem_do_eq refs v1 v2 with Eq_val T ->
        bvlSem_do_eq_list refs vs1 vs2 | Eq_val F -> Eq_val F | bad ->
        bad
        | (_24,_25) -> Eq_val F`;;

(* HOL4 overload (expanded in the port):
     Error = (Rerr(Rabort Rtype_error)):(bvlSem$v#('c,'ffi)
       bvlSem$state, bvlSem$v)result *)

let v_to_bytes_def = cake_define
  `bvlSem_v_to_bytes lv = some (\(ns:word8 list).
                     bvlSem_v_to_list lv = SOME (MAP
                       (bvlSem_Number o (&) o w2n) ns))`;;

let v_to_words_def = cake_define
  `bvlSem_v_to_words lv = some (\ns. bvlSem_v_to_list lv = SOME (MAP
  bvlSem_Word64 ns))`;;

(* HOL4 ML code, not ported:
val s = ``(s:('c,'ffi) bvlSem$state)``
*)

let do_install_def = cake_define
  `^
     (do_install vs) s =
         (match vs with [v1; v2] ->
              (match (bvlSem_v_to_bytes v1,bvlSem_v_to_words v2) with
                (SOME bytes,SOME data) ->
                  (let (cfg,progs) = ?_compile_oracle s 0 in
                  let new_oracle = shift_seq 1 (?_compile_oracle s)
                    in
                   (if DISJOINT (domain (?_code s)) (set_of_list (MAP
                     FST progs)) /\
                       ALL_DISTINCT (MAP FST progs) then
                    (match (?_compile s cfg progs,progs) with (SOME
                      (bytes',data',cfg'),(k,prog) :: _26) ->
                         (if bytes = bytes' /\ data = data' /\ FST
                           (new_oracle 0) = cfg' then
                           let s' = ?_compile_oracle_fupd (K
                             new_oracle) (?_code_fupd (K (sptree_union
                             (?_code s) (fromAList progs)))
                             s) in
                             Rval (bvlSem_CodePtr k,s') else Rerr
                               (Rabort Rtype_error)) | _27 -> Rerr
                               (Rabort Rtype_error)) else Rerr
                               (Rabort Rtype_error))) | _28 -> Rerr
                               (Rabort Rtype_error)) | _29 -> Rerr
                               (Rabort Rtype_error))`;;

let do_part_def = cake_define
  `bvlSem_do_part m (clos_known_Int i) refs = (bvlSem_Number i,refs) /\
   bvlSem_do_part m (closLang_W64 w) refs = (bvlSem_Word64 w,refs) /\
   bvlSem_do_part m (flatLang_Con t ns) refs = (bvlSem_Block t (MAP m
     ns),refs) /\
   bvlSem_do_part m (closLang_Str t) refs =
     (let ptr = (LEAST (\ptr. ~(ptr IN FDOM refs))) in
     let bytes = MAP (n2w o ORD) (explode t) in
       (bvlSem_RefPtr T ptr,refs |+ (ptr,((bvlSem_ByteArray T
         bytes):bvlSem_v bvlSem_ref))))`;;

let do_build_def = cake_define
  `bvlSem_do_build m i [] refs = (m (i - 1),refs) /\
   bvlSem_do_build m i (p :: rest) refs =
     (let (x,refs1) = bvlSem_do_part m p refs in
       bvlSem_do_build ((i =+ x) m) (i + 1) rest refs1)`;;

let do_build_const_def = cake_define
  `bvlSem_do_build_const xs refs = bvlSem_do_build (\x. bvlSem_Number
  0) 0 xs refs`;;
(* same as closSem$do_int_app *)
let do_int_app_def = cake_define
  `bvlSem_do_int_app x1 x2 =
      match (x1,x2) with
        ((closLang_Const n),[]) -> SOME (bvlSem_Number n)
      | ((closLang_Add),[bvlSem_Number n1; bvlSem_Number n2]) -> SOME
        (bvlSem_Number (n1 + n2))
      | ((closLang_Sub),[bvlSem_Number n1; bvlSem_Number n2]) -> SOME
        (bvlSem_Number (n1 - n2))
      | ((closLang_Mult),[bvlSem_Number n1; bvlSem_Number n2]) ->
        SOME (bvlSem_Number (n1 * n2))
      | ((closLang_Div),[bvlSem_Number n1; bvlSem_Number n2]) ->
       (if n2 = 0 then NONE else SOME (bvlSem_Number (n1 / n2)))
      | ((closLang_Mod),[bvlSem_Number n1; bvlSem_Number n2]) ->
       (if n2 = 0 then NONE else SOME (bvlSem_Number (n1 % n2)))
      | (((LESS)),[bvlSem_Number n1; bvlSem_Number n2]) -> SOME
        (bvlSem_Boolv (n1 < n2))
      | ((closLang_LessEq),[bvlSem_Number n1; bvlSem_Number n2]) ->
        SOME (bvlSem_Boolv (n1 <= n2))
      | (((GREATER)),[bvlSem_Number n1; bvlSem_Number n2]) -> SOME
        (bvlSem_Boolv (n1 > n2))
      | ((closLang_GreaterEq),[bvlSem_Number n1; bvlSem_Number n2])
        -> SOME (bvlSem_Boolv (n1 >= n2))
      | ((closLang_LessConstSmall n),[bvlSem_Number i]) ->
         (if 0 <= i /\ i <= 1000000 /\ n < 1000000 then
           SOME (bvlSem_Boolv (i < &n)) else NONE)
      | ((flatLang_op:closLang_int_op),(vs:bvlSem_v list)) -> NONE`;;

(* same as closSem$do_word_app *)
let do_word_app_def = cake_define
  `bvlSem_do_word_app x1 ws =
        match (x1,ws) with
          ((WordOpw ast_W8 opw),[bvlSem_Number n1; bvlSem_Number n2])
            ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (bvlSem_Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw closLang_W64 opw),[bvlSem_Word64 w1;
          bvlSem_Word64 w2]) ->
           SOME (bvlSem_Word64 (opw_lookup opw w1 w2))
        | ((WordTest ast_W8 test),[bvlSem_Number n1; bvlSem_Number
          n2]) ->
          (if 0 <= n1 /\ n1 < 256 /\ 0 <= n2 /\ n2 < 256 then
             (match test with (EQUAL) -> SOME (bvlSem_Boolv (n1 =
               n2)) | ast_Compare cmp -> SOME (bvlSem_Boolv
               (semanticPrimitives_int_cmp cmp n1 n2)) | _30 -> NONE)
               else NONE)
        | ((WordShift ast_W8 sh n),[bvlSem_Number i]) ->
          (match some (\(w:word8). i = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (bvlSem_Number (&(w2n (shift_lookup sh w
            n)))))
        | ((WordShift closLang_W64 sh n),[bvlSem_Word64 w]) ->
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
                  _31 -> NONE)
        | ((FP_bop bop),ws) ->
           (match ws with [bvlSem_Word64 w1; bvlSem_Word64 w2] ->
             (SOME (bvlSem_Word64 (fp_bop_comp bop w1 w2))) | _32 ->
             NONE)
        | ((FP_uop uop),ws) ->
           (match ws with [bvlSem_Word64 w] -> (SOME (bvlSem_Word64
             (fp_uop_comp uop w))) | _33 -> NONE)
        | ((FP_cmp cmp),ws) ->
           (match ws with [bvlSem_Word64 w1; bvlSem_Word64 w2] ->
             (SOME (bvlSem_Boolv (fp_cmp_comp cmp w1 w2))) | _34 ->
             NONE)
        | ((flatLang_op:closLang_word_op),(vs:bvlSem_v list)) ->
          NONE`;;

let bvlSem_dest_thunk_ret_INDUCT,bvlSem_dest_thunk_ret_RECURSION =
  define_datatype
  "bvlSem_dest_thunk_ret = bvlSem_BadRef | bvlSem_NotThunk | \
   bvlSem_IsThunk (thunk_mode) (bvlSem_v)";;

let dest_thunk_def = cake_define
  `bvlSem_dest_thunk x1 refs =
      match x1 with
        (bvlSem_RefPtr b ptr) ->
     (match FLOOKUP refs ptr with NONE -> bvlSem_BadRef | SOME
       (bvlSem_Thunk Evaluated bvlSem_v) ->
          (if b then bvlSem_BadRef else bvlSem_IsThunk Evaluated
            bvlSem_v) | SOME (bvlSem_Thunk NotEvaluated bvlSem_v) ->
          (if b then bvlSem_BadRef else bvlSem_IsThunk NotEvaluated
            bvlSem_v) | SOME _35 -> bvlSem_NotThunk)
      | _36 -> bvlSem_NotThunk`;;

let bad_thunk_update_def = cake_define
  `bvlSem_bad_thunk_update m bvlSem_v refs <=>
     m = Evaluated /\ ~(bvlSem_dest_thunk bvlSem_v refs =
       bvlSem_NotThunk)`;;

(* same as closSem$do_app, except:
    - LengthByteVec and DerefByteVec are removed
    - FromListByte, ToListByte, String, ConcatByteVec, and
      CopyByte work on ByteArrays rather than ByteVectors
    - Build now has full semantics, i.e. can handle all cases
    - Label is added *)

let do_app_def = cake_define
  `^
     (semanticPrimitives_do_app flatLang_op vs) s =
       (match (flatLang_op,vs) with (closLang_GlobOp (Global n),[])
         ->
           (match get_global n (?_globals s) with SOME (SOME
             bvlSem_v) -> Rval (bvlSem_v,s) | _37 -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_GlobOp
             (Global _38),[bvlSem_Number i]) ->
           (if i < 0 then ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result) else
            match get_global (num_of_int i + num_added_globals)
              (?_globals s) with SOME (SOME bvlSem_v) -> Rval
              (bvlSem_v,s) | _39 -> ((Rerr (Rabort
              Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
              ,bvlSem_v)semanticPrimitives_result)) | (closLang_GlobOp
              (SetGlobal n),[bvlSem_v]) ->
           (match get_global n (?_globals s) with SOME _40 -> Rval
             (bvlSem_Unit,?_globals_fupd (K (LUPDATE (SOME bvlSem_v) n
             (?_globals s)))
                s) | _41 -> ((Rerr (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result)) |
                  (closLang_GlobOp AllocGlobal,[bvlSem_Number i]) ->
           (if i < 0 then ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result) else Rval
             (bvlSem_Unit,?_globals_fupd (K (?_globals s ++ REPLICATE
             (num_of_int i) NONE)) s)) | (closLang_Install,vs) ->
             do_install vs s | (closLang_BlockOp (closLang_Cons tag),xs)
             -> Rval (bvlSem_Block tag xs,s) | (closLang_BlockOp
             (closLang_BoolTest test),[v1; v2]) ->
           (if (~(v1 = bvlSem_Boolv T) /\ ~(v1 = bvlSem_Boolv F))
             then ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result) else
            if (~(v2 = bvlSem_Boolv T) /\ ~(v2 = bvlSem_Boolv F))
              then ((Rerr (Rabort
              Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
              ,bvlSem_v)semanticPrimitives_result) else
              Rval (bvlSem_Boolv (v1 = v2),s)) | (closLang_BlockOp
                closLang_BoolNot,[v1]) ->
           (if v1 = bvlSem_Boolv T then Rval (bvlSem_Boolv F,s) else
            if v1 = bvlSem_Boolv F then Rval (bvlSem_Boolv T,s) else
              ((Rerr (Rabort
              Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
              ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
              (closLang_Build parts),[]) ->
           (let (bvlSem_v,rs) = bvlSem_do_build_const parts (?_refs
             s) in Rval (bvlSem_v,?_refs_fupd (K rs) s)) |
             (closLang_BlockOp (closLang_ConsExtend tag),bvlSem_Block
             _42 xs' :: bvlSem_Number lower :: bvlSem_Number len ::
             bvlSem_Number tot :: xs) ->
           (if lower < 0 \/ len < 0 \/ lower + len > &LENGTH xs' \/
              tot = 0 \/ ~(tot = &LENGTH xs + len) then
             ((Rerr (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result) else
             Rval (bvlSem_Block tag (xs ++ TAKE (num_of_int len)
               (DROP (num_of_int lower) xs')),s)) | (closLang_BlockOp
               (closLang_ConsExtend tag),_43) -> ((Rerr (Rabort
               Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
               ,bvlSem_v)semanticPrimitives_result) | (closLang_MemOp
               flatLang_El,[bvlSem_Block tag xs; bvlSem_Number i]) ->
           (if 0 <= i /\ num_of_int i < LENGTH xs then Rval (EL
             (num_of_int i) xs,s) else ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
             flatLang_El,[bvlSem_RefPtr _44 ptr; bvlSem_Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ValueArray
             xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval (EL
                 (num_of_int i) xs,s) else ((Rerr (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | _45 -> ((Rerr
                 (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) |
                 (closLang_BlockOp (closLang_ElemAt n),[bvlSem_Block tag
                 xs]) ->
           (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
             (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
             (closLang_ElemAt n),[bvlSem_RefPtr _46 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ValueArray
             xs) ->
               (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
                 (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | _47 -> ((Rerr
                 (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) |
                 (closLang_BlockOp closLang_ListAppend,[x1; x2]) ->
           (match (bvlSem_v_to_list x1,bvlSem_v_to_list x2) with
             (SOME xs,SOME ys) -> Rval (bvlSem_list_to_v (xs ++ ys),s) |
             _48 -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_BlockOp
             closLang_LengthBlock,[bvlSem_Block tag xs]) ->
           Rval (bvlSem_Number (&LENGTH xs),s) | (closLang_MemOp
             closLang_Length,[bvlSem_RefPtr _49 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ValueArray
             xs) ->
                 Rval (bvlSem_Number (&LENGTH xs),s) | _50 -> ((Rerr
                   (Rabort
                   Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                   ,bvlSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp closLang_LengthByte,[bvlSem_RefPtr
                   _51 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ByteArray
             _52 xs) ->
                 Rval (bvlSem_Number (&LENGTH xs),s) | _53 -> ((Rerr
                   (Rabort
                   Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                   ,bvlSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp (closLang_RefByte F),[bvlSem_Number
                   i; bvlSem_Number b]) ->
            (if 0 <= i /\ (?(w:word8). b = &(w2n w)) then
              let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s)))) in
                Rval (bvlSem_RefPtr T ptr,?_refs_fupd (K (?_refs s |+
                  (ptr,bvlSem_ByteArray F (REPLICATE (num_of_int i)
                    (i2w b))))) s) else ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp closLang_RefArray,[bvlSem_Number i;
                    bvlSem_v]) ->
           (if 0 <= i then
             let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s)))) in
               Rval (bvlSem_RefPtr T ptr,?_refs_fupd (K (?_refs s |+
                 (ptr,bvlSem_ValueArray (REPLICATE (num_of_int i)
                   bvlSem_v)))) s) else ((Rerr (Rabort
                   Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                   ,bvlSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp closLang_DerefByte,[bvlSem_RefPtr _54
                   ptr; bvlSem_Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ByteArray
             _55 ws) ->
               (if 0 <= i /\ i < &LENGTH ws then Rval (bvlSem_Number
                 (&(w2n (EL (num_of_int i) ws))),s) else ((Rerr (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | _56 -> ((Rerr
                 (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                 closLang_UpdateByte,[bvlSem_RefPtr _57 ptr;
                 bvlSem_Number i; bvlSem_Number b]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ByteArray
             f bs) ->
               (if 0 <= i /\ i < &LENGTH bs /\ (?(w:word8). b = &(w2n
                 w)) then
                  Rval (bvlSem_Unit,?_refs_fupd (K (?_refs s |+
                    (ptr,bvlSem_ByteArray f (LUPDATE (i2w b)
                      (num_of_int i) bs)))) s) else ((Rerr (Rabort
                      Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                      ,bvlSem_v)semanticPrimitives_result)) | _58 ->
                      ((Rerr (Rabort
                      Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                      ,bvlSem_v)semanticPrimitives_result)) |
                      (closLang_MemOp closLang_ConcatByteVec,[lv]) ->
            (match
               (some (\wss. ?ps.
                 bvlSem_v_to_list lv = SOME (MAP (bvlSem_RefPtr T)
                   ps) /\
                 MAP (FLOOKUP (?_refs s)) ps = MAP (SOME o
                   bvlSem_ByteArray T) wss)) with SOME wss ->
               (let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s))))
                 in
                 Rval (bvlSem_RefPtr T ptr,?_refs_fupd (K (?_refs s
                   |+
                          (ptr,bvlSem_ByteArray T (FLAT wss)))) s)) |
                            _59 -> ((Rerr (Rabort
                            Rtype_error)):(bvlSem_v#('c
                            ,'ffi)bvlSem_state
                            ,bvlSem_v)semanticPrimitives_result)) |
                            (closLang_BlockOp (closLang_FromList
                            n),[lv]) ->
           (match bvlSem_v_to_list lv with SOME vs -> Rval
             (bvlSem_Block n vs,s) | _60 -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
             closLang_FromListByte,[lv]) ->
           (match some (\ns. bvlSem_v_to_list lv = SOME (MAP
             (bvlSem_Number o (&)) ns) /\ EVERY (\n. n < 256) ns) with
             SOME ns -> (let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs
             s)))) in
                            Rval (bvlSem_RefPtr T ptr,?_refs_fupd (K
                              (?_refs s |+
                              (ptr,bvlSem_ByteArray T (MAP n2w ns))))
                                s)) | NONE -> ((Rerr (Rabort
                                Rtype_error)):(bvlSem_v#('c
                                ,'ffi)bvlSem_state
                                ,bvlSem_v)semanticPrimitives_result)) |
                                (closLang_MemOp
                                closLang_ToListByte,[bvlSem_RefPtr _61
                                ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ByteArray
             f bs) ->
               (Rval (bvlSem_list_to_v (MAP (\b. bvlSem_Number (&(w2n
                 b))) bs),s)) | _62 -> ((Rerr (Rabort
                 Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                 ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                 (closLang_CopyByte F),[bvlSem_RefPtr _63 src;
                 bvlSem_Number srcoff; bvlSem_Number len; bvlSem_RefPtr
                 _64 dst; bvlSem_Number dstoff]) ->
           (match (FLOOKUP (?_refs s) src,FLOOKUP (?_refs s) dst)
             with (SOME (bvlSem_ByteArray _65 ws),SOME (bvlSem_ByteArray
             fl ds)) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff))
                with SOME ds -> Rval (bvlSem_Unit,?_refs_fupd (K (?_refs
                s |+ (dst,bvlSem_ByteArray fl ds))) s) | NONE -> ((Rerr
                (Rabort
                Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                ,bvlSem_v)semanticPrimitives_result)) | _66 -> ((Rerr
                (Rabort
                Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                (closLang_CopyByte T),[bvlSem_RefPtr _67 src;
                bvlSem_Number srcoff; bvlSem_Number len]) ->
          (match (FLOOKUP (?_refs s) src) with SOME (bvlSem_ByteArray
            _68 ws) ->
              (match copy_array (ws,srcoff) len NONE with SOME ds ->
                 (let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s))))
                   in
                 Rval (bvlSem_RefPtr T ptr,?_refs_fupd (K (?_refs s
                   |+ (ptr,bvlSem_ByteArray T ds))) s)) | _69 -> ((Rerr
                   (Rabort
                   Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                   ,bvlSem_v)semanticPrimitives_result)) | _70 -> ((Rerr
                   (Rabort
                   Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                   ,bvlSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp closLang_XorByte,[bvlSem_RefPtr _71
                   dst; bvlSem_RefPtr _72 src]) ->
           (match (FLOOKUP (?_refs s) src,FLOOKUP (?_refs s) dst)
             with (SOME (bvlSem_ByteArray _73 ws),SOME (bvlSem_ByteArray
             fl ds)) ->
              (match xor_bytes ws ds with SOME ds1 -> Rval
                (bvlSem_Unit,?_refs_fupd (K (?_refs s |+
                (dst,bvlSem_ByteArray fl ds1))) s) | NONE -> ((Rerr
                (Rabort
                Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                ,bvlSem_v)semanticPrimitives_result)) | _74 -> ((Rerr
                (Rabort
                Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
                (closLang_StringCmp b cmp),[bvlSem_RefPtr _75 s1;
                bvlSem_RefPtr _76 s2]) ->
           (match (FLOOKUP (?_refs s) s1,FLOOKUP (?_refs s) s2) with
             (SOME (bvlSem_ByteArray _77 ws1),SOME (bvlSem_ByteArray _78
             ws2)) ->
                (let s1 = implode (MAP (CHR o w2n) ws1) in
                 let s2 = implode (MAP (CHR o w2n) ws2) in
                   Rval (bvlSem_Boolv (str_cmp b cmp s1 s2),s)) | _79
                     -> ((Rerr (Rabort
                     Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                     ,bvlSem_v)semanticPrimitives_result)) |
                     (closLang_BlockOp (closLang_TagEq n),[bvlSem_Block
                     tag xs]) ->
           Rval (bvlSem_Boolv (tag = n),s) | (closLang_BlockOp
             (flatLang_LenEq l),[bvlSem_Block tag xs]) ->
           Rval (bvlSem_Boolv (LENGTH xs = l),s) | (closLang_BlockOp
             (flatLang_TagLenEq n l),[bvlSem_Block tag xs]) ->
           Rval (bvlSem_Boolv (tag = n /\ LENGTH xs = l),s) |
             (closLang_BlockOp (closLang_EqualConst p),[x1]) ->
           (match p with clos_known_Int i -> (match x1 with
             bvlSem_Number j -> Rval (bvlSem_Boolv (i = j),s) | _80 ->
             ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | closLang_W64 i ->
             (match x1 with bvlSem_Word64 j -> Rval (bvlSem_Boolv (i =
             j),s) | _81 -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | closLang_Str i ->
             (match x1 with bvlSem_RefPtr _82 p ->
                          (match FLOOKUP (?_refs s) p with SOME
                            (bvlSem_ByteArray T j) ->
                             Rval (bvlSem_Boolv (j = MAP (n2w o ORD)
                               (explode i)),s) | _83 -> ((Rerr (Rabort
                               Rtype_error)):(bvlSem_v#('c
                               ,'ffi)bvlSem_state
                               ,bvlSem_v)semanticPrimitives_result)) |
                               _84 -> ((Rerr (Rabort
                               Rtype_error)):(bvlSem_v#('c
                               ,'ffi)bvlSem_state
                               ,bvlSem_v)semanticPrimitives_result)) |
                               _85 -> ((Rerr (Rabort
                               Rtype_error)):(bvlSem_v#('c
                               ,'ffi)bvlSem_state
                               ,bvlSem_v)semanticPrimitives_result)) |
                               (closLang_BlockOp (EQUAL),[x1; x2]) ->
           (match bvlSem_do_eq (?_refs s) x1 x2 with Eq_val b -> Rval
             (bvlSem_Boolv b,s) | _86 -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_MemOp
             closLang_Ref,xs) ->
           (let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s)))) in
             Rval (bvlSem_RefPtr T ptr,?_refs_fupd (K (?_refs s |+
               (ptr,bvlSem_ValueArray xs))) s)) | (closLang_MemOp
               closLang_Update,[bvlSem_RefPtr _87 ptr; bvlSem_Number i;
               x]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (bvlSem_ValueArray
             xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval
                 (bvlSem_Unit,?_refs_fupd (K (?_refs s |+
                              (ptr,bvlSem_ValueArray (LUPDATE x
                                (num_of_int i) xs)))) s) else ((Rerr
                                (Rabort
                                Rtype_error)):(bvlSem_v#('c
                                ,'ffi)bvlSem_state
                                ,bvlSem_v)semanticPrimitives_result)) |
                                _88 -> ((Rerr (Rabort
                                Rtype_error)):(bvlSem_v#('c
                                ,'ffi)bvlSem_state
                                ,bvlSem_v)semanticPrimitives_result)) |
                                (closLang_Label n,[]) ->
           (if n IN domain (?_code s) then Rval (bvlSem_CodePtr n,s)
             else ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_IntOp
             intop,vs) ->
           (match bvlSem_do_int_app intop vs with SOME res -> Rval
             (res,s) | _89 -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_WordOp
             wordop,vs) ->
           (match bvlSem_do_word_app wordop vs with SOME res -> Rval
             (res,s) | _90 -> ((Rerr (Rabort
             Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
             ,bvlSem_v)semanticPrimitives_result)) | (closLang_FFI
             n,[bvlSem_RefPtr _91 cptr; bvlSem_RefPtr _92 ptr]) ->
           (match (FLOOKUP (?_refs s) cptr,FLOOKUP (?_refs s) ptr)
             with (SOME (bvlSem_ByteArray T cws),SOME (bvlSem_ByteArray
             F ws)) ->
              (match call_FFI (?_ffi s) (ExtCall n) cws ws with
                FFI_return ffi' ws' ->
                   Rval (bvlSem_Unit,?_ffi_fupd (K ffi') (?_refs_fupd
                     (K (?_refs s |+ (ptr,bvlSem_ByteArray F ws')))
                         s)) | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome))) | _93 ->
                     ((Rerr (Rabort
                     Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                     ,bvlSem_v)semanticPrimitives_result)) |
                     (closLang_BlockOp closLang_BoundsCheckBlock,xs) ->
           (match xs with [bvlSem_Block tag ys; bvlSem_Number i] ->
                  Rval (bvlSem_Boolv (0 <= i /\ i < &LENGTH ys),s) |
                    _94 -> ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp (closLang_BoundsCheckByte loose),xs)
                    ->
           (match xs with [bvlSem_RefPtr _95 ptr; bvlSem_Number i] ->
             (match FLOOKUP (?_refs s) ptr with SOME
               (bvlSem_ByteArray _96 ws) ->
                  Rval (bvlSem_Boolv (0 <= i /\ (if loose then (<=)
                    else (<)) i (&LENGTH ws)),s) | _97 -> ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) | _98 ->
                    ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp closLang_BoundsCheckArray,xs) ->
           (match xs with [bvlSem_RefPtr _99 ptr; bvlSem_Number i] ->
             (match FLOOKUP (?_refs s) ptr with SOME
               (bvlSem_ValueArray ws) ->
                  Rval (bvlSem_Boolv (0 <= i /\ i < &LENGTH ws),s) |
                    _100 -> ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) | _101 ->
                    ((Rerr (Rabort
                    Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                    ,bvlSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp closLang_ConfigGC,[bvlSem_Number
                    _102; bvlSem_Number _103]) -> (Rval (bvlSem_Unit,s))
                    | (closLang_ThunkOp th_op,vs) ->
           (match (th_op,vs) with (AllocThunk m,[bvlSem_v]) ->
                (if bvlSem_bad_thunk_update m bvlSem_v (?_refs s)
                  then ((Rerr (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result) else
                 let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s))))
                   in
                   Rval (bvlSem_RefPtr F ptr,?_refs_fupd (K (?_refs s
                     |+ (ptr,bvlSem_Thunk m bvlSem_v))) s)) |
                     (UpdateThunk m,[bvlSem_RefPtr F ptr; bvlSem_v]) ->
                (if bvlSem_bad_thunk_update m bvlSem_v (?_refs s)
                  then ((Rerr (Rabort
                  Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                  ,bvlSem_v)semanticPrimitives_result) else
                 match FLOOKUP (?_refs s) ptr with SOME (bvlSem_Thunk
                   NotEvaluated _104) ->
                    Rval (bvlSem_Unit,?_refs_fupd (K (?_refs s |+
                      (ptr,bvlSem_Thunk m bvlSem_v))) s) | _105 ->
                      ((Rerr (Rabort
                      Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                      ,bvlSem_v)semanticPrimitives_result)) | _106 ->
                      ((Rerr (Rabort
                      Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                      ,bvlSem_v)semanticPrimitives_result)) | _107 ->
                      ((Rerr (Rabort
                      Rtype_error)):(bvlSem_v#('c,'ffi)bvlSem_state
                      ,bvlSem_v)semanticPrimitives_result))`;;

let dec_clock_def = cake_define
  `bvlSem_dec_clock n s = ?_clock_fupd (K (?_clock s - n)) s`;;

(* Functions for looking up function definitions *)

let find_code_def = cake_define
  `(bvlSem_find_code (SOME p) args code =
      (match sptree_lookup p code with NONE -> NONE | SOME
        (arity,flatLang_exp) -> (if LENGTH args = arity then SOME
        (args,flatLang_exp) else NONE))) /\
   (bvlSem_find_code NONE args code =
      (if args = [] then NONE else
        match LAST args with bvlSem_CodePtr loc ->
            (match sptree_lookup loc code with NONE -> NONE | SOME
              (arity,flatLang_exp) -> (if LENGTH args = arity + 1
              then SOME (FRONT args,flatLang_exp) else NONE)) | other
              -> NONE))`;;

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

(* Proving termination of the evaluator directly is tricky. We make
   our life simpler by forcing the clock to stay good using
   fix_clock. At the bottom of this file, we remove all occurrences
   of fix_clock. *)

let fix_clock_def = cake_define
  `bvlSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of exp expressions. *)

(* HOL4 termination: \\ rpt strip_tac \\ simp[dec_clock_def] \\
   imp_res_tac fix_clock_IMP \\ FULL_SIMP_TAC (srw_ss()) [] \\
   decide_tac *)
let evaluate_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE (list_size exp_size))
                            (\(xs,env,s). (?_clock s,xs)))`
  `(bvlSem_evaluate ([],env,s) = (Rval [],s)) /\
   (bvlSem_evaluate (x :: y :: xs,env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate ([x],env,s)) with
        (Rval v1,s1) ->
          (match bvlSem_evaluate (y :: xs,env,s1) with (Rval vs,s2)
            -> (Rval (HD v1 :: vs),s2) | res -> res) | res -> res)) /\
   (bvlSem_evaluate ([db_vars_Var n],env,s) =
      (if n < LENGTH env then (Rval [EL n env],s) else (Rerr (Rabort
        Rtype_error),s))) /\
   (bvlSem_evaluate ([flatLang_If x1 x2 x3],env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate ([x1],env,s)) with
        (Rval vs,s1) ->
           (if bvlSem_Boolv T = HD vs then bvlSem_evaluate
             ([x2],env,s1) else
           if bvlSem_Boolv F = HD vs then bvlSem_evaluate
             ([x3],env,s1) else
             (Rerr (Rabort Rtype_error),s1)) | res -> res)) /\
   (bvlSem_evaluate ([flatLang_Let xs x2],env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate (xs,env,s)) with
        (Rval vs,s1) -> bvlSem_evaluate ([x2],vs ++ env,s1) | res ->
        res)) /\
   (bvlSem_evaluate ([flatLang_Raise x1],env,s) =
      (match bvlSem_evaluate ([x1],env,s) with (Rval vs,s) -> (Rerr
        (Rraise (HD vs)),s) | res -> res)) /\
   (bvlSem_evaluate ([flatLang_Handle x1 x2],env,s1) =
      (match bvlSem_fix_clock s1 (bvlSem_evaluate ([x1],env,s1)) with
        (Rerr (Rraise bvlSem_v),s) -> bvlSem_evaluate ([x2],bvlSem_v ::
        env,s) | res -> res)) /\
   (bvlSem_evaluate ([bvl_Op flatLang_op xs],env,s) =
      (match bvlSem_fix_clock s (bvlSem_evaluate (xs,env,s)) with
        (Rval vs,s) ->
          (match semanticPrimitives_do_app flatLang_op (REVERSE vs) s
            with Rerr err -> (Rerr err,s) | Rval (bvlSem_v,s) -> (Rval
            [bvlSem_v],s)) | res -> res)) /\
   (bvlSem_evaluate ([bvl_Tick x],env,s) =
      (if ?_clock s = 0 then (Rerr (Rabort Rtimeout_error),s) else
        bvlSem_evaluate ([x],env,bvlSem_dec_clock 1 s))) /\
   (bvlSem_evaluate ([bvl_Force force_loc n],env,s) =
      (if ~(n < LENGTH env) then (Rerr (Rabort Rtype_error),s) else
        let thunk_v = EL n env in
          match bvlSem_dest_thunk thunk_v (?_refs s) with
            bvlSem_BadRef -> (Rerr (Rabort Rtype_error),s) |
            bvlSem_NotThunk -> (Rerr (Rabort Rtype_error),s) |
            bvlSem_IsThunk Evaluated bvlSem_v -> (Rval [bvlSem_v],s) |
            bvlSem_IsThunk NotEvaluated f ->
              (match bvlSem_find_code (SOME force_loc) [thunk_v; f]
                (?_code s) with NONE -> (Rerr (Rabort Rtype_error),s) |
                SOME (args,flatLang_exp) ->
                   (if ?_clock s = 0 then
                     (Rerr (Rabort Rtimeout_error),?_clock_fupd (K 0)
                       s) else
                     bvlSem_evaluate
                       ([flatLang_exp],args,bvlSem_dec_clock 1 s))))) /\
   (bvlSem_evaluate ([bvl_Call ticks dest xs],env,s1) =
      (match bvlSem_fix_clock s1 (bvlSem_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match bvlSem_find_code dest vs (?_code s) with NONE ->
            (Rerr (Rabort Rtype_error),s) | SOME (args,flatLang_exp) ->
               (if ?_clock s < ticks + 1 then (Rerr (Rabort
                 Rtimeout_error),?_clock_fupd (K 0) s) else
                   bvlSem_evaluate
                     ([flatLang_exp],args,bvlSem_dec_clock (ticks +
                     1) s))) | res -> res))`;;

(* HOL4 ML code, not ported:
val evaluate_ind = theorem"evaluate_ind";
*)

(* We prove that the clock never increases. *)

(* Finally, we remove fix_clock from the induction and definition
   theorems. *)

(* observational semantics *)

let initial_state_def = cake_define
  `bvlSem_initial_state ffi code co cc k = mk_? k ffi code cc co []
  FEMPTY`;;

let semantics_def = cake_define
  `bvlSem_semantics init_ffi code co cc start =
   (let es = [bvl_Call 0 (SOME start) []] in
   let init = bvlSem_initial_state init_ffi code co cc in
     if ?k. FST (bvlSem_evaluate (es,[],init k)) = Rerr (Rabort
       Rtype_error) then ffi_Fail else
     match some (\res.
       ?k s r outcome.
         bvlSem_evaluate (es,[],init k) = (r,s) /\
         (match r with Rerr (Rabort Rtimeout_error) -> F | Rerr
           (Rabort (Rffi_error e)) -> outcome = ffi_FFI_outcome e | _108
           -> outcome = ffi_Success) /\
         res = ffi_Terminate outcome (ffi_state_io_events (?_ffi s)))
           with SOME res -> res | NONE ->
        ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (?_ffi
               (SND (bvlSem_evaluate (es,[],init k)))))) UNIV)))`;;

(* clean up *)

(* HOL4 ML code, not ported:
val _ = map delete_binding ["evaluate_AUX_def",
  "evaluate_primitive_def"];
*)
