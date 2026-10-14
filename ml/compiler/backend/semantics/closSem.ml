(* ======================================================== *)
(*  closSem: ported from HOL4's
    compiler/backend/semantics/closSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of closLang
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/flatLang.ml";;
(* HOL4 ancestors outside the port: semanticPrimitivesProps (* for
   opw_lookup_def and others *) *)

(* differs from store_v by removing the single value Refv,
   also, adds flag to ByteArray for equality semantics *)
let closSem_ref_INDUCT,closSem_ref_RECURSION = define_datatype
  "closSem_ref = closSem_ValueArray ('a list) | closSem_ByteArray \
   (word8 list) | closSem_Thunk (thunk_mode) ('a)";;

(* --- Semantics of ClosLang --- *)

let closSem_v_INDUCT,closSem_v_RECURSION = define_datatype
  "closSem_v = closSem_Number (int) | closSem_Word64 (word64) | \
   closSem_Block (num) (closSem_v list) | closSem_ByteVector (word8 \
   list) | closSem_RefPtr (bool) (num) | closSem_Closure (num option) \
   (closSem_v list) (closSem_v list) (num) (closLang_exp) | \
   closSem_Recclosure (num option) (closSem_v list) (closSem_v list) \
   ((num#closLang_exp) list) (num)";;

(* HOL4 type abbreviation (expanded in the port):
     clos_co = num -> 'c # clos_prog *)

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

(* helper functions *)

let get_global_def = cake_define
  `get_global n globals =
     (if n < LENGTH globals then SOME (EL n globals) else NONE)`;;

let Boolv_def = cake_define
  `(closSem_Boolv b = closSem_Block (if b then true_tag else
  false_tag) [])`;;

let do_eq_def = cake_define
  `closSem_do_eq x y =
        match (x,y) with
          (x,y) ->
        match x with closSem_Number i ->
            (match y with closSem_Number j -> Eq_val (i = j) | _1 ->
              Eq_type_error) | closSem_Word64 closSem_v ->
            (match y with closSem_Word64 w -> Eq_val (closSem_v = w)
              | _2 -> Eq_type_error) | closSem_Block t1 xs ->
            (match y with closSem_Block t2 ys -> (if (t1 = t2) /\
              (LENGTH xs = LENGTH ys) then
                              closSem_do_eq_list xs ys else Eq_val F)
                                | _3 -> Eq_type_error) |
                                closSem_ByteVector cs ->
            (match y with closSem_ByteVector ds -> Eq_val (cs = ds) |
              _4 -> Eq_type_error) | closSem_RefPtr bi i ->
            (match y with closSem_RefPtr bj j -> (if bi /\ bj then
              Eq_val (i = j) else Eq_type_error) | _5 -> Eq_type_error)
              | _6 ->
            (match y with closSem_Number _7 -> Eq_type_error |
              closSem_Word64 _8 -> Eq_type_error | closSem_Block _9 _10
              -> Eq_type_error | closSem_ByteVector _11 -> Eq_type_error
              | closSem_RefPtr _12 _13 -> Eq_type_error | _14 -> Eq_val
              T)
        | ([],[]) -> Eq_val T
        | ((x :: xs),(y :: ys)) ->
        match closSem_do_eq x y with Eq_val T -> closSem_do_eq_list
          xs ys | res -> res
        | (_15,_16) -> Eq_val F`;;

let v_to_list_def = cake_define
  `closSem_v_to_list x1 =
        match x1 with
          (closSem_Block tag []) ->
        if tag = nil_tag then SOME [] else NONE
        | (closSem_Block tag [h; bt]) ->
        if tag = cons_tag then
          (match closSem_v_to_list bt with SOME t -> SOME (h :: t) |
            _17 -> NONE) else NONE
        | _18 -> NONE`;;

let list_to_v_def = cake_define
  `closSem_list_to_v [] = closSem_Block nil_tag [] /\
   closSem_list_to_v (x :: xs) = closSem_Block cons_tag [x;
     closSem_list_to_v xs]`;;

let Unit_def = cake_define
  `closSem_Unit = closSem_Block tuple_tag []`;;

(* HOL4 overload (expanded in the port):
     Error = (Rerr(Rabort Rtype_error)):(closSem$v#(('c,'ffi)
       closSem$state), closSem$v)result *)

let v_to_bytes_def = cake_define
  `closSem_v_to_bytes lv = some (\(ns:word8 list).
                     closSem_v_to_list lv = SOME (MAP
                       (closSem_Number o & o w2n) ns))`;;

let v_to_words_def = cake_define
  `closSem_v_to_words lv = some (\ns. closSem_v_to_list lv = SOME
  (MAP closSem_Word64 ns))`;;

(* HOL4 ML code, not ported:
val s = ``s:('c,'ffi)closSem$state``;
*)

let do_install_def = cake_define
  `^
     (do_install vs) s =
         (match vs with [v1; v2] ->
              (match (closSem_v_to_bytes v1,closSem_v_to_words v2)
                with (SOME bytes,SOME data) ->
                  (let (cfg,progs) = closSem_state_compile_oracle s 0
                    in
                  let new_oracle = shift_seq 1
                    (closSem_state_compile_oracle s) in
                   (if DISJOINT (FDOM (closSem_state_code s))
                     (set_of_list (MAP FST (SND progs))) /\
                       ALL_DISTINCT (MAP FST (SND progs)) then
                    (match (closSem_state_compile s cfg progs,progs)
                      with (SOME (bytes',data',cfg'),(exps,aux)) ->
                         (if bytes = bytes' /\ data = data' /\
                            FST (new_oracle 0) = cfg' /\ ~(exps = [])
                              then
                          (let s' = ?_clock_fupd (K (?_clock s - 1))
                            (closSem_state_compile_oracle_fupd (K
                            new_oracle) (closSem_state_code_fupd (K
                            (closSem_state_code s |++ aux))
                             s)) in
                             if ?_clock s = 0 then (Rerr (Rabort
                               Rtimeout_error),s') else (Rval
                               exps,s')) else ((Rerr (Rabort
                               Rtype_error):(closLang_exp
                               list
                               ,closSem_v)semanticPrimitives_result)
                               ,s)) | _19 -> (Rerr (Rabort
                               Rtype_error),s)) else (Rerr (Rabort
                               Rtype_error),s))) | _20 -> (Rerr
                               (Rabort Rtype_error),s)) | _21 ->
                               (Rerr (Rabort Rtype_error),s))`;;

(* HOL4 termination: \\ Induct_on ‘cs’ \\ rw [] \\ fs
   [const_size_def] \\ res_tac \\ pop_assum (qspec_then ‘t’
   assume_tac) \\ fs [] *)
let make_const_def = cake_define_wf
  `MEASURE const_size`
  `make_const (ConstInt i) = closSem_Number i /\
   make_const (ConstStr s) = closSem_ByteVector (MAP (n2w o ORD)
     (explode s)) /\
   make_const (ConstWord64 w) = closSem_Word64 w /\
   make_const (ConstCons t cs) = closSem_Block t (MAP make_const
     cs)`;;

let do_int_app_def = cake_define
  `closSem_do_int_app x1 x2 =
      match (x1,x2) with
        ((closLang_Const n),[]) -> SOME (closSem_Number n)
      | ((closLang_Add),[closSem_Number n1; closSem_Number n2]) ->
        SOME (closSem_Number (n1 + n2))
      | ((closLang_Sub),[closSem_Number n1; closSem_Number n2]) ->
        SOME (closSem_Number (n1 - n2))
      | ((closLang_Mult),[closSem_Number n1; closSem_Number n2]) ->
        SOME (closSem_Number (n1 * n2))
      | ((closLang_Div),[closSem_Number n1; closSem_Number n2]) ->
       (if n2 = 0 then NONE else SOME (closSem_Number (n1 / n2)))
      | ((closLang_Mod),[closSem_Number n1; closSem_Number n2]) ->
       (if n2 = 0 then NONE else SOME (closSem_Number (n1 % n2)))
      | (((LESS)),[closSem_Number n1; closSem_Number n2]) -> SOME
        (closSem_Boolv (n1 < n2))
      | ((closLang_LessEq),[closSem_Number n1; closSem_Number n2]) ->
        SOME (closSem_Boolv (n1 <= n2))
      | (((GREATER)),[closSem_Number n1; closSem_Number n2]) -> SOME
        (closSem_Boolv (n1 > n2))
      | ((closLang_GreaterEq),[closSem_Number n1; closSem_Number n2])
        -> SOME (closSem_Boolv (n1 >= n2))
      | ((closLang_LessConstSmall n),[closSem_Number i]) ->
         (if 0 <= i /\ i <= 1000000 /\ n < 1000000 then
           SOME (closSem_Boolv (i < &n)) else NONE)
      | ((flatLang_op:closLang_int_op),(vs:closSem_v list)) ->
        NONE`;;

let opw_lookup_def = cake_define
  `(opw_lookup backend_common_Andw = word_and) /\
   (opw_lookup backend_common_Orw = word_or) /\
   (opw_lookup backend_common_Xor = word_xor) /\
   (opw_lookup closLang_Add = word_add) /\
   (opw_lookup closLang_Sub = word_sub)`;;

let do_word_app_def = cake_define
  `closSem_do_word_app x1 ws =
        match (x1,ws) with
          ((WordOpw ast_W8 opw),[closSem_Number n1; closSem_Number
            n2]) ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (closSem_Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw closLang_W64 opw),[closSem_Word64 w1;
          closSem_Word64 w2]) ->
           SOME (closSem_Word64 (opw_lookup opw w1 w2))
        | ((WordTest ast_W8 test),[closSem_Number n1; closSem_Number
          n2]) ->
          (if 0 <= n1 /\ n1 < 256 /\ 0 <= n2 /\ n2 < 256 then
             (match test with (EQUAL) -> SOME (closSem_Boolv (n1 =
               n2)) | ast_Compare cmp -> SOME (closSem_Boolv
               (semanticPrimitives_int_cmp cmp n1 n2)) | _22 -> NONE)
               else NONE)
        | ((WordShift ast_W8 sh n),[closSem_Number i]) ->
          (match some (\(w:word8). i = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (closSem_Number (&(w2n (shift_lookup sh w
            n)))))
        | ((WordShift closLang_W64 sh n),[closSem_Word64 w]) ->
          SOME (closSem_Word64 (shift_lookup sh w n))
        | ((WordFromInt),[closSem_Number i]) ->
          SOME (closSem_Word64 (i2w i))
        | (WordToInt,[closSem_Word64 w]) ->
          SOME (closSem_Number (&(w2n w)))
        | ((WordFromWord T),[closSem_Word64 w]) ->
          SOME (closSem_Number (&(w2n ((w2w:word64->word8) w))))
        | ((WordFromWord F),[closSem_Number n]) ->
          (match some (\(w:word8). n = &(w2n w)) with NONE -> NONE |
            SOME w -> SOME (closSem_Word64 (w2w w)))
        | ((FP_top t_op),ws) ->
           (match ws with [closSem_Word64 w1; closSem_Word64 w2;
             closSem_Word64 w3] ->
                (SOME (closSem_Word64 (fp_top_comp t_op w1 w2 w3))) |
                  _23 -> NONE)
        | ((FP_bop bop),ws) ->
           (match ws with [closSem_Word64 w1; closSem_Word64 w2] ->
             (SOME (closSem_Word64 (fp_bop_comp bop w1 w2))) | _24 ->
             NONE)
        | ((FP_uop uop),ws) ->
           (match ws with [closSem_Word64 w] -> (SOME (closSem_Word64
             (fp_uop_comp uop w))) | _25 -> NONE)
        | ((FP_cmp cmp),ws) ->
           (match ws with [closSem_Word64 w1; closSem_Word64 w2] ->
             (SOME (closSem_Boolv (fp_cmp_comp cmp w1 w2))) | _26 ->
             NONE)
        | ((flatLang_op:closLang_word_op),(vs:closSem_v list)) ->
          NONE`;;

let closSem_dest_thunk_ret_INDUCT,closSem_dest_thunk_ret_RECURSION =
  define_datatype
  "closSem_dest_thunk_ret = closSem_BadRef | closSem_NotThunk | \
   closSem_IsThunk (thunk_mode) (closSem_v)";;

let dest_thunk_def = cake_define
  `closSem_dest_thunk vs refs =
      match vs with
        [closSem_RefPtr b ptr] ->
     (match FLOOKUP refs ptr with NONE -> closSem_BadRef | SOME
       (closSem_Thunk Evaluated closSem_v) ->
          (if b then closSem_BadRef else closSem_IsThunk Evaluated
            closSem_v) | SOME (closSem_Thunk NotEvaluated closSem_v) ->
          (if b then closSem_BadRef else closSem_IsThunk NotEvaluated
            closSem_v) | SOME _27 -> closSem_NotThunk)
      | vs -> closSem_NotThunk`;;

let store_thunk_def = cake_define
  `store_thunk ptr closSem_v refs =
     (match FLOOKUP refs ptr with SOME (closSem_Thunk NotEvaluated
       _28) -> SOME (refs |+ (ptr,closSem_v)) | _29 -> NONE)`;;

let update_thunk_def = cake_define
  `closSem_update_thunk x1 refs x3 =
      match (x1,x3) with
        ([closSem_RefPtr F ptr],[closSem_v]) ->
     (match closSem_dest_thunk [closSem_v] refs with closSem_NotThunk
       -> store_thunk ptr (closSem_Thunk Evaluated closSem_v) refs | _30
       -> NONE)
      | (_31,_32) -> NONE`;;

let bad_thunk_update_def = cake_define
  `closSem_bad_thunk_update m closSem_v refs <=>
     m = Evaluated /\ ~(closSem_dest_thunk [closSem_v] refs =
       closSem_NotThunk)`;;

let do_app_def = cake_define
  `^
     (semanticPrimitives_do_app (flatLang_op:closLang_op)
       (vs:closSem_v list)) s =
       (match (flatLang_op,vs) with (closLang_GlobOp (Global
         n),([]:closSem_v list)) ->
           (match get_global n (closSem_state_globals s) with SOME
             (SOME closSem_v) -> (Rval (closSem_v,s)) | _33 -> ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_GlobOp
             (Global _34),[closSem_Number i]) ->
           (if i < 0 then ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) else
            match get_global (num_of_int i) (closSem_state_globals s)
              with SOME (SOME closSem_v) -> (Rval (closSem_v,s)) | _35
              -> ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | (closLang_GlobOp
              (SetGlobal n),[closSem_v]) ->
           (match get_global n (closSem_state_globals s) with SOME
             NONE -> Rval (closSem_Unit,closSem_state_globals_fupd (K
             (LUPDATE (SOME closSem_v) n (closSem_state_globals s)))
                s) | _36 -> ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result)) |
                  (closLang_GlobOp AllocGlobal,[closSem_Number i]) ->
           (if i < 0 then ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) else Rval
             (closSem_Unit,closSem_state_globals_fupd (K
             (closSem_state_globals s ++ REPLICATE (num_of_int i) NONE))
             s)) | (closLang_BlockOp (closLang_Constant c),[]) -> Rval
             (make_const c,s) | (closLang_BlockOp (closLang_Cons
             tag),xs) -> Rval (closSem_Block tag xs,s) |
             (closLang_BlockOp (closLang_ConsExtend tag),closSem_Block
             _37 xs' :: closSem_Number lower :: closSem_Number len ::
             closSem_Number tot :: xs) ->
           (if lower < 0 \/ len < 0 \/ &LENGTH xs' < lower + len \/
              tot = 0 \/ ~(tot = &LENGTH xs + len) then
             ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result) else
             Rval (closSem_Block tag (xs ++ TAKE (num_of_int len)
               (DROP (num_of_int lower) xs')),s)) | (closLang_BlockOp
               (closLang_ConsExtend tag),_38) -> ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result) | (closLang_MemOp
               flatLang_El,[closSem_Block tag xs; closSem_Number i]) ->
           (if 0 <= i /\ num_of_int i < LENGTH xs then Rval (EL
             (num_of_int i) xs,s) else ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
             flatLang_El,[closSem_RefPtr _39 ptr; closSem_Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME
             (closSem_ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval (EL
                 (num_of_int i) xs,s) else ((Rerr (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) | _40 -> ((Rerr
                 (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) |
                 (closLang_BlockOp (closLang_BoolTest test),[v1; v2]) ->
           (if (~(v1 = closSem_Boolv T) /\ ~(v1 = closSem_Boolv F))
             then ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) else
            if (~(v2 = closSem_Boolv T) /\ ~(v2 = closSem_Boolv F))
              then ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result) else
              Rval (closSem_Boolv (v1 = v2),s)) | (closLang_BlockOp
                closLang_BoolNot,[v1]) ->
           (if v1 = closSem_Boolv T then Rval (closSem_Boolv F,s)
             else
            if v1 = closSem_Boolv F then Rval (closSem_Boolv T,s)
              else ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
              (closLang_ElemAt n),[closSem_Block tag xs]) ->
           (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
             closLang_ListAppend,[x1; x2]) ->
           (match (closSem_v_to_list x1,closSem_v_to_list x2) with
             (SOME xs,SOME ys) -> Rval (closSem_list_to_v (xs ++ ys),s)
             | _41 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
             closLang_LengthBlock,[closSem_Block tag xs]) ->
           Rval (closSem_Number (&LENGTH xs),s) | (closLang_MemOp
             closLang_Length,[closSem_RefPtr _42 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME
             (closSem_ValueArray xs) ->
                 Rval (closSem_Number (&LENGTH xs),s) | _43 -> ((Rerr
                   (Rabort
                   Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                   ,closSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp closLang_LengthByte,[closSem_RefPtr
                   _44 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (closSem_ByteArray
             xs) ->
                 Rval (closSem_Number (&LENGTH xs),s) | _45 -> ((Rerr
                   (Rabort
                   Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                   ,closSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp (closLang_RefByte F),[closSem_Number
                   i; closSem_Number b]) ->
            (if 0 <= i /\ (?(w:word8). b = &(w2n w)) then
              let ptr = (minimal (\ptr. ~(ptr IN FDOM (?_refs s))))
                in
                Rval (closSem_RefPtr T ptr,?_refs_fupd (K (?_refs s
                  |+
                  (ptr,closSem_ByteArray (REPLICATE (num_of_int i)
                    (i2w b))))) s) else ((Rerr (Rabort
                    Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                    ,closSem_v)semanticPrimitives_result)) |
                    (closLang_MemOp closLang_RefArray,[closSem_Number i;
                    closSem_v]) ->
           (if 0 <= i then
             let ptr = (minimal (\ptr. ~(ptr IN FDOM (?_refs s)))) in
               Rval (closSem_RefPtr T ptr,?_refs_fupd (K (?_refs s |+
                 (ptr,closSem_ValueArray (REPLICATE (num_of_int i)
                   closSem_v)))) s) else ((Rerr (Rabort
                   Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                   ,closSem_v)semanticPrimitives_result)) |
                   (closLang_MemOp closLang_DerefByte,[closSem_RefPtr
                   _46 ptr; closSem_Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (closSem_ByteArray
             ws) ->
               (if 0 <= i /\ i < &LENGTH ws then Rval (closSem_Number
                 (&(w2n (EL (num_of_int i) ws))),s) else ((Rerr (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) | _47 -> ((Rerr
                 (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) |
                 (closLang_MemOp closLang_UpdateByte,[closSem_RefPtr _48
                 ptr; closSem_Number i; closSem_Number b]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (closSem_ByteArray
             bs) ->
               (if 0 <= i /\ i < &LENGTH bs /\ (?(w:word8). b = &(w2n
                 w)) then
                  Rval (closSem_Unit,?_refs_fupd (K (?_refs s |+
                    (ptr,closSem_ByteArray (LUPDATE (i2w b)
                      (num_of_int i) bs)))) s) else ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) | _49 ->
                      ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) |
                      (closLang_MemOp closLang_ConcatByteVec,[lv]) ->
           (match (some (\wss. closSem_v_to_list lv = SOME (MAP
             closSem_ByteVector wss))) with SOME wss -> Rval
             (closSem_ByteVector (FLAT wss),s) | _50 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
             (closLang_FromList n),[lv]) ->
           (match closSem_v_to_list lv with SOME vs -> Rval
             (closSem_Block n vs,s) | _51 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
             closLang_FromListByte,[lv]) ->
           (match some (\ns. closSem_v_to_list lv = SOME (MAP
             (closSem_Number o &) ns) /\ EVERY (\n. n < 256) ns) with
             SOME ns -> Rval (closSem_ByteVector (MAP n2w ns),s) | NONE
             -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
             closLang_ToListByte,[closSem_ByteVector bs]) ->
           (Rval (closSem_list_to_v (MAP (\b. closSem_Number (&(w2n
             b))) bs),s)) | (closLang_MemOp
             closLang_LengthByteVec,[closSem_ByteVector bs]) ->
           (Rval (closSem_Number (&LENGTH bs),s)) | (closLang_MemOp
             closLang_DerefByteVec,[closSem_ByteVector bs;
             closSem_Number i]) ->
           (if 0 <= i /\ i < &LENGTH bs then
              Rval (closSem_Number (&(w2n (EL (num_of_int i) bs))),s)
                else ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
                (closLang_CopyByte F),[closSem_ByteVector ws;
                closSem_Number srcoff; closSem_Number len;
                closSem_RefPtr _52 dst; closSem_Number dstoff]) ->
           (match FLOOKUP (?_refs s) dst with SOME (closSem_ByteArray
             ds) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff))
                with SOME ds -> Rval (closSem_Unit,?_refs_fupd (K
                (?_refs s |+ (dst,closSem_ByteArray ds))) s) | NONE ->
                ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | _53 -> ((Rerr
                (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
                (closLang_CopyByte F),[closSem_RefPtr _54 src;
                closSem_Number srcoff; closSem_Number len;
                closSem_RefPtr _55 dst; closSem_Number dstoff]) ->
           (match (FLOOKUP (?_refs s) src,FLOOKUP (?_refs s) dst)
             with (SOME (closSem_ByteArray ws),SOME (closSem_ByteArray
             ds)) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff))
                with SOME ds -> Rval (closSem_Unit,?_refs_fupd (K
                (?_refs s |+ (dst,closSem_ByteArray ds))) s) | NONE ->
                ((Rerr (Rabort
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
            (closLang_CopyByte T),[closSem_RefPtr _58 src;
            closSem_Number srcoff; closSem_Number len]) ->
          (match FLOOKUP (?_refs s) src with SOME (closSem_ByteArray
            ws) ->
             (match copy_array (ws,srcoff) len NONE with SOME ds ->
               Rval (closSem_ByteVector ds,s) | _59 -> ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | _60 -> ((Rerr
               (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
               closLang_XorByte,[closSem_RefPtr _61 dst;
               closSem_ByteVector ws]) ->
          (match FLOOKUP (?_refs s) dst with SOME (closSem_ByteArray
            ds) ->
             (match xor_bytes ws ds with SOME ds1 -> Rval
               (closSem_Unit,?_refs_fupd (K (?_refs s |+
               (dst,closSem_ByteArray ds1))) s) | _62 -> ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | _63 -> ((Rerr
               (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
               (closLang_StringCmp b cmp),[closSem_ByteVector b1;
               closSem_ByteVector b2]) ->
          (let s1 = implode (MAP (CHR o w2n) b1) in
           let s2 = implode (MAP (CHR o w2n) b2) in
             Rval (closSem_Boolv (str_cmp b cmp s1 s2),s)) |
               (closLang_BlockOp (closLang_TagEq n),[closSem_Block tag
               xs]) ->
           Rval (closSem_Boolv (tag = n),s) | (closLang_BlockOp
             (flatLang_LenEq l),[closSem_Block tag xs]) ->
           Rval (closSem_Boolv (LENGTH xs = l),s) | (closLang_BlockOp
             (flatLang_TagLenEq n l),[closSem_Block tag xs]) ->
           Rval (closSem_Boolv (tag = n /\ LENGTH xs = l),s) |
             (closLang_BlockOp (closLang_EqualConst p),[x1]) ->
           (match p with closLang_Int i -> (match x1 with
             closSem_Number j -> Rval (closSem_Boolv (i = j),s) | _64 ->
             ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | closLang_W64 i ->
             (match x1 with closSem_Word64 j -> Rval (closSem_Boolv (i =
             j),s) | _65 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | closLang_Str i ->
             (match x1 with closSem_ByteVector j -> Rval (closSem_Boolv
             (j = MAP (n2w o ORD) (explode i)),s) | _66 -> ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | _67 -> ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_BlockOp
             (EQUAL),[x1; x2]) ->
           (match closSem_do_eq x1 x2 with Eq_val b -> Rval
             (closSem_Boolv b,s) | _68 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_MemOp
             closLang_Ref,xs) ->
           (let ptr = (minimal (\ptr. ~(ptr IN FDOM (?_refs s)))) in
             Rval (closSem_RefPtr T ptr,?_refs_fupd (K (?_refs s |+
               (ptr,closSem_ValueArray xs))) s)) | (closLang_MemOp
               closLang_Update,[closSem_RefPtr _69 ptr; closSem_Number
               i; x]) ->
           (match FLOOKUP (?_refs s) ptr with SOME
             (closSem_ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval
                 (closSem_Unit,?_refs_fupd (K (?_refs s |+
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
           (match closSem_do_word_app word_op' vs with SOME res ->
             Rval (res,s) | _72 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (closLang_FFI
             n,[closSem_ByteVector conf; closSem_RefPtr _73 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (closSem_ByteArray
             ws) ->
              (match call_FFI (?_ffi s) (ExtCall n) conf ws with
                FFI_return ffi' ws' ->
                   Rval (closSem_Unit,?_ffi_fupd (K ffi')
                     (?_refs_fupd (K (?_refs s |+ (ptr,closSem_ByteArray
                     ws')))
                         s)) | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome))) | _74 ->
                     ((Rerr (Rabort
                     Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                     ,closSem_v)semanticPrimitives_result)) |
                     (closLang_BlockOp
                     closLang_BoundsCheckBlock,[closSem_Block tag ys;
                     closSem_Number i]) ->
           Rval (closSem_Boolv (0 <= i /\ i < &LENGTH ys),s) |
             (closLang_MemOp (closLang_BoundsCheckByte
             loose),[closSem_ByteVector bs; closSem_Number i]) ->
           Rval (closSem_Boolv (0 <= i /\ (if loose then (<=) else
             (<)) i (&LENGTH bs)),s) | (closLang_MemOp
             (closLang_BoundsCheckByte loose),[closSem_RefPtr _75 ptr;
             closSem_Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (closSem_ByteArray
             ws) ->
                Rval (closSem_Boolv (0 <= i /\ (if loose then (<=)
                  else (<)) i (&LENGTH ws)),s) | _76 -> ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp
                  closLang_BoundsCheckArray,[closSem_RefPtr _77 ptr;
                  closSem_Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME
             (closSem_ValueArray ws) ->
                Rval (closSem_Boolv (0 <= i /\ i < &LENGTH ws),s) |
                  _78 -> ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result)) |
                  (closLang_MemOp closLang_ConfigGC,[closSem_Number _79;
                  closSem_Number _80]) -> (Rval (closSem_Unit,s)) |
                  (closLang_ThunkOp th_op,vs) ->
           (match (th_op,vs) with (AllocThunk m,[closSem_v]) ->
                (if closSem_bad_thunk_update m closSem_v (?_refs s)
                  then ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result) else
                 let ptr = (minimal (\ptr. ~(ptr IN FDOM (?_refs
                   s)))) in
                   Rval (closSem_RefPtr F ptr,?_refs_fupd (K (?_refs
                     s |+ (ptr,closSem_Thunk m closSem_v))) s)) |
                     (UpdateThunk m,[closSem_RefPtr F ptr; closSem_v])
                     ->
                (if closSem_bad_thunk_update m closSem_v (?_refs s)
                  then ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result) else
                 match FLOOKUP (?_refs s) ptr with SOME
                   (closSem_Thunk NotEvaluated _81) ->
                    Rval (closSem_Unit,?_refs_fupd (K (?_refs s |+
                      (ptr,closSem_Thunk m closSem_v))) s) | _82 ->
                      ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) | _83 ->
                      ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) | _84 ->
                      ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result))`;;

let dec_clock_def = cake_define
  `^
     (dec_clock n) s = ?_clock_fupd (K (?_clock s - n)) s`;;

let find_code_def = cake_define
  `closSem_find_code p args code =
     (match FLOOKUP code p with NONE -> NONE | SOME
       (arity,flatLang_exp) -> (if LENGTH args = arity then SOME
       (args,flatLang_exp) else NONE))`;;

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

(* Proving termination of the evaluator directly is tricky. We make
   our life simpler by forcing the clock to stay good using
   fix_clock. At the bottom of this file, we remove all occurrences
   of fix_clock. *)

let fix_clock_def = cake_define
  `closSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of clos_exp expressions. *)

let check_loc_def = cake_define
  `(check_loc (max_app:num) NONE loc num_params num_args so_far <=>
     num_args <= max_app) /\
   (check_loc max_app (SOME p) loc num_params num_args so_far <=>
     num_params = num_args /\ so_far = (0:num) /\ SOME p = loc)`;;

let app_kind_INDUCT,app_kind_RECURSION = define_datatype
  "app_kind = Partial_app (closSem_v) | Full_app (closLang_exp) \
   (closSem_v list) (closSem_v list)";;

let dest_closure_def = cake_define
  `dest_closure max_app loc_opt f' args =
     (match f' with closSem_Closure loc arg_env clo_env num_args
       flatLang_exp ->
         (if check_loc max_app loc_opt loc num_args (LENGTH args)
           (LENGTH arg_env) /\ LENGTH arg_env < num_args then
           if ~(LENGTH args + LENGTH arg_env < num_args) then
             SOME (Full_app flatLang_exp
                            (REVERSE (TAKE (num_args - LENGTH
                              arg_env) (REVERSE args)) ++
                             arg_env ++ clo_env)
                            (REVERSE (DROP (num_args - LENGTH
                              arg_env) (REVERSE args)))) else
             SOME (Partial_app (closSem_Closure loc (args ++ arg_env)
               clo_env num_args flatLang_exp)) else
           NONE) | closSem_Recclosure loc arg_env clo_env fns i ->
         (let (num_args,flatLang_exp) = EL i fns in
           if LENGTH fns <= i \/
              ~check_loc max_app
                         loc_opt
                         (OPTION_MAP ((+) (2 * i)) loc) num_args
                         (LENGTH args)
                         (LENGTH arg_env) \/
              ~(LENGTH arg_env < num_args) then NONE else
             let rs = GENLIST (closSem_Recclosure loc [] clo_env fns)
               (LENGTH fns) in
               if ~(LENGTH args + LENGTH arg_env < num_args) then
                 SOME (Full_app flatLang_exp
                              (REVERSE (TAKE (num_args - LENGTH
                                arg_env) (REVERSE args)) ++
                              arg_env ++ rs ++ clo_env)
                              (REVERSE (DROP (num_args - LENGTH
                                arg_env) (REVERSE args)))) else
                 SOME (Partial_app (closSem_Recclosure loc (args
                   ++ arg_env) clo_env fns i))) | _85 -> NONE)`;;

let clos_env_def = cake_define
  `clos_env restrict names env =
     (if restrict then lookup_vars names env else SOME env)`;;

let build_recc_def = cake_define
  `build_recc restrict loc env names fns =
     (match clos_env restrict names env with SOME env1 -> SOME
       (GENLIST (closSem_Recclosure loc [] env1 fns) (LENGTH fns)) |
       NONE -> NONE)`;;

let AppUnit_def = cake_define
  `closSem_AppUnit x = closLang_App backend_common_None NONE x
  [closLang_Op backend_common_None (closLang_BlockOp (closLang_Cons
  0)) []]`;;

let exp_alt_size_def = cake_define
  `closSem_exp_alt_size x1 =
      match x1 with
        (closLang_Var a0 a1) -> 1 + (tra_size a0 + a1)
      | (flatLang_If a0 a1 a2 a3) ->
   1 + (tra_size a0 + (closSem_exp_alt_size a1 +
     (closSem_exp_alt_size a2 + closSem_exp_alt_size a3)))
      | (flatLang_Let a0 a1 a2) ->
   1 + (tra_size a0 + (closSem_exp3_alt_size a1 +
     closSem_exp_alt_size a2))
      | (flatLang_Raise a0 a1) -> 1 + (tra_size a0 +
        closSem_exp_alt_size a1)
      | (flatLang_Handle a0 a1 a2) ->
   1 + (tra_size a0 + (closSem_exp_alt_size a1 + closSem_exp_alt_size
     a2))
      | (closLang_Tick a0 a1) -> 1 + (tra_size a0 +
        closSem_exp_alt_size a1)
      | (closLang_Call a0 a1 a2 a3) ->
   1 + (tra_size a0 + (a1 + (a2 + closSem_exp3_alt_size a3)))
      | (flatLang_App a0 a1 a2 a3) ->
   1 +
   (tra_size a0 + (option_size (\x. x) a1 + (closSem_exp_alt_size a2
     + closSem_exp3_alt_size a3)))
      | (closLang_Fn a0 a1 a2 a3 a4) ->
   1 +
   (mlstring_size a0 +
    (option_size (\x. x) a1 +
     (option_size (list_size (\x. x)) a2 + (a3 + closSem_exp_alt_size
       a4))))
      | (flatLang_Letrec a0 a1 a2 a3 a4) ->
   1 +
   (list_size mlstring_size a0 +
    (option_size (\x. x) a1 +
     (option_size (list_size (\x. x)) a2 + (closSem_exp1_alt_size a3
       + closSem_exp_alt_size a4))))
      | (closLang_Op a0 a1 a2) ->
     1 + (tra_size a0 + (op_size a1 + closSem_exp3_alt_size a2)) +
       (if a1 = closLang_ThunkOp ForceThunk then 100 else 0)
      | [] -> 0
      | (a0 :: a1) -> 1 + (closSem_exp2_alt_size a0 +
        closSem_exp1_alt_size a1)
      | (a0,a1) -> 1 + (a0 + closSem_exp_alt_size a1)
      | [] -> 0
      | (a0 :: a1) -> 1 + (closSem_exp_alt_size a0 +
        closSem_exp3_alt_size a1)`;;

(* HOL4 termination: \\ rpt strip_tac \\ simp[dec_clock_def] \\
   imp_res_tac fix_clock_IMP \\ FULL_SIMP_TAC (srw_ss()) [] \\ TRY
   DECIDE_TAC \\ imp_res_tac do_install_clock \\ imp_res_tac
   dest_closure_length \\ imp_res_tac LESS_EQ_dec_clock \\
   FULL_SIMP_TAC (srw_ss()) [] \\ simp [AppUnit_def] \\ IF_CASES_TAC
   \\ gvs [] *)
let evaluate_def = cake_define_wf
  `(inv_image (MEASURE I LEX MEASURE I LEX MEASURE I)
                   (\x. match x with INL (xs,env,s) -> (?_clock
                     s,list_size closSem_exp_alt_size xs,0) | INR
                     (l,f',args,s) -> (?_clock s,0,LENGTH args)))`
  `(closSem_evaluate ([],(env:closSem_v list),s) = (Rval [],s)) /\
   (closSem_evaluate (x :: y :: xs,env,s) =
      (match closSem_fix_clock s (closSem_evaluate ([x],env,s)) with
        (Rval v1,s1) ->
          (match closSem_evaluate (y :: xs,env,s1) with (Rval vs,s2)
            -> (Rval (HD v1 :: vs),s2) | res -> res) | res -> res)) /\
   (closSem_evaluate ([closLang_Var _86 n],env,s) =
      (if n < LENGTH env then (Rval [EL n env],s) else (Rerr (Rabort
        Rtype_error),s))) /\
   (closSem_evaluate ([flatLang_If _87 x1 x2 x3],env,s) =
      (match closSem_fix_clock s (closSem_evaluate ([x1],env,s)) with
        (Rval vs,s1) ->
           (if closSem_Boolv T = HD vs then closSem_evaluate
             ([x2],env,s1) else
           if closSem_Boolv F = HD vs then closSem_evaluate
             ([x3],env,s1) else
             (Rerr (Rabort Rtype_error),s1)) | res -> res)) /\
   (closSem_evaluate ([flatLang_Let _88 xs x2],env,s) =
      (match closSem_fix_clock s (closSem_evaluate (xs,env,s)) with
        (Rval vs,s1) -> closSem_evaluate ([x2],vs ++ env,s1) | res ->
        res)) /\
   (closSem_evaluate ([flatLang_Raise _89 x1],env,s) =
      (match closSem_evaluate ([x1],env,s) with (Rval vs,s) -> (Rerr
        (Rraise (HD vs)),s) | res -> res)) /\
   (closSem_evaluate ([flatLang_Handle _90 x1 x2],env,s1) =
      (match closSem_fix_clock s1 (closSem_evaluate ([x1],env,s1))
        with (Rerr (Rraise closSem_v),s) -> closSem_evaluate
        ([x2],closSem_v :: env,s) | res -> res)) /\
   (closSem_evaluate ([closLang_Op _91 flatLang_op xs],env,s) =
      (match closSem_fix_clock s (closSem_evaluate (xs,env,s)) with
        (Rval vs,s) ->
        (if flatLang_op = closLang_Install then
        (match do_install (REVERSE vs) s with (Rval es,s) ->
             (match closSem_evaluate (es,[],s) with (Rval vs,s) ->
               (Rval [LAST vs],s) | res -> res) | (Rerr err,s) -> (Rerr
               err,s)) else if flatLang_op = closLang_ThunkOp ForceThunk
               then
          (match closSem_dest_thunk vs (?_refs s) with closSem_BadRef
            -> (Rerr (Rabort Rtype_error),s) | closSem_NotThunk -> (Rerr
            (Rabort Rtype_error),s) | closSem_IsThunk Evaluated
            closSem_v -> (Rval [closSem_v],s) | closSem_IsThunk
            NotEvaluated f' ->
              (match closSem_evaluate ([closSem_AppUnit (closLang_Var
                backend_common_None 0)],[f'],s) with (Rval vs2,s) ->
                  (match closSem_update_thunk vs (?_refs s) vs2 with
                    NONE -> (Rerr (Rabort Rtype_error),s) | SOME refs ->
                    (Rval vs2,?_refs_fupd (K refs) s)) | (Rerr e,s) ->
                    (Rerr e,s))) else
        (match semanticPrimitives_do_app flatLang_op (REVERSE vs) s
          with Rerr err -> (Rerr err,s) | Rval (closSem_v,s) -> (Rval
          [closSem_v],s))) | res -> res)) /\
   (closSem_evaluate ([closLang_Fn _92 loc vsopt num_args
     flatLang_exp],env,s) =
      (if num_args <= closSem_state_max_app s /\ ~(num_args = 0) then
        match vsopt with NONE -> (Rval [closSem_Closure loc [] env
          num_args flatLang_exp],s) | SOME vs ->
            (match lookup_vars vs env with NONE -> (Rerr (Rabort
              Rtype_error),s) | SOME env' -> (Rval [closSem_Closure loc
              [] env' num_args flatLang_exp],s)) else
        (Rerr (Rabort Rtype_error),s))) /\
   (closSem_evaluate ([flatLang_Letrec _93 loc namesopt fns
     flatLang_exp],env,s) =
      (if EVERY (\(num_args,e). num_args <= closSem_state_max_app s
        /\ ~(num_args = 0)) fns then
        let
          build_rc e = GENLIST (closSem_Recclosure loc [] e fns)
            (LENGTH fns) in
        let
          envdelta =
            match namesopt with NONE -> SOME (build_rc env) | SOME
              names -> OPTION_MAP build_rc (lookup_vars names env) in
          match envdelta with
              NONE -> (Rerr (Rabort Rtype_error),s) | SOME ed ->
                closSem_evaluate ([flatLang_exp],ed ++ env,s) else
        (Rerr (Rabort Rtype_error),s))) /\
   (closSem_evaluate ([flatLang_App _94 loc_opt x1 args],env,s) =
      (if LENGTH args > 0 then
        (match closSem_fix_clock s (closSem_evaluate (args,env,s))
          with (Rval y2,s1) ->
           (match closSem_fix_clock s1 (closSem_evaluate
             ([x1],env,s1)) with (Rval y1,s2) -> evaluate_app loc_opt
             (HD y1) y2 s2 | res -> res) | res -> res) else
        (Rerr (Rabort Rtype_error),s))) /\
   (closSem_evaluate ([closLang_Tick _95 x],env,s) =
      (if ?_clock s = 0 then (Rerr (Rabort Rtimeout_error),s) else
        closSem_evaluate ([x],env,dec_clock 1 s))) /\
   (closSem_evaluate ([closLang_Call _96 ticks dest xs],env,s1) =
      (match closSem_fix_clock s1 (closSem_evaluate (xs,env,s1)) with
        (Rval vs,s) ->
          (match closSem_find_code dest vs (closSem_state_code s)
            with NONE -> (Rerr (Rabort Rtype_error),s) | SOME
            (args,flatLang_exp) ->
               (if (?_clock s < ticks + 1) then (Rerr (Rabort
                 Rtimeout_error),?_clock_fupd (K 0) s) else
                   closSem_evaluate ([flatLang_exp],args,dec_clock
                     (ticks + 1) s))) | res -> res)) /\
   (evaluate_app loc_opt f' [] s = (Rval [f'],s)) /\
   (evaluate_app loc_opt f' args s =
      (match dest_closure (closSem_state_max_app s) loc_opt f' args
        with NONE -> (Rerr (Rabort Rtype_error),s) | SOME (Partial_app
        closSem_v) ->
          (if ?_clock s < LENGTH args then (Rerr (Rabort
            Rtimeout_error),?_clock_fupd (K 0) s) else (Rval
            [closSem_v],dec_clock (LENGTH args) s)) | SOME (Full_app
            flatLang_exp env rest_args) ->
          (if ?_clock s < (LENGTH args - LENGTH rest_args) then (Rerr
            (Rabort Rtimeout_error),?_clock_fupd (K 0) s) else
              match closSem_fix_clock (dec_clock (LENGTH args -
                LENGTH rest_args) s)
                     (closSem_evaluate ([flatLang_exp],env,dec_clock
                       (LENGTH args - LENGTH rest_args) s)) with (Rval
                       [closSem_v],s1) ->
                evaluate_app loc_opt closSem_v rest_args s1 | res
                  -> res)))`;;

(* We prove that the clock never increases. *)

(* Finally, we remove fix_clock from the induction and definition
   theorems. *)

(* observational semantics *)

let initial_state_def = cake_define
  `closSem_initial_state ffi ma code co cc k = mk_closSem_state []
  FEMPTY ffi k cc co code ma`;;

let semantics_def = cake_define
  `closSem_semantics ffi ma code co cc es =
     (let st = closSem_initial_state ffi ma code co cc in
       if ?k. FST (closSem_evaluate (es,[],st k)) = Rerr (Rabort
         Rtype_error) then ffi_Fail else
       match some (\res.
         ?k r s outcome.
           closSem_evaluate (es,[],st k) = (r,s) /\
           (match r with Rerr (Rabort Rtimeout_error) -> F | Rerr
             (Rabort (Rffi_error e)) -> outcome = ffi_FFI_outcome e |
             _97 -> outcome = ffi_Success) /\
           res = ffi_Terminate outcome (ffi_state_io_events (?_ffi
             s))) with SOME res -> res | NONE ->
          ffi_Diverge
            (build_lprefix_lub
              (IMAGE (\k. fromList (ffi_state_io_events (?_ffi
                 (SND (closSem_evaluate (es,[],st k)))))) UNIV)))`;;
