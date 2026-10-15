(* ======================================================== *)
(*  closSem: ported from HOL4's
    compiler/backend/semantics/closSemScript.sml  *)
(* ======================================================== *)

(*
  The formal semantics of closLang
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/comparison.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
(* HOL4 ancestors outside the port: (* for opw_lookup_def and others
   *) *)

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

let boolv_def = cake_define
  `(closSem_Boolv b = Block (if b then true_tag else false_tag) [])`;;
hol4_overload "Boolv" "closSem_Boolv";;

let do_eq_def = cake_define_list
  [`closSem_do_eq x y =
         (match x with Number i ->
             (match y with Number j -> Eq_val (i = j) | _1 ->
               Eq_type_error) | Word64 v ->
             (match y with Word64 w -> Eq_val (v = w) | _2 ->
               Eq_type_error) | Block t1 xs ->
             (match y with Block t2 ys -> (if (t1 = t2) /\ (LENGTH
               xs = LENGTH ys) then
                              closSem_do_eq_list xs ys else Eq_val
                                F) | _3 -> Eq_type_error) | ByteVector
                                cs ->
             (match y with ByteVector ds -> Eq_val (cs = ds) | _4 ->
               Eq_type_error) | RefPtr bi i ->
             (match y with RefPtr bj j -> (if bi /\ bj then Eq_val
               (i = j) else Eq_type_error) | _5 -> Eq_type_error) | _6
               ->
             (match y with Number _7 -> Eq_type_error | Word64 _8
               -> Eq_type_error | Block _9 _10 -> Eq_type_error |
               ByteVector _11 -> Eq_type_error | RefPtr _12 _13 ->
               Eq_type_error | _14 -> Eq_val T))`;
   `closSem_do_eq_list [] [] = Eq_val T`;
   `closSem_do_eq_list (x :: xs) (y :: ys) =
         (match closSem_do_eq x y with Eq_val T ->
           closSem_do_eq_list xs ys | res -> res)`;
   `closSem_do_eq_list _15 _16 = Eq_val F`];;
hol4_overload "do_eq" "closSem_do_eq";;
hol4_overload "do_eq_list" "closSem_do_eq_list";;

let v_to_list_def = cake_define
  `closSem_v_to_list x1 =
        match x1 with
          Block tag [] ->
        (if tag = nil_tag then SOME [] else NONE)
        | (Block tag [h; bt]) ->
        (if tag = cons_tag then
          (match closSem_v_to_list bt with SOME t -> SOME (h :: t) |
            _17 -> NONE) else NONE)
        | _18 -> NONE`;;
hol4_overload "v_to_list" "closSem_v_to_list";;

let list_to_v_def = cake_define_list
  [`closSem_list_to_v [] = Block nil_tag []`;
   `closSem_list_to_v (x :: xs) = Block cons_tag [x;
  closSem_list_to_v xs]`];;
hol4_overload "list_to_v" "closSem_list_to_v";;

let unit_def = cake_define
  `closSem_Unit = Block tuple_tag []`;;
hol4_overload "Unit" "closSem_Unit";;

(* HOL4 overload (expanded in the port):
     Error = (Rerr(Rabort Rtype_error)):(closSem$v#(('c,'ffi)
       closSem$state), closSem$v)result *)

let v_to_bytes_def = cake_define
  `closSem_v_to_bytes lv = some (\(ns:word8 list).
                     v_to_list lv = SOME (MAP (Number o (&) o w2n)
                       ns))`;;
hol4_overload "v_to_bytes" "closSem_v_to_bytes";;

let v_to_words_def = cake_define
  `closSem_v_to_words lv = some (\ns. v_to_list lv = SOME (MAP Word64
  ns))`;;
hol4_overload "v_to_words" "closSem_v_to_words";;

(* HOL4 ML code, not ported:
val s = ``s:('c,'ffi)closSem$state``;
*)

let do_install_def = cake_define
  `(\x y. strcat x y)
     (do_install vs) s =
         (match vs with [v1; v2] ->
              (match (v_to_bytes v1,v_to_words v2) with (SOME
                bytes,SOME data) ->
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

let make_const_def = cake_define_list
  [`make_const (ConstInt i) = Number i`;
   `make_const (ConstStr s) = ByteVector (MAP (n2w o ORD) (explode
  s))`;
   `make_const (ConstWord64 w) = Word64 w`;
   `make_const (ConstCons t cs) = Block t (MAP make_const cs)`];;

let do_int_app_def = cake_define
  `closSem_do_int_app x1 x2 =
      match (x1,x2) with
        (Const n,[]) -> SOME (Number n)
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
      | ((op:closLang_int_op),(vs:closSem_v list)) -> NONE`;;
hol4_overload "do_int_app" "closSem_do_int_app";;

let opw_lookup_def = cake_define_list
  [`opw_lookup Andw = word_and`;
   `opw_lookup Orw = word_or`;
   `opw_lookup Xor = word_xor`;
   `opw_lookup Add = word_add`;
   `opw_lookup Sub = word_sub`];;

let do_word_app_def = cake_define
  `closSem_do_word_app x1 ws =
        match (x1,ws) with
          (WordOpw W8 opw,[Number n1; Number n2]) ->
          (match some (\((w1:word8),(w2:word8)). n1 = &(w2n w1) /\ n2
            = &(w2n w2)) with NONE -> NONE | SOME (w1,w2) -> SOME
            (Number (&(w2n (opw_lookup opw w1 w2)))))
        | ((WordOpw W64 opw),[Word64 w1; Word64 w2]) ->
           SOME (Word64 (opw_lookup opw w1 w2))
        | ((WordTest W8 test),[Number n1; Number n2]) ->
          (if 0 <= n1 /\ n1 < 256 /\ 0 <= n2 /\ n2 < 256 then
             (match test with Equal -> SOME (Boolv (n1 = n2)) |
               Compare cmp -> SOME (Boolv (int_cmp cmp n1 n2)) | _22 ->
               NONE) else NONE)
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

let dest_thunk_def = cake_define
  `closSem_dest_thunk vs refs =
      match vs with
        [RefPtr b ptr] ->
     (match FLOOKUP refs ptr with NONE -> BadRef | SOME (Thunk
       Evaluated v) ->
          (if b then BadRef else IsThunk Evaluated v) | SOME (Thunk
            NotEvaluated v) ->
          (if b then BadRef else IsThunk NotEvaluated v) | SOME _27
            -> NotThunk)
      | vs -> NotThunk`;;
hol4_overload "dest_thunk" "closSem_dest_thunk";;

let store_thunk_def = cake_define
  `store_thunk ptr v refs =
     (match FLOOKUP refs ptr with SOME (Thunk NotEvaluated _28) ->
       SOME (refs |+ (ptr,v)) | _29 -> NONE)`;;

let update_thunk_def = cake_define
  `closSem_update_thunk x1 refs x3 =
      match (x1,x3) with
        ([RefPtr F ptr],[v]) ->
     (match dest_thunk [v] refs with NotThunk -> store_thunk ptr
       (Thunk Evaluated v) refs | _30 -> NONE)
      | (_31,_32) -> NONE`;;
hol4_overload "update_thunk" "closSem_update_thunk";;

let bad_thunk_update_def = cake_define
  `closSem_bad_thunk_update m v refs <=>
     m = Evaluated /\ ~(dest_thunk [v] refs = NotThunk)`;;
hol4_overload "bad_thunk_update" "closSem_bad_thunk_update";;

let do_app_def = cake_define
  `(\x y. strcat x y)
     (do_app (op:closLang_op) (vs:closSem_v list)) s =
       (match (op,vs) with (GlobOp (Global n),([]:closSem_v list)) ->
           (match get_global n (closSem_state_globals s) with SOME
             (SOME v) -> (Rval (v,s)) | _33 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (GlobOp (Global
             _34),[Number i]) ->
           (if i < 0 then ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) else
            match get_global (num_of_int i) (closSem_state_globals s)
              with SOME (SOME v) -> (Rval (v,s)) | _35 -> ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | (GlobOp
              (SetGlobal n),[v]) ->
           (match get_global n (closSem_state_globals s) with SOME
             NONE -> Rval (Unit,closSem_state_globals_fupd (K (LUPDATE
             (SOME v) n (closSem_state_globals s)))
                s) | _36 -> ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result)) | (GlobOp
                  AllocGlobal,[Number i]) ->
           (if i < 0 then ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) else Rval
             (Unit,closSem_state_globals_fupd (K (closSem_state_globals
             s ++ REPLICATE (num_of_int i) NONE)) s)) | (BlockOp
             (Constant c),[]) -> Rval (make_const c,s) | (BlockOp (Cons
             tag),xs) -> Rval (Block tag xs,s) | (BlockOp (ConsExtend
             tag),Block _37 xs' :: Number lower :: Number len :: Number
             tot :: xs) ->
           (if lower < 0 \/ len < 0 \/ &(LENGTH xs') < lower + len \/
              tot = 0 \/ ~(tot = &(LENGTH xs) + len) then
             ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result) else
             Rval (Block tag (xs ++ TAKE (num_of_int len) (DROP
               (num_of_int lower) xs')),s)) | (BlockOp (ConsExtend
               tag),_38) -> ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result) | (MemOp El,[Block
               tag xs; Number i]) ->
           (if 0 <= i /\ num_of_int i < LENGTH xs then Rval (EL
             (num_of_int i) xs,s) else ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (MemOp El,[RefPtr
             _39 ptr; Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval (EL
                 (num_of_int i) xs,s) else ((Rerr (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) | _40 -> ((Rerr
                 (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) | (BlockOp
                 (BoolTest test),[v1; v2]) ->
           (if (~(v1 = Boolv T) /\ ~(v1 = Boolv F)) then ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result) else
            if (~(v2 = Boolv T) /\ ~(v2 = Boolv F)) then ((Rerr
              (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result) else
              Rval (Boolv (v1 = v2),s)) | (BlockOp BoolNot,[v1]) ->
           (if v1 = Boolv T then Rval (Boolv F,s) else
            if v1 = Boolv F then Rval (Boolv T,s) else ((Rerr (Rabort
              Rtype_error)):(closSem_v#('c,'ffi)closSem_state
              ,closSem_v)semanticPrimitives_result)) | (BlockOp (ElemAt
              n),[Block tag xs]) ->
           (if n < LENGTH xs then Rval (EL n xs,s) else ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (BlockOp
             ListAppend,[x1; x2]) ->
           (match (v_to_list x1,v_to_list x2) with (SOME xs,SOME ys)
             -> Rval (list_to_v (xs ++ ys),s) | _41 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (BlockOp
             LengthBlock,[Block tag xs]) ->
           Rval (Number (&(LENGTH xs)),s) | (MemOp Length,[RefPtr _42
             ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ValueArray xs) ->
                 Rval (Number (&(LENGTH xs)),s) | _43 -> ((Rerr
                   (Rabort
                   Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                   ,closSem_v)semanticPrimitives_result)) | (MemOp
                   LengthByte,[RefPtr _44 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ByteArray xs) ->
                 Rval (Number (&(LENGTH xs)),s) | _45 -> ((Rerr
                   (Rabort
                   Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                   ,closSem_v)semanticPrimitives_result)) | (MemOp
                   (RefByte F),[Number i; Number b]) ->
            (if 0 <= i /\ (?(w:word8). b = &(w2n w)) then
              let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s)))) in
                Rval (RefPtr T ptr,?_refs_fupd (K (?_refs s |+
                  (ptr,ByteArray (REPLICATE (num_of_int i) (i2w
                    b))))) s) else ((Rerr (Rabort
                    Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                    ,closSem_v)semanticPrimitives_result)) | (MemOp
                    RefArray,[Number i; v]) ->
           (if 0 <= i then
             let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s)))) in
               Rval (RefPtr T ptr,?_refs_fupd (K (?_refs s |+
                 (ptr,ValueArray (REPLICATE (num_of_int i) v)))) s)
                   else ((Rerr (Rabort
                   Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                   ,closSem_v)semanticPrimitives_result)) | (MemOp
                   DerefByte,[RefPtr _46 ptr; Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ByteArray ws) ->
               (if 0 <= i /\ i < &(LENGTH ws) then Rval (Number
                 (&(w2n (EL (num_of_int i) ws))),s) else ((Rerr (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) | _47 -> ((Rerr
                 (Rabort
                 Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                 ,closSem_v)semanticPrimitives_result)) | (MemOp
                 UpdateByte,[RefPtr _48 ptr; Number i; Number b]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ByteArray bs) ->
               (if 0 <= i /\ i < &(LENGTH bs) /\ (?(w:word8). b =
                 &(w2n w)) then
                  Rval (Unit,?_refs_fupd (K (?_refs s |+
                    (ptr,ByteArray (LUPDATE (i2w b) (num_of_int i)
                      bs)))) s) else ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) | _49 ->
                      ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) | (MemOp
                      ConcatByteVec,[lv]) ->
           (match (some (\wss. v_to_list lv = SOME (MAP ByteVector
             wss))) with SOME wss -> Rval (ByteVector (FLAT wss),s) |
             _50 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (BlockOp (FromList
             n),[lv]) ->
           (match v_to_list lv with SOME vs -> Rval (Block n vs,s) |
             _51 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (MemOp
             FromListByte,[lv]) ->
           (match some (\ns. v_to_list lv = SOME (MAP (Number o (&))
             ns) /\ EVERY (\n. n < 256) ns) with SOME ns -> Rval
             (ByteVector (MAP n2w ns),s) | NONE -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (MemOp
             ToListByte,[ByteVector bs]) ->
           (Rval (list_to_v (MAP (\b. Number (&(w2n b))) bs),s)) |
             (MemOp LengthByteVec,[ByteVector bs]) ->
           (Rval (Number (&(LENGTH bs)),s)) | (MemOp
             DerefByteVec,[ByteVector bs; Number i]) ->
           (if 0 <= i /\ i < &(LENGTH bs) then
              Rval (Number (&(w2n (EL (num_of_int i) bs))),s) else
                ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | (MemOp
                (CopyByte F),[ByteVector ws; Number srcoff; Number len;
                RefPtr _52 dst; Number dstoff]) ->
           (match FLOOKUP (?_refs s) dst with SOME (ByteArray ds) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff))
                with SOME ds -> Rval (Unit,?_refs_fupd (K (?_refs s |+
                (dst,ByteArray ds))) s) | NONE -> ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | _53 -> ((Rerr
                (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | (MemOp
                (CopyByte F),[RefPtr _54 src; Number srcoff; Number len;
                RefPtr _55 dst; Number dstoff]) ->
           (match (FLOOKUP (?_refs s) src,FLOOKUP (?_refs s) dst)
             with (SOME (ByteArray ws),SOME (ByteArray ds)) ->
              (match copy_array (ws,srcoff) len (SOME (ds,dstoff))
                with SOME ds -> Rval (Unit,?_refs_fupd (K (?_refs s |+
                (dst,ByteArray ds))) s) | NONE -> ((Rerr (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | _56 -> ((Rerr
                (Rabort
                Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                ,closSem_v)semanticPrimitives_result)) | (MemOp
                (CopyByte T),[ByteVector ws; Number srcoff; Number len])
                ->
          (match copy_array (ws,srcoff) len NONE with SOME ds -> Rval
            (ByteVector ds,s) | _57 -> ((Rerr (Rabort
            Rtype_error)):(closSem_v#('c,'ffi)closSem_state
            ,closSem_v)semanticPrimitives_result)) | (MemOp (CopyByte
            T),[RefPtr _58 src; Number srcoff; Number len]) ->
          (match FLOOKUP (?_refs s) src with SOME (ByteArray ws) ->
             (match copy_array (ws,srcoff) len NONE with SOME ds ->
               Rval (ByteVector ds,s) | _59 -> ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | _60 -> ((Rerr
               (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | (MemOp
               XorByte,[RefPtr _61 dst; ByteVector ws]) ->
          (match FLOOKUP (?_refs s) dst with SOME (ByteArray ds) ->
             (match xor_bytes ws ds with SOME ds1 -> Rval
               (Unit,?_refs_fupd (K (?_refs s |+ (dst,ByteArray ds1)))
               s) | _62 -> ((Rerr (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | _63 -> ((Rerr
               (Rabort
               Rtype_error)):(closSem_v#('c,'ffi)closSem_state
               ,closSem_v)semanticPrimitives_result)) | (MemOp
               (StringCmp b cmp),[ByteVector b1; ByteVector b2]) ->
          (let s1 = implode (MAP (CHR o w2n) b1) in
           let s2 = implode (MAP (CHR o w2n) b2) in
             Rval (Boolv (str_cmp b cmp s1 s2),s)) | (BlockOp (TagEq
               n),[Block tag xs]) ->
           Rval (Boolv (tag = n),s) | (BlockOp (LenEq l),[Block tag
             xs]) ->
           Rval (Boolv (LENGTH xs = l),s) | (BlockOp (TagLenEq n
             l),[Block tag xs]) ->
           Rval (Boolv (tag = n /\ LENGTH xs = l),s) | (BlockOp
             (EqualConst p),[x1]) ->
           (match p with Int i -> (match x1 with Number j -> Rval
             (Boolv (i = j),s) | _64 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | W64 i -> (match x1
             with Word64 j -> Rval (Boolv (i = j),s) | _65 -> ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | Str i -> (match x1
             with ByteVector j -> Rval (Boolv (j = MAP (n2w o ORD)
             (explode i)),s) | _66 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | _67 -> ((Rerr
             (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (BlockOp
             Equal,[x1; x2]) ->
           (match do_eq x1 x2 with Eq_val b -> Rval (Boolv b,s) | _68
             -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (MemOp Ref,xs) ->
           (let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s)))) in
             Rval (RefPtr T ptr,?_refs_fupd (K (?_refs s |+
               (ptr,ValueArray xs))) s)) | (MemOp Update,[RefPtr _69
               ptr; Number i; x]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ValueArray xs) ->
               (if 0 <= i /\ i < &(LENGTH xs) then Rval
                 (Unit,?_refs_fupd (K (?_refs s |+
                              (ptr,ValueArray (LUPDATE x (num_of_int
                                i) xs)))) s) else ((Rerr (Rabort
                                Rtype_error)):(closSem_v#('c
                                ,'ffi)closSem_state
                                ,closSem_v)semanticPrimitives_result)) |
                                _70 -> ((Rerr (Rabort
                                Rtype_error)):(closSem_v#('c
                                ,'ffi)closSem_state
                                ,closSem_v)semanticPrimitives_result)) |
                                (IntOp int_op',vs) ->
           (match do_int_app int_op' vs with SOME res -> Rval (res,s)
             | _71 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (WordOp
             word_op',vs) ->
           (match do_word_app word_op' vs with SOME res -> Rval
             (res,s) | _72 -> ((Rerr (Rabort
             Rtype_error)):(closSem_v#('c,'ffi)closSem_state
             ,closSem_v)semanticPrimitives_result)) | (FFI n,[ByteVector
             conf; RefPtr _73 ptr]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ByteArray ws) ->
              (match call_FFI (?_ffi s) (ExtCall n) conf ws with
                FFI_return ffi' ws' ->
                   Rval (Unit,?_ffi_fupd (K ffi') (?_refs_fupd (K
                     (?_refs s |+ (ptr,ByteArray ws')))
                         s)) | FFI_final outcome ->
                   Rerr (Rabort (Rffi_error outcome))) | _74 ->
                     ((Rerr (Rabort
                     Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                     ,closSem_v)semanticPrimitives_result)) | (BlockOp
                     BoundsCheckBlock,[Block tag ys; Number i]) ->
           Rval (Boolv (0 <= i /\ i < &(LENGTH ys)),s) | (MemOp
             (BoundsCheckByte loose),[ByteVector bs; Number i]) ->
           Rval (Boolv (0 <= i /\ (if loose then (<=) else (<)) i
             (&(LENGTH bs))),s) | (MemOp (BoundsCheckByte loose),[RefPtr
             _75 ptr; Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ByteArray ws) ->
                Rval (Boolv (0 <= i /\ (if loose then (<=) else (<))
                  i (&(LENGTH ws))),s) | _76 -> ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result)) | (MemOp
                  BoundsCheckArray,[RefPtr _77 ptr; Number i]) ->
           (match FLOOKUP (?_refs s) ptr with SOME (ValueArray ws) ->
                Rval (Boolv (0 <= i /\ i < &(LENGTH ws)),s) | _78 ->
                  ((Rerr (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result)) | (MemOp
                  ConfigGC,[Number _79; Number _80]) -> (Rval (Unit,s))
                  | (ThunkOp th_op,vs) ->
           (match (th_op,vs) with (AllocThunk m,[v]) ->
                (if bad_thunk_update m v (?_refs s) then ((Rerr
                  (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result) else
                 let ptr = (LEAST (\ptr. ~(ptr IN FDOM (?_refs s))))
                   in
                   Rval (RefPtr F ptr,?_refs_fupd (K (?_refs s |+
                     (ptr,Thunk m v))) s)) | (UpdateThunk m,[RefPtr F
                     ptr; v]) ->
                (if bad_thunk_update m v (?_refs s) then ((Rerr
                  (Rabort
                  Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                  ,closSem_v)semanticPrimitives_result) else
                 match FLOOKUP (?_refs s) ptr with SOME (Thunk
                   NotEvaluated _81) ->
                    Rval (Unit,?_refs_fupd (K (?_refs s |+
                      (ptr,Thunk m v))) s) | _82 -> ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) | _83 ->
                      ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result)) | _84 ->
                      ((Rerr (Rabort
                      Rtype_error)):(closSem_v#('c,'ffi)closSem_state
                      ,closSem_v)semanticPrimitives_result))`;;

let dec_clock_def = cake_define
  `(\x y. strcat x y)
     (dec_clock n) s = ?_clock_fupd (K (?_clock s - n)) s`;;

let find_code_def = cake_define
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

let fix_clock_def = cake_define
  `closSem_fix_clock s (res,s1) = (res,?_clock_fupd (K (MIN (?_clock
  s) (?_clock s1))) s1)`;;
hol4_overload "fix_clock" "closSem_fix_clock";;

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of clos_exp expressions. *)

let check_loc_def = cake_define_list
  [`check_loc (max_app:num) NONE loc num_params num_args so_far <=>
        num_args <= max_app`;
   `check_loc max_app (SOME p) loc num_params num_args so_far <=>
        num_params = num_args /\ so_far = (0:num) /\ SOME p = loc`];;

let app_kind_INDUCT,app_kind_RECURSION = define_datatype
  "app_kind = Partial_app (closSem_v) | Full_app (closLang_exp) \
   (closSem_v list) (closSem_v list)";;

let dest_closure_def = cake_define
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
             SOME (Partial_app (Closure loc (args ++ arg_env) clo_env
               num_args exp)) else
           NONE) | Recclosure loc arg_env clo_env fns i ->
         (let (num_args,exp) = EL i fns in
           if LENGTH fns <= i \/
              ~check_loc max_app
                         loc_opt
                         (OPTION_MAP ((+) (2 * i)) loc) num_args
                         (LENGTH args)
                         (LENGTH arg_env) \/
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
                 SOME (Partial_app (Recclosure loc (args ++
                   arg_env) clo_env fns i))) | _85 -> NONE)`;;

let clos_env_def = cake_define
  `clos_env restrict names env =
     (if restrict then lookup_vars names env else SOME env)`;;

let build_recc_def = cake_define
  `build_recc restrict loc env names fns =
     (match clos_env restrict names env with SOME env1 -> SOME
       (GENLIST (Recclosure loc [] env1 fns) (LENGTH fns)) | NONE ->
       NONE)`;;

let AppUnit_def = cake_define
  `closSem_AppUnit x = closLang_App None NONE x [Op None (BlockOp
  (Cons 0)) []]`;;
hol4_overload "AppUnit" "closSem_AppUnit";;

let exp_alt_size_def = cake_define_list
  [`closSem_exp_alt_size (Var a0 a1:flatLang_exp) = 1 + (tra_size a0
  + a1)`;
   `closSem_exp_alt_size (If a0 a1 a2 a3:flatLang_exp) =
    1 + (tra_size a0 + (closSem_exp_alt_size a1 +
      (closSem_exp_alt_size a2 + closSem_exp_alt_size a3)))`;
   `closSem_exp_alt_size (Let a0 a1 a2:flatLang_exp) =
    1 + (tra_size a0 + (closSem_exp3_alt_size a1 +
      closSem_exp_alt_size a2))`;
   `closSem_exp_alt_size (Raise a0 a1:flatLang_exp) = 1 + (tra_size
  a0 + closSem_exp_alt_size a1)`;
   `closSem_exp_alt_size (Handle a0 a1 a2:flatLang_exp) =
    1 + (tra_size a0 + (closSem_exp_alt_size a1 +
      closSem_exp_alt_size a2))`;
   `closSem_exp_alt_size (Tick a0 a1) = 1 + (tra_size a0 +
  closSem_exp_alt_size a1)`;
   `closSem_exp_alt_size (Call a0 a1 a2 a3) =
    1 + (tra_size a0 + (a1 + (a2 + closSem_exp3_alt_size a3)))`;
   `closSem_exp_alt_size (App a0 a1 a2 a3:flatLang_exp) =
    1 +
    (tra_size a0 + (option_size (\x. x) a1 +
      (closSem_exp_alt_size a2 + closSem_exp3_alt_size a3)))`;
   `closSem_exp_alt_size (Fn a0 a1 a2 a3 a4) =
    1 +
    (mlstring_size a0 +
     (option_size (\x. x) a1 +
      (option_size (list_size (\x. x)) a2 + (a3 +
        closSem_exp_alt_size a4))))`;
   `closSem_exp_alt_size (Letrec a0 a1 a2 a3 a4:flatLang_exp) =
    1 +
    (list_size mlstring_size a0 +
     (option_size (\x. x) a1 +
      (option_size (list_size (\x. x)) a2 +
        (closSem_exp1_alt_size a3 + closSem_exp_alt_size a4))))`;
   `closSem_exp_alt_size (Op a0 a1 a2) =
      1 + (tra_size a0 + (op_size a1 + closSem_exp3_alt_size a2))
        + (if a1 = ThunkOp ForceThunk then 100 else 0)`;
   `closSem_exp1_alt_size [] = 0`;
   `closSem_exp1_alt_size (a0 :: a1) = 1 + (closSem_exp2_alt_size a0
  + closSem_exp1_alt_size a1)`;
   `closSem_exp2_alt_size (a0,a1) = 1 + (a0 + closSem_exp_alt_size
  a1)`;
   `closSem_exp3_alt_size [] = 0`;
   `closSem_exp3_alt_size (a0 :: a1) = 1 + (closSem_exp_alt_size a0 +
  closSem_exp3_alt_size a1)`];;
hol4_overload "exp1_alt_size" "closSem_exp1_alt_size";;
hol4_overload "exp2_alt_size" "closSem_exp2_alt_size";;
hol4_overload "exp3_alt_size" "closSem_exp3_alt_size";;
hol4_overload "exp_alt_size" "closSem_exp_alt_size";;

let evaluate_def = cake_define_list
  [`closSem_evaluate ([],(env:closSem_v list),s) = (Rval [],s)`;
   `closSem_evaluate (x :: y :: xs,env,s) =
         (match fix_clock s (closSem_evaluate ([x],env,s)) with
           (Rval v1,s1) ->
             (match closSem_evaluate (y :: xs,env,s1) with (Rval
               vs,s2) -> (Rval (HD v1 :: vs),s2) | res -> res) | res
               -> res)`;
   `closSem_evaluate ([(Var _86 n:flatLang_exp)],env,s) =
         (if n < LENGTH env then (Rval [EL n env],s) else (Rerr
           (Rabort Rtype_error),s))`;
   `closSem_evaluate ([(If _87 x1 x2 x3:flatLang_exp)],env,s) =
         (match fix_clock s (closSem_evaluate ([x1],env,s)) with
           (Rval vs,s1) ->
              (if Boolv T = HD vs then closSem_evaluate
                ([x2],env,s1) else
              if Boolv F = HD vs then closSem_evaluate ([x3],env,s1)
                else
                (Rerr (Rabort Rtype_error),s1)) | res -> res)`;
   `closSem_evaluate ([(Let _88 xs x2:flatLang_exp)],env,s) =
         (match fix_clock s (closSem_evaluate (xs,env,s)) with
           (Rval vs,s1) -> closSem_evaluate ([x2],vs ++ env,s1) | res
           -> res)`;
   `closSem_evaluate ([(Raise _89 x1:flatLang_exp)],env,s) =
         (match closSem_evaluate ([x1],env,s) with (Rval vs,s) ->
           (Rerr (Rraise (HD vs)),s) | res -> res)`;
   `closSem_evaluate ([(Handle _90 x1 x2:flatLang_exp)],env,s1) =
         (match fix_clock s1 (closSem_evaluate ([x1],env,s1))
           with (Rerr (Rraise v),s) -> closSem_evaluate ([x2],v ::
           env,s) | res -> res)`;
   `closSem_evaluate ([Op _91 op xs],env,s) =
         (match fix_clock s (closSem_evaluate (xs,env,s)) with (Rval
           vs,s) ->
           (if op = Install then
           (match do_install (REVERSE vs) s with (Rval es,s) ->
                (match closSem_evaluate (es,[],s) with (Rval vs,s)
                  -> (Rval [LAST vs],s) | res -> res) | (Rerr err,s) ->
                  (Rerr err,s)) else if op = ThunkOp ForceThunk then
             (match dest_thunk vs (?_refs s) with BadRef -> (Rerr
               (Rabort Rtype_error),s) | NotThunk -> (Rerr (Rabort
               Rtype_error),s) | IsThunk Evaluated v -> (Rval [v],s) |
               IsThunk NotEvaluated f ->
                 (match closSem_evaluate ([AppUnit (Var None
                   0)],[f],s) with (Rval vs2,s) ->
                     (match update_thunk vs (?_refs s) vs2 with NONE
                       -> (Rerr (Rabort Rtype_error),s) | SOME refs ->
                       (Rval vs2,?_refs_fupd (K refs) s)) | (Rerr e,s)
                       -> (Rerr e,s))) else
           (match do_app op (REVERSE vs) s with Rerr err -> (Rerr
             err,s) | Rval (v,s) -> (Rval [v],s))) | res -> res)`;
   `closSem_evaluate ([Fn _92 loc vsopt num_args exp],env,s) =
         (if num_args <= closSem_state_max_app s /\ ~(num_args = 0)
           then
           match vsopt with NONE -> (Rval [Closure loc [] env
             num_args exp],s) | SOME vs ->
               (match lookup_vars vs env with NONE -> (Rerr (Rabort
                 Rtype_error),s) | SOME env' -> (Rval [Closure loc []
                 env' num_args exp],s)) else
           (Rerr (Rabort Rtype_error),s))`;
   `closSem_evaluate ([(Letrec _93 loc namesopt fns
  exp:flatLang_exp)],env,s) =
         (if EVERY (\(num_args,e). num_args <= closSem_state_max_app
           s /\ ~(num_args = 0)) fns then
           let
             build_rc e = GENLIST (Recclosure loc [] e fns) (LENGTH
               fns) in
           let
             envdelta =
               match namesopt with NONE -> SOME (build_rc env) |
                 SOME names -> OPTION_MAP build_rc (lookup_vars names
                 env) in
             match envdelta with
                 NONE -> (Rerr (Rabort Rtype_error),s) | SOME ed ->
                   closSem_evaluate ([exp],ed ++ env,s) else
           (Rerr (Rabort Rtype_error),s))`;
   `closSem_evaluate ([(App _94 loc_opt x1 args:flatLang_exp)],env,s) =
         (if LENGTH args > 0 then
           (match fix_clock s (closSem_evaluate (args,env,s)) with
             (Rval y2,s1) ->
              (match fix_clock s1 (closSem_evaluate ([x1],env,s1))
                with (Rval y1,s2) -> evaluate_app loc_opt (HD y1) y2 s2
                | res -> res) | res -> res) else
           (Rerr (Rabort Rtype_error),s))`;
   `closSem_evaluate ([Tick _95 x],env,s) =
         (if ?_clock s = 0 then (Rerr (Rabort Rtimeout_error),s)
           else closSem_evaluate ([x],env,dec_clock 1 s))`;
   `closSem_evaluate ([Call _96 ticks dest xs],env,s1) =
         (match fix_clock s1 (closSem_evaluate (xs,env,s1)) with
           (Rval vs,s) ->
             (match find_code dest vs (closSem_state_code s) with
               NONE -> (Rerr (Rabort Rtype_error),s) | SOME (args,exp)
               ->
                  (if (?_clock s < ticks + 1) then (Rerr (Rabort
                    Rtimeout_error),?_clock_fupd (K 0) s) else
                      closSem_evaluate ([exp],args,dec_clock
                        (ticks + 1) s))) | res -> res)`;
   `evaluate_app loc_opt f [] s = (Rval [f],s)`;
   `evaluate_app loc_opt f args s =
         (match dest_closure (closSem_state_max_app s) loc_opt f
           args with NONE -> (Rerr (Rabort Rtype_error),s) | SOME
           (Partial_app v) ->
             (if ?_clock s < LENGTH args then (Rerr (Rabort
               Rtimeout_error),?_clock_fupd (K 0) s) else (Rval
               [v],dec_clock (LENGTH args) s)) | SOME (Full_app exp env
               rest_args) ->
             (if ?_clock s < (LENGTH args - LENGTH rest_args) then
               (Rerr (Rabort Rtimeout_error),?_clock_fupd (K 0) s) else
                 match fix_clock (dec_clock (LENGTH args - LENGTH
                   rest_args) s)
                        (closSem_evaluate ([exp],env,dec_clock
                          (LENGTH args - LENGTH rest_args) s)) with
                          (Rval [v],s1) ->
                   evaluate_app loc_opt v rest_args s1 | res ->
                     res))`];;
hol4_overload "evaluate" "closSem_evaluate";;

(* We prove that the clock never increases. *)

(* Finally, we remove fix_clock from the induction and definition
   theorems. *)

(* observational semantics *)

let initial_state_def = cake_define
  `closSem_initial_state ffi ma code co cc k = mk_closSem_state []
  FEMPTY ffi k cc co code ma`;;
hol4_overload "initial_state" "closSem_initial_state";;

let semantics_def = cake_define
  `closSem_semantics ffi ma code co cc es =
     (let st = initial_state ffi ma code co cc in
       if ?k. FST (evaluate (es,[],st k)) = Rerr (Rabort Rtype_error)
         then Fail else
       match some (\res.
         ?k r s outcome.
           evaluate (es,[],st k) = (r,s) /\
           (match r with Rerr (Rabort Rtimeout_error) -> F | Rerr
             (Rabort (Rffi_error e)) -> outcome = FFI_outcome e | _97 ->
             outcome = Success) /\
           res = Terminate outcome (ffi_state_io_events (?_ffi s)))
             with SOME res -> res | NONE ->
          Diverge
            (build_lprefix_lub
              (IMAGE (\k. fromList (ffi_state_io_events (?_ffi
                 (SND (evaluate (es,[],st k)))))) UNIV)))`;;
hol4_overload "semantics" "closSem_semantics";;
