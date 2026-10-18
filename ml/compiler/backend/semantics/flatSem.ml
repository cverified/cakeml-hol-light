(* ======================================================== *)
(*  flatSem: ported from HOL4's
    compiler/backend/semantics/flatSemScript.sml
    A definition theory, with 40 definitions, 5 datatypes and 10
    theorems.  Needed by 5 files of the port.  *)
(* ======================================================== *)

(*
  The formal semantics of flatLang
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/flatLang.ml";;
needs "lib/comparison.ml";;
needs "lib/errorMonad.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* The values of flatLang differ from source semantic values in that
 * the closures do not carry environments for global definitions.
 *
 * The semantics of flatLang differ from source in that there is no
 * module environment menv, nor are top-level bindings added to the
 * normal env, thus when a closure is created, only locals bindings
 * are put into it. There is a global environment genv, which is just
 * a list of the top-level bindings seen so far, with the older
 * bindings nearer the head. Global variable reference expressions
 * simply index into global environment. Top-level let rec
 * declarations evaluate to closures, rather than to recursive
 * closures, since the recursion can be handled through the genv. The
 * expressions bound to top-level lets must evaluate to a tuple with
 * exactly as many things in it as the number of bindings that the let
 * will bind.
 *)

let flatSem_environment_FIELDS = define_record "flatSem_environment"
  ["v","(mlstring#'v) list"];;

let flatSem_v_INDUCT,flatSem_v_RECURSION = define_datatype
  "flatSem_v = flatSem_Litv (lit) | flatSem_Conv ((num#num option) \
   option) (flatSem_v list) | flatSem_Closure (flatSem_v \
   flatSem_environment) (mlstring) (flatLang_exp) | \
   flatSem_Recclosure (flatSem_v flatSem_environment) \
   ((mlstring#mlstring#flatLang_exp) list) (mlstring) | flatSem_Loc \
   (bool) (num) | flatSem_Vectorv (flatSem_v list)";;
hol4_overload "Litv" "flatSem_Litv";;
hol4_overload "Conv" "flatSem_Conv";;
hol4_overload "Closure" "flatSem_Closure";;
hol4_overload "Recclosure" "flatSem_Recclosure";;
hol4_overload "Loc" "flatSem_Loc";;
hol4_overload "Vectorv" "flatSem_Vectorv";;

let install_config_FIELDS = define_record "install_config"
  ["compile","'c->flatLang_exp list->(word8 list#word64 list#'c) \
   option";
   "compile_oracle","num->'c#flatLang_exp list"];;
hol4_field_overload "compile" "install_config_compile";;
hol4_field_overload "compile_fupd" "install_config_compile_fupd";;
hol4_field_overload "compile_oracle" "install_config_compile_oracle";;
hol4_field_overload "compile_oracle_fupd"
  "install_config_compile_oracle_fupd";;

let flatSem_state_FIELDS = define_record "flatSem_state"
  ["clock","num";
   "refs","(flatSem_v store_v) list";
   "ffi","'ffi ffi_state";
   "globals","(flatSem_v option) list";
   "eval_config","'c install_config"];;
hol4_field_overload "state_clock" "flatSem_state_clock";;
hol4_field_overload "state_clock_fupd" "flatSem_state_clock_fupd";;
hol4_field_overload "state_refs" "flatSem_state_refs";;
hol4_field_overload "state_refs_fupd" "flatSem_state_refs_fupd";;
hol4_field_overload "state_ffi" "flatSem_state_ffi";;
hol4_field_overload "state_ffi_fupd" "flatSem_state_ffi_fupd";;
hol4_field_overload "state_globals" "flatSem_state_globals";;
hol4_field_overload "state_globals_fupd" "flatSem_state_globals_fupd";;

(* HOL4 flatSemScript.sml:66: the ML values that the definitions
   below antiquote *)

let list_id_def = cake_define
  `list_id = 1`;;

let boolv_def = cake_define
  `flatSem_Boolv b = Conv (SOME ((if b then true_tag else
  false_tag),SOME bool_id)) []`;;
hol4_overload "Boolv" "flatSem_Boolv";;

let unitv_def = cake_define
  `Unitv = Conv NONE []`;;

let bind_exn_v_def = cake_define
  `flatSem_bind_exn_v = Conv (SOME (bind_tag,NONE)) []`;;
hol4_overload "bind_exn_v" "flatSem_bind_exn_v";;

let chr_exn_v_def = cake_define
  `flatSem_chr_exn_v = Conv (SOME (chr_tag,NONE)) []`;;
hol4_overload "chr_exn_v" "flatSem_chr_exn_v";;

let div_exn_v_def = cake_define
  `flatSem_div_exn_v = Conv (SOME (div_tag,NONE)) []`;;
hol4_overload "div_exn_v" "flatSem_div_exn_v";;

let subscript_exn_v_def = cake_define
  `subscript_exn_v = Conv (SOME (subscript_tag,NONE)) []`;;

let build_rec_env_def = cake_define
  `flatSem_build_rec_env funs cl_env add_to_env =
     ITLIST (\(f,x,e) env'. (f,Recclosure cl_env funs f) :: env')
       funs
       add_to_env`;;
hol4_overload "build_rec_env" "flatSem_build_rec_env";;

let ctor_same_type_def = cake_define
  `flatSem_ctor_same_type x1 x2 =
        match (x1,x2) with
          (SOME (_1,t),SOME (_2,t')) -> t = t'
        | (NONE,NONE) -> T
        | (_3,_4) -> F`;;
hol4_overload "ctor_same_type" "flatSem_ctor_same_type";;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let do_eq_def = cake_define_list_cheat CHEAT_TAC
  [`flatSem_do_eq (Litv l1:flatSem_v) (Litv l2:flatSem_v) =
       (if lit_same_type l1 l2 then Eq_val (l1 = l2) else
         Eq_type_error)`;
   `flatSem_do_eq (Loc b1 l1:flatSem_v) (Loc b2 l2:flatSem_v) =
        (if b1 /\ b2 then Eq_val (l1 = l2) else Eq_type_error)`;
   `flatSem_do_eq (Conv cn1 vs1:flatSem_v) (Conv cn2 vs2:flatSem_v) =
       (if (cn1 = cn2) /\ (LENGTH vs1 = LENGTH vs2) then
         flatSem_do_eq_list vs1 vs2 else if ctor_same_type cn1 cn2
           then
         Eq_val F else
         Eq_type_error)`;
   `flatSem_do_eq (Vectorv vs1:flatSem_v) (Vectorv vs2:flatSem_v) =
       (if LENGTH vs1 = LENGTH vs2 then
         flatSem_do_eq_list vs1 vs2 else
         Eq_val F)`;
   `flatSem_do_eq (Closure _11 _12 _13:flatSem_v) (Closure _14 _15
  _16:flatSem_v) = Eq_val T`;
   `flatSem_do_eq (Closure _23 _24 _25:flatSem_v) (Recclosure _26 _27
  _28:flatSem_v) = Eq_val T`;
   `flatSem_do_eq (Recclosure _35 _36 _37:flatSem_v) (Closure _38 _39
  _40:flatSem_v) = Eq_val T`;
   `flatSem_do_eq (Recclosure _47 _48 _49:flatSem_v) (Recclosure _50
  _51 _52:flatSem_v) = Eq_val T`;
   `flatSem_do_eq _53 _54 = Eq_type_error`;
   `flatSem_do_eq_list [] [] = Eq_val T`;
   `flatSem_do_eq_list (v1 :: vs1) (v2 :: vs2) =
       (match flatSem_do_eq v1 v2 with Eq_type_error ->
         Eq_type_error | Eq_val r ->
          (if r then
            flatSem_do_eq_list vs1 vs2 else
            Eq_val F))`;
   `flatSem_do_eq_list _55 _56 = Eq_val F`];;
hol4_overload "do_eq" "flatSem_do_eq";;
hol4_overload "do_eq_list" "flatSem_do_eq_list";;

(* Do an application *)
let do_opapp_def = cake_define
  `flatSem_do_opapp vs =
   (match vs with [Closure env n e; v] ->
       SOME (flatSem_environment_v_fupd (\env. (n,v) :: env) env,e) |
         [Recclosure env funs n; v] ->
       (if ALL_DISTINCT (MAP FST funs) then
         (match find_recfun n funs with SOME (n,e) -> SOME
           (flatSem_environment_v_fupd (K (
              (n,v) :: build_rec_env funs env
                (flatSem_environment_v env))) env,e) | NONE -> NONE)
                else NONE) | _57 -> NONE)`;;
hol4_overload "do_opapp" "flatSem_do_opapp";;

let v_to_list_def = cake_define
  `flatSem_v_to_list x1 =
        match x1 with
          (Conv (SOME (cid,tid)) []:flatSem_v) ->
      (if cid = nil_tag /\ tid = SOME list_id then
        SOME [] else NONE)
        | (Conv (SOME (cid,tid)) [v1; v2]) ->
      (if cid = cons_tag /\ tid = SOME list_id then
        (match flatSem_v_to_list v2 with SOME vs -> SOME (v1 :: vs) |
          NONE -> NONE) else NONE)
        | _58 -> NONE`;;
hol4_overload "v_to_list" "flatSem_v_to_list";;

let list_to_v_def = cake_define_list
  [`flatSem_list_to_v [] = Conv (SOME (nil_tag,SOME list_id)) []`;
   `flatSem_list_to_v (x :: xs) =
        Conv (SOME (cons_tag,SOME list_id)) [x;
          flatSem_list_to_v xs]`];;
hol4_overload "list_to_v" "flatSem_list_to_v";;

let v_to_char_list_def = cake_define
  `flatSem_v_to_char_list x1 =
        match x1 with
          (Conv (SOME (cid,tid)) []:flatSem_v) ->
     (if cid = nil_tag /\ tid = SOME list_id then
       SOME [] else NONE)
        | (Conv (SOME (cid,tid)) [Litv (ast_Char c); v]) ->
     (if cid = cons_tag /\ tid = SOME list_id then
       (match flatSem_v_to_char_list v with SOME cs -> SOME (c :: cs)
         | NONE -> NONE) else NONE)
        | _59 -> NONE`;;
hol4_overload "v_to_char_list" "flatSem_v_to_char_list";;

let vs_to_string_def = cake_define
  `flatSem_vs_to_string x1 =
        match x1 with
          [] -> SOME (implode "")
        | ((Litv (ast_StrLit s1):flatSem_v) :: vs) ->
      (match flatSem_vs_to_string vs with SOME s2 -> SOME ((\x y.
        strcat x y) s1 s2) | _60 -> NONE)
        | _61 -> NONE`;;
hol4_overload "vs_to_string" "flatSem_vs_to_string";;

let v_to_bytes_def = cake_define
  `flatSem_v_to_bytes lv = some (\ns. v_to_list lv = SOME (MAP (Litv
  o ast_Word8) ns))`;;
hol4_overload "v_to_bytes" "flatSem_v_to_bytes";;

let v_to_words_def = cake_define
  `flatSem_v_to_words lv = some (\ns. v_to_list lv = SOME (MAP (Litv
  o ast_Word64) ns))`;;
hol4_overload "v_to_words" "flatSem_v_to_words";;

let check_type_def = cake_define
  `flatSem_check_type x1 v =
      match x1 with
        ast_BoolT -> (v = Boolv T \/ v = Boolv F)
      | ast_IntT -> (?i. v = Litv (ast_IntLit i))
      | ast_CharT -> (?c. v = Litv (ast_Char c))
      | ast_StrT -> (?s. v = Litv (ast_StrLit s))
      | (ast_WordT ast_W8) -> (?w. v = Litv (ast_Word8 w))
      | (ast_WordT ast_W64) -> (?w. v = Litv (ast_Word64 w))
      | ast_Float64T -> (?w. v = Litv (ast_Float64 w))`;;
hol4_overload "check_type" "flatSem_check_type";;

let dest_Litv_def = cake_define
  `flatSem_dest_Litv x1 =
      match x1 with
        (Litv v:flatSem_v) -> SOME v
      | _62 -> NONE`;;
hol4_overload "dest_Litv" "flatSem_dest_Litv";;

let the_Litv_Float64_def = cake_define
  `flatSem_the_Litv_Float64 (Litv (ast_Float64 w):flatSem_v) = w`;;
hol4_overload "the_Litv_Float64" "flatSem_the_Litv_Float64";;

let do_test_def = cake_define_list
  [`flatSem_do_test (Equal:test) ty v1 v2 =
      (if check_type ty v1 /\ check_type ty v2 then
         (if ty = ast_Float64T then Eq_val (fp64_equal
           (the_Litv_Float64 v1) (the_Litv_Float64 v2)) else do_eq v1
           v2) else Eq_type_error)`;
   `flatSem_do_test (ast_Compare cmp) ty v1 v2 =
      (match (ty,dest_Litv v1,dest_Litv v2) with (ast_IntT,SOME
        (ast_IntLit i),SOME (ast_IntLit j)) -> Eq_val
        (semanticPrimitives_int_cmp cmp i j) | (ast_CharT,SOME
        (ast_Char c),SOME (ast_Char d)) -> Eq_val (num_cmp cmp (ORD
        c) (ORD d)) | (ast_WordT ast_W8,SOME (ast_Word8 w),SOME
        (ast_Word8 v)) -> Eq_val (num_cmp cmp (w2n w) (w2n v)) |
        (ast_Float64T,SOME (ast_Float64 w),SOME (ast_Float64 v)) ->
        Eq_val (fp_cmp cmp w v) | (ast_StrT,SOME (ast_StrLit s),SOME
        (ast_StrLit t)) -> Eq_val (str_cmp F cmp s t) | _65 ->
        Eq_type_error)`;
   `flatSem_do_test (ast_AltCompare cmp) ty v1 v2 =
      (match (ty,dest_Litv v1,dest_Litv v2) with (ast_StrT,SOME
        (ast_StrLit s),SOME (ast_StrLit t)) -> Eq_val (str_cmp T
        cmp s t) | _66 -> Eq_type_error)`];;
hol4_overload "do_test" "flatSem_do_test";;

let v_to_flat_def = cake_define
  `v_to_flat x1 =
      match x1 with
        semanticPrimitives_Litv v -> flatSem_Litv v
      | (Conv x y) ->
     (if Conv x y = Boolv T then Boolv T else
      if Conv x y = Boolv F then Boolv F else Vectorv [])
      | _67 -> Vectorv []`;;

let flat_to_v_def = cake_define
  `flat_to_v x1 =
      match x1 with
        flatSem_Litv v -> semanticPrimitives_Litv v
      | (Conv x y) ->
     (if Conv x y = Boolv T then Boolv T else
      if Conv x y = Boolv F then Boolv F else Vectorv [])
      | _68 -> Vectorv []`;;

let flatSem_dest_thunk_ret_INDUCT,flatSem_dest_thunk_ret_RECURSION =
  define_datatype
  "flatSem_dest_thunk_ret = flatSem_BadRef | flatSem_NotThunk | \
   flatSem_IsThunk (thunk_mode) (flatSem_v)";;
hol4_overload "BadRef" "flatSem_BadRef";;
hol4_overload "NotThunk" "flatSem_NotThunk";;
hol4_overload "IsThunk" "flatSem_IsThunk";;

let dest_thunk_def = cake_define
  `flatSem_dest_thunk vs st =
      match vs with
        [(Loc b n:flatSem_v)] ->
     (match store_lookup n st with NONE -> BadRef | SOME
       (semanticPrimitives_Thunk Evaluated v) ->
          (if b then BadRef else IsThunk Evaluated v) | SOME
            (semanticPrimitives_Thunk NotEvaluated v) ->
          (if b then BadRef else IsThunk NotEvaluated v) | SOME _69
            -> NotThunk)
      | vs -> NotThunk`;;
hol4_overload "dest_thunk" "flatSem_dest_thunk";;

let update_thunk_def = cake_define
  `flatSem_update_thunk x1 st x3 =
      match (x1,x3) with
        ([(Loc F n:flatSem_v)],[v]) ->
     (match dest_thunk [v] st with NotThunk -> store_assign n
       (semanticPrimitives_Thunk Evaluated v) st | _70 -> NONE)
      | (_71,_72) -> NONE`;;
hol4_overload "update_thunk" "flatSem_update_thunk";;

let bad_thunk_update_def = cake_define
  `flatSem_bad_thunk_update m v refs <=>
     m = Evaluated /\ ~(dest_thunk [v] refs = NotThunk)`;;
hol4_overload "bad_thunk_update" "flatSem_bad_thunk_update";;

let do_app_def = cake_define
  `flatSem_do_app s op (vs:flatSem_v list) =
   (match (op,vs) with (flatLang_Src (ast_Shift wz sh n),[Litv w]) ->
       (match do_shift sh n wz w with NONE -> NONE | SOME w -> SOME
         (s,Rval (Litv w))) | (flatLang_Src ast_Equality,[v1; v2]) ->
     (match do_eq v1 v2 with Eq_type_error -> NONE | Eq_val b -> SOME
       (s,Rval (Boolv b))) | (flatLang_Src (ast_Test test test_ty),[v1;
       v2]) ->
     (match do_test test test_ty v1 v2 with Eq_type_error -> NONE |
       Eq_val b -> SOME (s,Rval (Boolv b))) | (flatLang_Src (ast_Arith a
       ty),vs) ->
     (let vs = MAP flat_to_v vs in
        if EVERY (check_type ty) vs then
          (match do_arith a ty vs with SOME (INR res) -> SOME (s,Rval
            (v_to_flat res)) | SOME (INL exn) -> SOME (s,Rerr (Rraise
            div_exn_v)) | NONE -> NONE) else NONE) | (flatLang_Src
            (ast_FromTo ty1 ty2),[v]) ->
     (let v = flat_to_v v in
        if check_type ty1 v then
          (match do_conversion v ty1 ty2 with SOME (INR res) -> SOME
            (s,Rval (v_to_flat res)) | SOME (INL exn) -> SOME (s,Rerr
            (Rraise chr_exn_v)) | NONE -> NONE) else NONE) |
            (flatLang_Src ast_Opassign,[Loc _73 lnum; v]) ->
     (match store_assign lnum (semanticPrimitives_Refv v) (state_refs
       s) with SOME s' -> SOME (state_refs_fupd (K s') s,Rval Unitv) |
       NONE -> NONE) | (flatLang_Src ast_Opref,[v]) ->
     (let (s',n) = (store_alloc (semanticPrimitives_Refv v)
       (state_refs s)) in
       SOME (state_refs_fupd (K s') s,Rval (Loc T n))) |
         (flatLang_Src ast_Aw8alloc,[Litv (ast_IntLit n); Litv
         (ast_Word8 w)]) ->
     (if n < (&0) then
       SOME (s,Rerr (Rraise subscript_exn_v)) else
       let (s',lnum) =
         store_alloc (semanticPrimitives_W8array (REPLICATE
           (num_of_int (abs n)) w)) (state_refs s) in
         SOME (state_refs_fupd (K s') s,Rval (Loc T lnum))) |
           (flatLang_Src ast_Aw8sub,[Loc _74 lnum; Litv (ast_IntLit i)])
           ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_W8array ws) ->
        (if i < (&0) then
          SOME (s,Rerr (Rraise subscript_exn_v)) else
          let n = (num_of_int (abs i)) in
            if n >= LENGTH ws then
              SOME (s,Rerr (Rraise subscript_exn_v)) else
              SOME (s,Rval (Litv (ast_Word8 (EL n ws))))) | _75 ->
                NONE) | (flatLang_Src ast_Aw8sub_unsafe,[Loc _76 lnum;
                Litv (ast_IntLit i)]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_W8array ws) ->
        (if i < (&0) then
          NONE else
          let n = (num_of_int (abs i)) in
            if n >= LENGTH ws then
              NONE else
              SOME (s,Rval (Litv (ast_Word8 (EL n ws))))) | _77 ->
                NONE) | (flatLang_Src ast_Aw8length,[Loc _78 n]) ->
     (match store_lookup n (state_refs s) with SOME
       (semanticPrimitives_W8array ws) ->
        SOME (s,Rval (Litv (ast_IntLit (int_of_num (LENGTH ws))))) |
          _79 -> NONE) | (flatLang_Src ast_Aw8update,[Loc _80 lnum; Litv
          (ast_IntLit i); Litv (ast_Word8 w)]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_W8array ws) ->
        (if i < (&0) then
          SOME (s,Rerr (Rraise subscript_exn_v)) else
          let n = (num_of_int (abs i)) in
            if n >= LENGTH ws then
              SOME (s,Rerr (Rraise subscript_exn_v)) else
              (match store_assign lnum (semanticPrimitives_W8array
                (LUPDATE w n ws)) (state_refs s) with NONE -> NONE |
                SOME s' -> SOME (state_refs_fupd (K s') s,Rval Unitv)))
                | _81 -> NONE) | (flatLang_Src ast_Aw8update_unsafe,[Loc
                _82 lnum; Litv (ast_IntLit i); Litv (ast_Word8 w)]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_W8array ws) ->
        (if i < (&0) then
          NONE else
          let n = (num_of_int (abs i)) in
            if n >= LENGTH ws then
              NONE else
              (match store_assign lnum (semanticPrimitives_W8array
                (LUPDATE w n ws)) (state_refs s) with NONE -> NONE |
                SOME s' -> SOME (state_refs_fupd (K s') s,Rval Unitv)))
                | _83 -> NONE) | (flatLang_Src ast_CopyStrStr,[Litv
                (ast_StrLit str); Litv (ast_IntLit off); Litv
                (ast_IntLit len)]) ->
       SOME (s,
       (match copy_array (explode str,off) len NONE with
         NONE -> Rerr (Rraise subscript_exn_v) | SOME cs -> Rval
           (Litv (ast_StrLit (implode cs))))) | (flatLang_Src
           ast_CopyStrAw8,[Litv (ast_StrLit str); Litv (ast_IntLit off);
           Litv (ast_IntLit len);
                   Loc _84 dst; Litv (ast_IntLit dstoff)]) ->
       (match store_lookup dst (state_refs s) with
         SOME (semanticPrimitives_W8array ws) ->
           (match copy_array (explode str,off) len (SOME (ws_to_chars
             ws,dstoff)) with
             NONE -> SOME (s,Rerr (Rraise subscript_exn_v)) | SOME cs
               ->
             (match store_assign dst (semanticPrimitives_W8array
               (chars_to_ws cs)) (state_refs s) with
               SOME s' -> SOME (state_refs_fupd (K s') s,Rval Unitv)
                 | _85 -> NONE)) | _86 -> NONE) | (flatLang_Src
                 ast_CopyAw8Str,[Loc _87 src; Litv (ast_IntLit off);
                 Litv (ast_IntLit len)]) ->
     (match store_lookup src (state_refs s) with
       SOME (semanticPrimitives_W8array ws) ->
       SOME (s,
         (match copy_array (ws,off) len NONE with
           NONE -> Rerr (Rraise subscript_exn_v) | SOME ws -> Rval
             (Litv (ast_StrLit (implode (ws_to_chars ws)))))) | _88 ->
             NONE) | (flatLang_Src ast_CopyAw8Aw8,[Loc _89 src; Litv
             (ast_IntLit off); Litv (ast_IntLit len);
                   Loc _90 dst; Litv (ast_IntLit dstoff)]) ->
     (match (store_lookup src (state_refs s),store_lookup dst
       (state_refs s)) with
       (SOME (semanticPrimitives_W8array ws),SOME
         (semanticPrimitives_W8array ds)) ->
         (match copy_array (ws,off) len (SOME (ds,dstoff)) with
           NONE -> SOME (s,Rerr (Rraise subscript_exn_v)) | SOME ws
             ->
             (match store_assign dst (semanticPrimitives_W8array ws)
               (state_refs s) with
               SOME s' -> SOME (state_refs_fupd (K s') s,Rval Unitv)
                 | _91 -> NONE)) | _92 -> NONE) | (flatLang_Src
                 ast_XorAw8Str_unsafe,[Loc _93 dst; Litv (ast_StrLit
                 str_arg)]) ->
     (match store_lookup dst (state_refs s) with SOME
       (semanticPrimitives_W8array ds) ->
          (match xor_bytes (MAP (n2w o ORD) (explode str_arg)) ds
            with NONE -> NONE | SOME new_bs ->
               (match store_assign dst (semanticPrimitives_W8array
                 new_bs) (state_refs s) with NONE -> NONE | SOME s' ->
                 SOME (state_refs_fupd (K s') s,Rval Unitv))) | _94 ->
                 NONE) | (flatLang_Src ast_Implode,[v]) ->
     (match v_to_char_list v with SOME ls ->
        SOME (s,Rval (Litv (ast_StrLit (implode ls)))) | NONE ->
          NONE) | (flatLang_Src ast_Explode,[Litv (ast_StrLit str)]) ->
     (SOME (s,Rval (list_to_v (MAP (\c. Litv (ast_Char c)) (explode
       str))))) | (flatLang_Src ast_Strsub,[Litv (ast_StrLit str); Litv
       (ast_IntLit i)]) ->
     (if i < (&0) then
       SOME (s,Rerr (Rraise subscript_exn_v)) else
       let n = (num_of_int (abs i)) in
         if n >= strlen str then
           SOME (s,Rerr (Rraise subscript_exn_v)) else
           SOME (s,Rval (Litv (ast_Char (strsub str n))))) |
             (flatLang_Src ast_Strlen,[Litv (ast_StrLit str)]) ->
     SOME (s,Rval (Litv (ast_IntLit (int_of_num (strlen str))))) |
       (flatLang_Src ast_Strcat,[v]) ->
       (match v_to_list v with
         SOME vs ->
           (match vs_to_string vs with
             SOME str ->
               SOME (s,Rval (Litv (ast_StrLit str))) | _95 -> NONE) |
                 _96 -> NONE) | (flatLang_Src ast_VfromList,[v]) ->
     (match v_to_list v with SOME vs ->
        SOME (s,Rval (Vectorv vs)) | NONE -> NONE) | (flatLang_Src
          ast_Vsub,[Vectorv vs; Litv (ast_IntLit i)]) ->
     (if i < (&0) then
       SOME (s,Rerr (Rraise subscript_exn_v)) else
       let n = (num_of_int (abs i)) in
         if n >= LENGTH vs then
           SOME (s,Rerr (Rraise subscript_exn_v)) else
           SOME (s,Rval (EL n vs))) | (flatLang_Src
             ast_Vsub_unsafe,[Vectorv vs; Litv (ast_IntLit i)]) ->
     (if (&0) <= i /\ num_of_int i < LENGTH vs then
       SOME (s,Rval (EL (num_of_int i) vs)) else
       NONE) | (flatLang_Src ast_Vlength,[Vectorv vs]) ->
     SOME (s,Rval (Litv (ast_IntLit (int_of_num (LENGTH vs))))) |
       (flatLang_Src ast_Aalloc,[Litv (ast_IntLit n); v]) ->
     (if n < (&0) then
       SOME (s,Rerr (Rraise subscript_exn_v)) else
       let (s',lnum) =
         store_alloc (semanticPrimitives_Varray (REPLICATE
           (num_of_int (abs n)) v)) (state_refs s) in
         SOME (state_refs_fupd (K s') s,Rval (Loc T lnum))) |
           (flatLang_Src ast_AallocFixed,vs) ->
     (let (s',lnum) =
       store_alloc (semanticPrimitives_Varray vs) (state_refs s) in
       SOME (state_refs_fupd (K s') s,Rval (Loc T lnum))) |
         (flatLang_Src ast_Asub,[Loc _97 lnum; Litv (ast_IntLit i)]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_Varray vs) ->
      (if i < (&0) then
        SOME (s,Rerr (Rraise subscript_exn_v)) else
        let n = (num_of_int (abs i)) in
          if n >= LENGTH vs then
            SOME (s,Rerr (Rraise subscript_exn_v)) else
            SOME (s,Rval (EL n vs))) | _98 -> NONE) | (flatLang_Src
              ast_Asub_unsafe,[Loc _99 lnum; Litv (ast_IntLit i)]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_Varray vs) ->
      (if i < (&0) then
        NONE else
        let n = (num_of_int (abs i)) in
          if n >= LENGTH vs then
            NONE else
            SOME (s,Rval (EL n vs))) | _100 -> NONE) | (flatLang_Src
              ast_Alength,[Loc _101 n]) ->
       (match store_lookup n (state_refs s) with SOME
         (semanticPrimitives_Varray ws) ->
          SOME (s,Rval (Litv (ast_IntLit (int_of_num (LENGTH ws)))))
            | _102 -> NONE) | (flatLang_Src ast_Aupdate,[Loc _103 lnum;
            Litv (ast_IntLit i); v]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_Varray vs) ->
      (if i < (&0) then
        SOME (s,Rerr (Rraise subscript_exn_v)) else
        let n = (num_of_int (abs i)) in
          if n >= LENGTH vs then
            SOME (s,Rerr (Rraise subscript_exn_v)) else
            (match store_assign lnum (semanticPrimitives_Varray
              (LUPDATE v n vs)) (state_refs s) with NONE -> NONE | SOME
              s' -> SOME (state_refs_fupd (K s') s,Rval Unitv))) | _104
              -> NONE) | (flatLang_Src ast_Aupdate_unsafe,[Loc _105
              lnum; Litv (ast_IntLit i); v]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_Varray vs) ->
      (if i < (&0) then
        NONE else
        let n = (num_of_int (abs i)) in
          if n >= LENGTH vs then
            NONE else
            (match store_assign lnum (semanticPrimitives_Varray
              (LUPDATE v n vs)) (state_refs s) with NONE -> NONE | SOME
              s' -> SOME (state_refs_fupd (K s') s,Rval Unitv))) | _106
              -> NONE) | (flatLang_Src ast_ListAppend,[x1; x2]) ->
     (match (v_to_list x1,v_to_list x2) with (SOME xs,SOME ys) ->
       SOME (s,Rval (list_to_v (xs ++ ys))) | _107 -> NONE) |
       (flatLang_Src ast_ConfigGC,[Litv (ast_IntLit n1); Litv
       (ast_IntLit n2)]) ->
        SOME (s,Rval Unitv) | (flatLang_Src (ast_FFI n),[Litv
          (ast_StrLit conf); Loc _108 lnum]) ->
     (match store_lookup lnum (state_refs s) with SOME
       (semanticPrimitives_W8array ws) ->
        (match call_FFI (state_ffi s) (ffi_ExtCall n) (MAP (\c. n2w
          (ORD c)) (explode conf)) ws with FFI_final outcome -> SOME
          (s,Rerr (Rabort (Rffi_error outcome))) | FFI_return t' ws' ->
           (match store_assign lnum (semanticPrimitives_W8array ws')
             (state_refs s) with SOME s' -> SOME (state_ffi_fupd (K t')
             (state_refs_fupd (K s') s),Rval Unitv) | NONE -> NONE)) |
             _109 -> NONE) | (flatLang_Src ast_Opapp,_110) -> NONE |
             (flatLang_Src ast_Eval,_111) -> NONE | (flatLang_Src
             (ast_ThunkOp th_op),vs) ->
      (match (th_op,vs) with (AllocThunk m,[v]) ->
           (if bad_thunk_update m v (state_refs s) then NONE else
            let (r,n) = store_alloc (semanticPrimitives_Thunk m v)
              (state_refs s) in
              SOME (state_refs_fupd (K r) s,Rval (Loc F n))) |
                (UpdateThunk m,[Loc F lnum; v]) ->
           (if bad_thunk_update m v (state_refs s) then NONE else
            match store_assign lnum (semanticPrimitives_Thunk m v)
              (state_refs s) with SOME r -> SOME (state_refs_fupd (K r)
              s,Rval (Conv NONE [])) | NONE -> NONE) | _112 -> NONE) |
              (flatLang_Src _113,_114) -> NONE |
              (flatLang_GlobalVarAlloc n,[]) ->
     SOME (flatSem_state_globals_fupd (K (flatSem_state_globals s ++
       REPLICATE n NONE)) s,Rval Unitv) | (flatLang_GlobalVarInit n,[v])
       ->
     (if n < LENGTH (flatSem_state_globals s) /\ IS_NONE (EL n
       (flatSem_state_globals s)) then
       SOME (flatSem_state_globals_fupd (K (LUPDATE (SOME v) n
         (flatSem_state_globals s))) s,Rval Unitv) else
       NONE) | (flatLang_GlobalVarLookup n,[]) ->
     (if n < LENGTH (flatSem_state_globals s) /\ IS_SOME (EL n
       (flatSem_state_globals s)) then
       SOME (s,Rval (THE (EL n (flatSem_state_globals s)))) else
       NONE) | (flatLang_TagLenEq n l,[Conv (SOME (tag,_115)) xs]) ->
     SOME (s,Rval (Boolv (tag = n /\ LENGTH xs = l))) |
       (flatLang_LenEq l,[Conv _116 xs]) ->
     SOME (s,Rval (Boolv (LENGTH xs = l))) | (flatLang_El n,[Conv
       _117 vs]) ->
     (if n < LENGTH vs then SOME (s,Rval (EL n vs)) else NONE) |
       (flatLang_El n,[Loc _118 p]) ->
     (if ~(n = 0) then NONE else
        match store_lookup p (state_refs s) with SOME
          (semanticPrimitives_Refv v) -> SOME (s,Rval v) | _119 -> NONE)
          | (flatLang_Id,[v1]) ->
     SOME (s,Rval v1) | _120 -> NONE)`;;
hol4_overload "do_app" "flatSem_do_app";;

let do_if_def = cake_define
  `(flatSem_do_if v e1 e2 =
    (if v = Boolv T then
      SOME e1 else if v = Boolv F then
      SOME e2 else
        NONE))`;;
hol4_overload "do_if" "flatSem_do_if";;

let do_if_either_or = cake_theorem "do_if_either_or"
  (fun () ->
    `do_if v e1 e2 = SOME e ==> e = e1 \/ e = e2`)
  CHEAT_TAC;;

let pmatch_stamps_ok = cake_inductive
  `(
     pmatch_stamps_ok (SOME (cn,NONE)) (SOME (cn',NONE)) n_ps n_vs)
       /\
   (
         ty_id = ty_id' /\ MEM (cn,n_ps) ctor_set /\ MEM (cn',n_vs)
           ctor_set ==> pmatch_stamps_ok (SOME (cn,(SOME
           (ty_id,ctor_set))))
     (SOME (cn',SOME ty_id')) n_ps n_vs) /\
   (
     n_ps = n_vs ==> pmatch_stamps_ok NONE NONE n_ps n_vs)`;;

let _ = size_thms "flatLang_pat";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flatSemScript.sml:704-708: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let pmatch_def = cake_define_list_try_tac (fun () ->
  `inv_image (<) (\x. match x with INL (x,p,y,z) -> flatLang_pat_size p
     | INR (x,ps,y,z) -> list_size flatLang_pat_size ps)`)
  CHEAT_TAC
  [`flatSem_pmatch s (Pvar x:flatLang_pat) v' bindings =
        (Match ((x,v') :: bindings))`;
   `flatSem_pmatch s flatLang_Pany v' bindings = Match bindings`;
   `flatSem_pmatch s (Plit l:flatLang_pat) (Litv l':flatSem_v) bindings
  =
        (if l = l' then
          Match bindings else if lit_same_type l l' then
          No_match else
          Match_type_error)`;
   `flatSem_pmatch s (Pcon stmp ps:flatLang_pat) (Conv stmp'
  vs:flatSem_v) bindings =
        (if ~(pmatch_stamps_ok stmp stmp' (LENGTH ps) (LENGTH vs))
          then
          Match_type_error else if OPTION_MAP FST stmp = OPTION_MAP
            FST stmp' /\
           LENGTH ps = LENGTH vs then
          flatSem_pmatch_list s ps vs bindings else
          No_match)`;
   `flatSem_pmatch s (Pas p i:flatLang_pat) v bindings =
        flatSem_pmatch s p v ((i,v) :: bindings)`;
   `flatSem_pmatch s (Pref p:flatLang_pat) (Loc _124 lnum:flatSem_v)
  bindings =
        (match store_lookup lnum (state_refs s) with SOME
          (semanticPrimitives_Refv v) -> flatSem_pmatch s p v
          bindings | _125 -> Match_type_error)`;
   `flatSem_pmatch _126 _127 _128 bindings = Match_type_error`;
   `flatSem_pmatch_list s [] [] bindings = Match bindings`;
   `flatSem_pmatch_list s (p :: ps) (v :: vs) bindings =
        (match flatSem_pmatch s p v bindings with Match_type_error
          -> Match_type_error | Match bindings' -> flatSem_pmatch_list s
          ps vs bindings' | No_match ->
          (match flatSem_pmatch_list s ps vs bindings with
            Match_type_error -> Match_type_error | _129 -> No_match))`;
   `flatSem_pmatch_list s _130 _131 bindings = Match_type_error`];;
hol4_overload "pmatch" "flatSem_pmatch";;
hol4_overload "pmatch_list" "flatSem_pmatch_list";;

let pmatch_rows_def = cake_define_list
  [`pmatch_rows [] s v = No_match`;
   `pmatch_rows ((p,e) :: pes) s v =
      (match pmatch s p v [] with Match_type_error ->
        Match_type_error | No_match -> pmatch_rows pes s v | Match env
        ->
         (match pmatch_rows pes s v with Match_type_error ->
           Match_type_error | _133 -> Match (env,p,e)))`];;

let dec_clock_def = cake_define
  `flatSem_dec_clock s = state_clock_fupd (K (state_clock s - 1)) s`;;
hol4_overload "dec_clock" "flatSem_dec_clock";;

let fix_clock_def = cake_define
  `flatSem_fix_clock s (s1,res) = (state_clock_fupd (K (MIN
  (state_clock s) (state_clock s1))) s1,res)`;;
hol4_overload "fix_clock" "flatSem_fix_clock";;

let flatSem_fix_clock_IMP = cake_theorem "fix_clock_IMP[local]"
  (fun () ->
    `fix_clock s x = (s1,res) ==> state_clock s1 <= state_clock s`)
  CHEAT_TAC;;


let do_eval_def = cake_define
  `flatSem_do_eval (vs:flatSem_v list) eval_config =
   (match vs with [v1; v2] ->
       (match (flatSem_v_to_bytes v1,flatSem_v_to_words v2) with
         (SOME bytes,SOME data) ->
          (let (st,decs) = install_config_compile_oracle eval_config
            0 in
          let new_oracle = misc_shift_seq 1
            (install_config_compile_oracle eval_config) in
          (match install_config_compile eval_config st decs with SOME
            (bytes',data',st') ->
             (if bytes = bytes' /\ data = data' /\ ~(decs = []) /\
                 FST (new_oracle 0) = st' then
               SOME (decs,install_config_compile_oracle_fupd (K
                 new_oracle) eval_config,Unitv) else NONE) | _134 ->
                 NONE)) | _135 -> NONE) | _136 -> NONE)`;;
hol4_overload "do_eval" "flatSem_do_eval";;

let AppUnit_def = cake_define
  `flatSem_AppUnit x = flatLang_App backend_common_None (flatLang_Src
  ast_Opapp) [x; Con backend_common_None NONE []]`;;
hol4_overload "AppUnit" "flatSem_AppUnit";;

let _ = size_thms "flatLang_op";;
let _ = size_thms "flatLang_pat";;
let _ = size_thms "lit";;
let _ = size_thms "mlstring";;
let _ = size_thms "tra";;
let exp_alt_size_def = cake_define_list
  [`flatSem_exp_alt_size (Raise a0 a1:flatLang_exp) = 1 + (tra_size
  a0 + flatSem_exp_alt_size a1)`;
   `flatSem_exp_alt_size (Handle a0 a1 a2:flatLang_exp) =
    1 + (tra_size a0 + (flatSem_exp_alt_size a1 +
      flatSem_exp3_alt_size a2))`;
   `flatSem_exp_alt_size (Lit a0 a1:flatLang_exp) = 1 + (tra_size a0
  + lit_size a1)`;
   `flatSem_exp_alt_size (Con a0 a1 a2:flatLang_exp) =
    1 +
    (tra_size a0 +
     (option_size (pair_size (\x. x) (option_size (\x. x))) a1 +
      exp6_alt_size a2))`;
   `flatSem_exp_alt_size (flatLang_Var_local a0 a1) = 1 + (tra_size
  a0 + mlstring_size a1)`;
   `flatSem_exp_alt_size (Fun a0 a1 a2:flatLang_exp) =
    1 + (mlstring_size a0 + (mlstring_size a1 +
      flatSem_exp_alt_size a2))`;
   `flatSem_exp_alt_size (App a0 a1 a2:flatLang_exp) =
    1 + (tra_size a0 + (flatLang_op_size a1 + exp6_alt_size a2))
      + (if a1 = flatLang_Src (ast_ThunkOp ForceThunk) then 100 else
      0)`;
   `flatSem_exp_alt_size (If a0 a1 a2 a3:flatLang_exp) =
    1 + (tra_size a0 + (flatSem_exp_alt_size a1 +
      (flatSem_exp_alt_size a2 + flatSem_exp_alt_size a3)))`;
   `flatSem_exp_alt_size (Mat a0 a1 a2:flatLang_exp) =
    1 + (tra_size a0 + (flatSem_exp_alt_size a1 +
      flatSem_exp3_alt_size a2))`;
   `flatSem_exp_alt_size (Let a0 a1 a2 a3:flatLang_exp) =
    1 +
    (tra_size a0 +
     (option_size mlstring_size a1 + (flatSem_exp_alt_size a2 +
       flatSem_exp_alt_size a3)))`;
   `flatSem_exp_alt_size (Letrec a0 a1 a2:flatLang_exp) =
    1 + (mlstring_size a0 + (flatSem_exp1_alt_size a1 +
      flatSem_exp_alt_size a2))`;
   `flatSem_exp1_alt_size [] = 0`;
   `flatSem_exp1_alt_size (a0 :: a1) = 1 + (flatSem_exp2_alt_size a0
  + flatSem_exp1_alt_size a1)`;
   `flatSem_exp2_alt_size (a0,a1) = 1 + (mlstring_size a0 +
  exp4_alt_size a1)`;
   `flatSem_exp3_alt_size [] = 0`;
   `flatSem_exp3_alt_size (a0 :: a1) = 1 + (exp5_alt_size a0 +
  flatSem_exp3_alt_size a1)`;
   `exp4_alt_size (a0,a1) = 1 + (mlstring_size a0 +
  flatSem_exp_alt_size a1)`;
   `exp5_alt_size (a0,a1) = 1 + (flatLang_pat_size a0 +
  flatSem_exp_alt_size a1)`;
   `exp6_alt_size [] = 0`;
   `exp6_alt_size (a0 :: a1) = 1 + (flatSem_exp_alt_size a0 +
  exp6_alt_size a1)`];;
hol4_overload "exp1_alt_size" "flatSem_exp1_alt_size";;
hol4_overload "exp2_alt_size" "flatSem_exp2_alt_size";;
hol4_overload "exp3_alt_size" "flatSem_exp3_alt_size";;
hol4_overload "exp_alt_size" "flatSem_exp_alt_size";;

let exp6_alt_size = cake_theorem "exp6_alt_size"
  (fun () ->
    `exp6_alt_size xs = LENGTH xs + SUM (MAP flatSem_exp_alt_size xs)`)
  CHEAT_TAC;;

let pmatch_rows_Match_exp_alt_size =
  cake_theorem "pmatch_rows_Match_exp_alt_size"
  (fun () ->
    `!pes s v env e.
       pmatch_rows pes s v = Match (env',p,e) ==>
       flatSem_exp_alt_size e < flatSem_exp3_alt_size pes`)
  CHEAT_TAC;;

let dec_alt_size_def = cake_define
  `dec_alt_size a = 1 + flatSem_exp_alt_size a`;;

let fix_clock_IMP =
  try prove
   (`!s x s1 res. flatSem_fix_clock s x = (s1,res)
                  ==> state_clock s1 <= state_clock s`,
    REWRITE_TAC[FORALL_PAIR_THM; fix_clock_def] THEN
    REWRITE_TAC(PAIR_EQ :: record_thms "flatSem_state") THEN
    REPEAT STRIP_TAC THEN SUBST_VAR_TAC THEN
    REWRITE_TAC(record_thms "flatSem_state") THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC)
  with Failure e ->
    (print_string ("\nfix_clock_IMP: " ^ e ^ "\n"); TRUTH);;

(* a fallback TRUTH says nothing, and a fact that says nothing
   is of no use *)
if concl fix_clock_IMP <> `T` then
  cake_term_facts := fix_clock_IMP :: (!cake_term_facts);;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 flatSemScript.sml:932-945: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let evaluate_def = cake_define_list_try_tac (fun () ->
  `inv_image ((<) LEX (<))
          (\x. match x with INL (env,s,exps) -> (state_clock s,SUM
            (MAP
            flatSem_exp_alt_size exps) + LENGTH exps) | (INR (INL
              (s,d)))
            -> (state_clock s,dec_alt_size d + 1) | (INR (INR
              (s,ds))) ->
            (state_clock s,SUM (MAP dec_alt_size ds) + LENGTH ds +
              1))`)
  CHEAT_TAC
  [`flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) ([]:flatLang_exp list) =
        (s,Rval [])`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) (e1 :: e2 :: es) =
        (match fix_clock s (flatSem_evaluate env s [e1]) with
          (s,Rval v) ->
            (match flatSem_evaluate env s (e2 :: es) with (s,Rval
              vs) -> (s,Rval (HD v :: vs)) | res -> res) | res ->
              res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Lit _138 l:flatLang_exp)] = (s,Rval
  [Litv l])`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Raise _140 e:flatLang_exp)] =
       (match flatSem_evaluate env s [e] with (s,Rval v) ->
         (s,Rerr (Rraise (HD v))) | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Handle _142 e pes:flatLang_exp)] =
       (match fix_clock s (flatSem_evaluate env s [e]) with (s,Rerr
         (Rraise v)) ->
           (match pmatch_rows pes s v with Match_type_error ->
             (s,Rerr (Rabort Rtype_error)) | No_match -> (s,Rerr (Rraise
             v)) | Match (env',p',e') ->
               (if ALL_DISTINCT (pat_bindings p') then
                 flatSem_evaluate (flatSem_environment_v_fupd (K
                 (env' ++ flatSem_environment_v env)) env) s [e']
                 else (s,Rerr (Rabort Rtype_error)))) | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Con _144 NONE es:flatLang_exp)] =
        (match flatSem_evaluate env s (REVERSE es) with (s,Rval
          vs) -> (s,Rval [Conv NONE (REVERSE vs)]) | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Con _146 (SOME cn) es:flatLang_exp)] =
        (match flatSem_evaluate env s (REVERSE es) with (s,Rval
          vs) -> (s,Rval [Conv (SOME cn) (REVERSE vs)]) | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [flatLang_Var_local _147 n] = (s,
       (match ALOOKUP (flatSem_environment_v env) n with SOME v
         -> Rval [v] | NONE -> Rerr (Rabort Rtype_error)))`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Fun _149 n e:flatLang_exp)] = (s,Rval
  [Closure env n e])`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(App _151 op es:flatLang_exp)] =
       (match fix_clock s (flatSem_evaluate env s (REVERSE es)) with
         (s,Rval vs) ->
           (if op = flatLang_Src ast_Opapp then
             (match flatSem_do_opapp (REVERSE vs) with SOME (env',e)
               ->
                (if state_clock s = 0 then
                  (s,Rerr (Rabort Rtimeout_error)) else
                  flatSem_evaluate env' (dec_clock s) [e]) | NONE ->
                    (s,Rerr (Rabort Rtype_error))) else if op =
                    flatLang_Src ast_Eval then
             (match do_eval (REVERSE vs) (flatSem_state_eval_config
               s) with SOME (decs,eval_config,retv) ->
                  (let s = flatSem_state_eval_config_fupd (K
                    eval_config) s in
                  if state_clock s = 0 then
                    (s,Rerr (Rabort Rtimeout_error)) else (match
                      flatSem_evaluate_decs (dec_clock s) decs with
                      (s,NONE) -> (s,Rval [retv]) | (s,SOME e) ->
                      (s,Rerr e))) | NONE -> (s,Rerr (Rabort
                      Rtype_error))) else if op = flatLang_Src
                      (ast_ThunkOp ForceThunk) then
             (match dest_thunk vs (state_refs s) with BadRef ->
               (s,Rerr (Rabort Rtype_error)) | NotThunk -> (s,Rerr
               (Rabort Rtype_error)) | IsThunk Evaluated v -> (s,Rval
               [v]) | IsThunk NotEvaluated f ->
                 (match flatSem_evaluate (mk_flatSem_environment
                   [((implode "f"),f)]) s
                        [flatSem_AppUnit (flatLang_Var_local
                          backend_common_None (implode "f"))] with
                          (s,Rval vs2) ->
                      (match update_thunk vs (state_refs s) vs2 with
                        NONE -> (s,Rerr (Rabort Rtype_error)) | SOME
                        refs -> (state_refs_fupd (K refs) s,Rval vs2)) |
                        (s,Rerr e) -> (s,Rerr e))) else
            (match (do_app s op (REVERSE vs)) with NONE ->
              (s,Rerr (Rabort Rtype_error)) | SOME (s',r) ->
              (s',list_result r))) | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(If _153 e1 e2 e3:flatLang_exp)] =
       (match fix_clock s (flatSem_evaluate env s [e1]) with (s,Rval
         vs) ->
         (match do_if (HD vs) e2 e3 with SOME e ->
           flatSem_evaluate env s [e] | NONE -> (s,Rerr (Rabort
           Rtype_error))) | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Mat _155 e pes:flatLang_exp)] =
       (match fix_clock s (flatSem_evaluate env s [e]) with (s,Rval
         v) ->
           (match pmatch_rows pes s (HD v) with Match_type_error ->
             (s,Rerr (Rabort Rtype_error)) | No_match -> (s,Rerr (Rraise
             bind_exn_v)) | Match (env',p',e') ->
               (if ALL_DISTINCT (pat_bindings p') then
                 flatSem_evaluate (flatSem_environment_v_fupd (K
                 (env' ++ flatSem_environment_v env)) env) s [e']
                 else (s,Rerr (Rabort Rtype_error)))) | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Let _157 n e1 e2:flatLang_exp)] =
       (match fix_clock s (flatSem_evaluate env s [e1]) with
         (s,Rval vs) -> flatSem_evaluate (flatSem_environment_v_fupd
         (opt_bind n (HD vs)) env) s [e2] | res -> res)`;
   `flatSem_evaluate (env:flatSem_v flatSem_environment)
  (s:('c,'ffi)flatSem_state) [(Letrec _159 funs e:flatLang_exp)] =
       (if ALL_DISTINCT (MAP FST funs) then flatSem_evaluate
         (flatSem_environment_v_fupd (K (build_rec_env funs env
         (flatSem_environment_v env))) env) s [e] else (s,Rerr
         (Rabort Rtype_error)))`;
   `evaluate_dec (s:('c,'ffi)flatSem_state) e =
       (match flatSem_evaluate (mk_flatSem_environment []) s [e]
         with (s,Rval x) ->
         (if x = [Unitv] then
           (s,NONE) else
           (s,SOME (Rabort Rtype_error))) | (s,Rerr e) -> (s,SOME
             e))`;
   `flatSem_evaluate_decs (s:('c,'ffi)flatSem_state) [] = (s,NONE)`;
   `flatSem_evaluate_decs (s:('c,'ffi)flatSem_state) (d :: ds) =
       (match fix_clock s (evaluate_dec s d) with (s,NONE) ->
         flatSem_evaluate_decs s ds | (s,SOME e) -> (s,SOME e))`];;
hol4_overload "evaluate" "flatSem_evaluate";;
hol4_overload "evaluate_decs" "flatSem_evaluate_decs";;

(* HOL4 flatSemScript.sml:947-950: ML code, not ported *)

(* HOL4 flatSemScript.sml:952-953: a theorem that HOL4 states as the
   value of an ML expression: case_eq_thms *)

let flatSem_do_app_const = cake_theorem "do_app_const"
  (fun () ->
    `do_app s op vs = SOME (s',r) ==> state_clock s = state_clock s'`)
  CHEAT_TAC;;

let flatSem_evaluate_clock = cake_theorem "evaluate_clock"
  (fun () ->
    `(!env (s:('c,'ffi)flatSem_state) e r s2. evaluate env s e = (s2,r)
  ==> state_clock s2 <= flatSem_state_clock s) /\
     (!(s:('c,'ffi)flatSem_state) e r s2. evaluate_dec s e = (s2,r)
       ==> state_clock s2 <= flatSem_state_clock s) /\
     (!(s:('c,'ffi)flatSem_state) e r s2. evaluate_decs s e =
       (s2,r) ==> state_clock s2 <= flatSem_state_clock s)`)
  CHEAT_TAC;;

let flatSem_fix_clock_evaluate = cake_theorem "fix_clock_evaluate"
  (fun () ->
    `fix_clock s (evaluate env s e) = evaluate env s e /\
     fix_clock s (evaluate_dec s d) = evaluate_dec s d /\
     fix_clock s (evaluate_decs s ds) = evaluate_decs s ds`)
  CHEAT_TAC;;

(* HOL4 flatSemScript.sml:986-987: a theorem that HOL4 states as the
   value of an ML expression: evaluate_def *)

(* HOL4 flatSemScript.sml:989-990: a theorem that HOL4 states as the
   value of an ML expression: evaluate_ind *)

let initial_state_def = cake_define
  `flatSem_initial_state ffi k ec =
     (mk_flatSem_state k [] ffi [] ec:('c,'ffi)flatSem_state)`;;
hol4_overload "initial_state" "flatSem_initial_state";;

let semantics_def = cake_define
  `flatSem_semantics (ec:'c install_config) (ffi:'ffi ffi_state) prog =
     (if ?k.
            SND (evaluate_decs (flatSem_initial_state ffi k ec) prog)
              = SOME (Rabort Rtype_error) then ffi_Fail else
     match some (\res.
       ?k s r outcome.
         evaluate_decs (flatSem_initial_state ffi k ec) prog = (s,r)
           /\
         (match r with SOME (Rabort (Rffi_error e)) -> outcome =
           ffi_FFI_outcome e | SOME (Rabort _160) -> F | _161 -> outcome
           = ffi_Success) /\
         res = ffi_Terminate outcome (ffi_state_io_events (state_ffi
           s))) with SOME res -> res | NONE ->
        ffi_Diverge
          (build_lprefix_lub
            (IMAGE (\k. fromList (ffi_state_io_events (state_ffi
              (FST (evaluate_decs (flatSem_initial_state ffi k ec)
                prog)))))
                UNIV)))`;;
hol4_overload "semantics" "flatSem_semantics";;

(* HOL4 flatSemScript.sml:1025-1027: ML code, not ported *)
