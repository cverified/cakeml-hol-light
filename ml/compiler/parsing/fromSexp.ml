(* ======================================================== *)
(*  fromSexp: ported from HOL4's
    compiler/parsing/fromSexpScript.sml  *)
(* ======================================================== *)

(*
  Definitions of functions for conversion between an S-expression
    encoding of
  the CakeML abstract syntax and the abstract syntax type itself.

  The S-expressions are parsed as *per* the PEG in HOL’s
  `examples/formal-language/context-free/simpleSexpPEGScript.sml`.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/encoders/asm/asmSem.ml";;
needs "lib/ASCIInumbers.ml";;
needs "lib/comparison.ml";;
needs "lib/location.ml";;
needs "lib/numposrep.ml";;
needs "semantics/ast.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;
(* HOL4 ancestors outside the port: simpleSexp quantHeuristics *)

(* TODO: this is duplicated in parserProgTheory *)

(* HOL4 overload (expanded in the port):
     lift = OPTION_MAP *)

(* TODO: move*)

(* HOL4 ML code, not ported:
val type_ind =
  (TypeBase.induction_of``:ast_t``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`
*)

(* HOL4 ML code, not ported:
val pat_ind =
  (TypeBase.induction_of``:pat``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`
*)

(* HOL4 ML code, not ported:
val exp_ind =
  (TypeBase.induction_of``:exp``)
  |> Q.SPECL[`P`,`EVERY (P o SND o SND)`,`P o SND o SND`,`EVERY (P o
    SND)`,`P o SND`,`P o SND`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`
*)

(* HOL4 ML code, not ported:
val dec_ind =
  (TypeBase.induction_of``:dec``)
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE list_ss []
  |> UNDISCH_ALL |> CONJUNCT1
  |> DISCH_ALL |> Q.GEN`P`
*)

(* end TODO *)

let encode_control_def = cake_define_list
  [`encode_control "" = ""`;
   `encode_control (c :: cs) =
        (if c = (CHR 92) then c :: c :: (encode_control cs) else if
          isPrint c then c :: (encode_control cs) else
             ((CHR 92) :: ((if ORD c < 16 then "0" else "") ++
               num_to_hex_string (ORD c))) ++ (encode_control cs))`];;

let decode_control_def = cake_define_list
  [`decode_control "" = SOME ""`;
   `decode_control (c :: cs) =
         (if c = (CHR 92) then
         match cs with (CHR 92) :: cs -> OPTION_MAP (CONS c)
           (decode_control cs) | d1 :: d2 :: cs ->
           OPTION_IGNORE_BIND (OPTION_GUARD
             (isHexDigit d1 /\
              isHexDigit d2 /\
              (isAlpha d1 ==> isUpper d1) /\
              (isAlpha d2 ==> isUpper d2) /\ ~isPrint (CHR
                (num_from_hex_string [d1; d2]))))
           (OPTION_MAP (CONS (CHR (num_from_hex_string [d1;
             d2]))) (decode_control cs)) | _2 -> NONE else
             OPTION_IGNORE_BIND (OPTION_GUARD (isPrint c))
             (OPTION_MAP (CONS c) (decode_control cs)))`];;

let SEXSTR_def = cake_define
  `SEXSTR s = SX_STR (encode_control s)`;;

let odestSEXSTR_def = cake_define
  `odestSEXSTR x1 =
        match x1 with
          SX_STR s -> OPTION_MAP implode (decode_control s)
        | _3 -> NONE`;;

let odestSXSTR_def = cake_define
  `odestSXSTR x1 =
        match x1 with
          SX_STR s -> SOME (implode s)
        | _4 -> NONE`;;

let odestSXSYM_def = cake_define
  `odestSXSYM x1 =
        match x1 with
          SX_SYM s -> SOME (implode s)
        | _5 -> NONE`;;

let odestSXNUM_def = cake_define
  `odestSXNUM x1 =
        match x1 with
          SX_NUM n -> SOME n
        | _6 -> NONE`;;

let sexpopt_def = cake_define
  `sexpopt p s =
     OPTION_BIND (odestSXSYM s) (\
        nm. OPTION_IGNORE_BIND
        (assert (nm = (implode "NONE"))) (
        SOME NONE)) ++
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args). OPTION_IGNORE_BIND
       (assert (nm = "SOME" /\ LENGTH args = 1)) (
       OPTION_MAP SOME (p (HD args))))`;;

let sexplist_def = cake_define
  `sexplist p s =
     (match s with
       SX_CONS h t ->
         OPTION_BIND (p h) (\
           ph. OPTION_BIND (sexplist p t) (\
           pt.
           SOME (ph :: pt))) | SX_SYM s -> (if s = "nil" then SOME
             [] else fail) | _7 -> fail)`;;

let sexppair_def = cake_define
  `sexppair p1 p2 s =
     (match s with
       SX_CONS s1 s2 -> lift2 (,) (p1 s1) (p2 s2) | _8 -> fail)`;;

(* HOL4 overload (expanded in the port):
     guard = λb m. monad_unitbind (assert b) m *)

(* TERMINATION: wf_rel_tac `measure (sexp_size o SND)` >>
  simp[dstrip_sexp_SOME, LENGTH_EQ_NUM_compute, PULL_EXISTS,
    sexp_size_def] *)
let sexpid_def = cake_define
  `sexpid p s =
     OPTION_BIND (dstrip_sexp s) (\
        (nm,args).
        ((\b m. monad_unitbind (assert b) m) (nm = "Short" /\ LENGTH
          args = 1)
               (OPTION_MAP Short (p (EL 0 args))) ++
         (\b m. monad_unitbind (assert b) m) (nm = "Long" /\ LENGTH
           args = 2)
               (lift2 Long (odestSEXSTR (EL 0 args)) (sexpid p (EL
                 1 args)))))`;;

(* TERMINATION: wf_rel_tac `measure sexp_size` >>
  simp[LENGTH_EQ_NUM_compute, dstrip_sexp_SOME, PULL_EXISTS,
    sexp_size_def] >>
  rpt strip_tac >> drule sxMEM_sizelt >> simp[] *)
let sexptype_def = cake_define
  `sexptype s =
     OPTION_BIND (dstrip_sexp s) (\
        (s,args).
        ((\b m. monad_unitbind (assert b) m) (s = "Atvar" /\ LENGTH
          args = 1)
               (OPTION_MAP Atvar (odestSEXSTR (EL 0 args))) ++
         (\b m. monad_unitbind (assert b) m) (s = "Atfun" /\ LENGTH
           args = 2)
               (lift2 Atfun (sexptype (EL 0 args)) (sexptype (EL 1
                 args))) ++
         (\b m. monad_unitbind (assert b) m) (s = "Attup" /\ LENGTH
           args = 1)
               (OPTION_MAP Attup (sexplist sexptype (EL 0 args))) ++
         (\b m. monad_unitbind (assert b) m) (s = "Atapp" /\ LENGTH
           args = 2)
               (lift2 Atapp (sexplist sexptype (EL 0 args))
                      (sexpid odestSEXSTR (EL 1 args)))))`;;

(* translator friendly version for bootstrapping *)
let sexptype_alt_def = cake_define_list
  [`sexptype_alt s =
        (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
          (if nm = "Atvar" /\ LENGTH args = 1 then
            OPTION_MAP Atvar (odestSEXSTR (EL 0 args)) else if nm =
              "Atfun" /\ LENGTH args = 2 then
            OPTION_MAP2 Atfun (sexptype_alt (EL 0 args))
              (sexptype_alt (EL 1 args)) else if nm = "Attup" /\ LENGTH
              args = 1 then
            OPTION_MAP Attup (sexptype_list (EL 0 args)) else if nm
              = "Atapp" /\ LENGTH args = 2 then
            OPTION_MAP2 Atapp (sexptype_list (EL 0 args)) (sexpid
              odestSEXSTR (EL 1 args)) else NONE))`;
   `sexptype_list s =
        (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
          NONE) | SX_CONS a d ->
          (match sexptype_alt a with NONE -> NONE | SOME h ->
           (match sexptype_list d with NONE -> NONE | SOME t ->
             SOME (h :: t))) | _9 -> NONE)`];;

let sexplit_def = cake_define
  `sexplit s =
     OPTION_MAP (ast_IntLit o (&)) (odestSXNUM s) ++
     OPTION_MAP ast_StrLit (odestSEXSTR s) ++
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args). OPTION_IGNORE_BIND
       (assert (LENGTH args = 1)) (
       (\b m. monad_unitbind (assert b) m) (nm = "-")
             (OPTION_BIND (odestSXNUM (HD args))
                          (\n. if n = 0 then NONE else SOME
                            (ast_IntLit (--&n)))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "char")
             (OPTION_BIND (odestSEXSTR (HD args)) (\
               cs. OPTION_IGNORE_BIND
               (assert (strlen cs = 1)) (
               SOME (ast_Char (strsub cs 0))))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "word8")
             (OPTION_BIND (odestSXNUM (HD args)) (\
               n. OPTION_IGNORE_BIND
               (assert (n < 256)) (
               SOME (ast_Word8 (n2w n))))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "word64")
             (OPTION_BIND (odestSXNUM (HD args)) (\
               n. OPTION_IGNORE_BIND
               (assert (n < 2 EXP 64)) (
               SOME (ast_Word64 (n2w n))))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "float64")
             (OPTION_BIND (odestSXNUM (HD args)) (\
               n. OPTION_IGNORE_BIND
               (assert (n < 2 EXP 64)) (
               SOME (ast_Float64 (n2w n)))))))`;;

(* don't require Pvar constructors; bare strings can be pattern
   variables.
   Unclear if this sort of special-casing is ever likely to be helpful
     *)
let _ = size_thms "sexp";;
(* HOL4 termination: >> simp[] >> rpt strip_tac >-
   metis_tac[arithmeticTheory.LESS_TRANS, rich_listTheory.EL_MEM,
   DECIDE ``1n < 2``, sxMEM_sizelt, dstrip_sexp_size] >-
   metis_tac[arithmeticTheory.LESS_TRANS, rich_listTheory.EL_MEM,
   DECIDE ``0n < 2``, sxMEM_sizelt, dstrip_sexp_size, EL ] >-
   metis_tac[arithmeticTheory.LESS_TRANS, rich_listTheory.EL_MEM,
   DECIDE ``0n < 2``, sxMEM_sizelt, dstrip_sexp_size, EL ] >-
   metis_tac[rich_listTheory.EL_MEM, DECIDE ``0n < 1``,
   listTheory.EL, dstrip_sexp_size] *)
let sexppat_def = cake_define_wf
  `MEASURE sexp_size`
  `sexppat s =
     OPTION_MAP ast_Pvar (odestSEXSTR s) ++
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args).
       (\b m. monad_unitbind (assert b) m) (nm = "Pany" /\ LENGTH
         args = 0)
             (SOME ast_Pany) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Plit" /\ LENGTH
         args = 1)
             (OPTION_MAP ast_Plit (sexplit (EL 0 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Pcon" /\ LENGTH
         args = 2)
             (lift2 ast_Pcon (sexpopt (sexpid odestSEXSTR) (EL 0
               args))
                         (sexplist sexppat (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Pas" /\ LENGTH args
         = 2)
             (lift2 ast_Pas (sexppat (EL 0 args))
                        (odestSEXSTR (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Pref" /\ LENGTH
         args = 1) (OPTION_MAP ast_Pref (sexppat (EL 0 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Ptannot" /\ LENGTH
         args = 2)
             (lift2 ast_Ptannot (sexppat (EL 0 args)) (sexptype
               (EL 1 args))))`;;

(* translator friendly version for bootstrapping *)
let sexppat_alt_def = cake_define_list
  [`sexppat_alt s =
        OPTION_MAP ast_Pvar (odestSEXSTR s) ++
        (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
          (if nm = "Pany" /\ LENGTH args = 0 then
            SOME ast_Pany else if nm = "Plit" /\ LENGTH args = 1
              then
            OPTION_MAP ast_Plit (sexplit (EL 0 args)) else if nm =
              "Pcon" /\ LENGTH args = 2 then
            OPTION_MAP2 ast_Pcon (sexpopt (sexpid odestSEXSTR) (EL 0
              args))
              (sexppat_list (EL 1 args)) else if nm = "Pas" /\
                LENGTH args = 2 then
            OPTION_MAP2 ast_Pas (sexppat_alt (EL 0 args))
                            (odestSEXSTR (EL 1 args)) else if nm =
                              "Pref" /\ LENGTH args = 1 then
            OPTION_MAP ast_Pref (sexppat_alt (EL 0 args)) else if nm
              = "Ptannot" /\ LENGTH args = 2 then
            OPTION_MAP2 ast_Ptannot (sexppat_alt (EL 0 args))
              (sexptype_alt (EL 1 args)) else NONE))`;
   `sexppat_list s =
        (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
          NONE) | SX_CONS a d ->
          (match sexppat_alt a with NONE -> NONE | SOME h ->
           (match sexppat_list d with NONE -> NONE | SOME t ->
             SOME (h :: t))) | _10 -> NONE)`];;

(* HOL4 ML code, not ported:
val sexppat_alt_ind = theorem"sexppat_alt_ind";
*)

let decode_thunk_mode_def = cake_define
  `decode_thunk_mode s =
     (if s = "Evaluated" then SOME Evaluated else if s =
       "NotEvaluated" then SOME NotEvaluated else NONE)`;;

let encode_thunk_mode_def = cake_define_list
  [`encode_thunk_mode Evaluated = "Evaluated"`;
   `encode_thunk_mode NotEvaluated = "NotEvaluated"`];;

let decode_test_def = cake_define
  `fromSexp_decode_test x1 =
      match x1 with
        SX_SYM s ->
     (if s = "Equal" then SOME Equal else
      if s = "Less" then SOME (ast_Compare ast_Lt) else
      if s = "LessEq" then SOME (ast_Compare ast_Leq) else
      if s = "Greater" then SOME (ast_Compare ast_Gt) else
      if s = "GreaterEq" then SOME (ast_Compare ast_Geq) else
      if s = "AltLess" then SOME (ast_AltCompare ast_Lt) else
      if s = "AltLessEq" then SOME (ast_AltCompare ast_Leq) else
      if s = "AltGreater" then SOME (ast_AltCompare ast_Gt) else
      if s = "AltGreaterEq" then SOME (ast_AltCompare ast_Geq) else
        NONE)
      | _11 -> NONE`;;

let decode_prim_type_def = cake_define
  `decode_prim_type x1 =
      match x1 with
        SX_SYM s ->
     (if s = "BoolT" then SOME ast_BoolT else
      if s = "IntT" then SOME ast_IntT else
      if s = "CharT" then SOME ast_CharT else
      if s = "StrT" then SOME ast_StrT else
      if s = "Word8T" then SOME (ast_WordT ast_W8) else
      if s = "Word64T" then SOME (ast_WordT ast_W64) else
      if s = "Float64T" then SOME ast_Float64T else NONE)
      | _12 -> NONE`;;

let sexparith_def = cake_define
  `sexparith x1 =
      match x1 with
        SX_SYM s ->
     (if s = "Add" then SOME ast_Add else
      if s = "Sub" then SOME ast_Sub else
      if s = "Mul" then SOME ast_Mul else
      if s = "Div" then SOME ast_Div else
      if s = "Mod" then SOME ast_Mod else
      if s = "Neg" then SOME ast_Neg else
      if s = "Abs" then SOME ast_Abs else
      if s = "And" then SOME ast_And else
      if s = "Xor" then SOME ast_Xor else
      if s = "Or" then SOME ast_Or else
      if s = "Not" then SOME ast_Not else
      if s = "Sqrt" then SOME ast_Sqrt else
      if s = "FMA" then SOME ast_FMA else NONE)
      | _13 -> NONE`;;

let sexplog_def = cake_define
  `sexplog x1 =
      match x1 with
        SX_SYM s ->
     (if s = "Andalso" then SOME Andalso else
      if s = "Orelse" then SOME Orelse else NONE)
      | _14 -> NONE`;;

let sexpop_def = cake_define
  `sexpop x1 =
        match x1 with
          SX_SYM s ->
     (if s = "Equality" then SOME ast_Equality else
     if s = "Opapp" then SOME ast_Opapp else
     if s = "Opassign" then SOME ast_Opassign else
     if s = "Opref" then SOME ast_Opref else
     if s = "Opderef" then SOME ast_Opderef else
     if s = "Aw8alloc" then SOME ast_Aw8alloc else
     if s = "Aw8sub" then SOME ast_Aw8sub else
     if s = "Aw8length" then SOME ast_Aw8length else
     if s = "Aw8update" then SOME ast_Aw8update else
     if s = "Aw8subunsafe" then SOME ast_Aw8sub_unsafe else
     if s = "Aw8updateunsafe" then SOME ast_Aw8update_unsafe else
     if s = "CopyStrStr" then SOME ast_CopyStrStr else
     if s = "CopyStrAw8" then SOME ast_CopyStrAw8 else
     if s = "CopyAw8Str" then SOME ast_CopyAw8Str else
     if s = "CopyAw8Aw8" then SOME ast_CopyAw8Aw8 else
     if s = "XorAw8Strunsafe" then SOME ast_XorAw8Str_unsafe else
     if s = "Implode" then SOME ast_Implode else
     if s = "Explode" then SOME ast_Explode else
     if s = "Strsub" then SOME ast_Strsub else
     if s = "Strlen" then SOME ast_Strlen else
     if s = "Strcat" then SOME ast_Strcat else
     if s = "VfromList" then SOME ast_VfromList else
     if s = "Vsub" then SOME ast_Vsub else
     if s = "Vsubunsafe" then SOME ast_Vsub_unsafe else
     if s = "Vlength" then SOME ast_Vlength else
     if s = "ListAppend" then SOME ast_ListAppend else
     if s = "Aalloc" then SOME ast_Aalloc else
     if s = "AallocEmpty" then SOME ast_AallocEmpty else
     if s = "AallocFixed" then SOME ast_AallocFixed else
     if s = "Asub" then SOME ast_Asub else
     if s = "Alength" then SOME ast_Alength else
     if s = "Aupdate" then SOME ast_Aupdate else
     if s = "Asubunsafe" then SOME ast_Asub_unsafe else
     if s = "Aupdateunsafe" then SOME ast_Aupdate_unsafe else
     if s = "ForceThunk" then SOME (ast_ThunkOp ForceThunk) else
     if s = "ConfigGC" then SOME ast_ConfigGC else
     if s = "Eval" then SOME ast_Eval else
     if s = "Envid" then SOME ast_Env_id else NONE)
        | (SX_CONS (SX_SYM s) (SX_STR s')) ->
        (if s = "FFI" then OPTION_MAP (ast_FFI o implode)
          (decode_control s') else NONE)
        | (SX_CONS (SX_SYM s) (SX_SYM t)) ->
        (match decode_thunk_mode t with NONE -> NONE | SOME m ->
            (if s = "AllocThunk" then SOME (ast_ThunkOp (AllocThunk
              m)) else
            if s = "UpdateThunk" then SOME (ast_ThunkOp (UpdateThunk
              m)) else NONE))
        | (SX_CONS (SX_SYM s) (SX_NUM n)) ->
       (if s = "Shift8Lsl" then SOME (ast_Shift ast_W8 Lsl n) else
       if s = "Shift8Lsr" then SOME (ast_Shift ast_W8 Lsr n) else
       if s = "Shift8Asr" then SOME (ast_Shift ast_W8 Asr n) else
       if s = "Shift8Ror" then SOME (ast_Shift ast_W8 Ror n) else
       if s = "Shift64Lsl" then SOME (ast_Shift ast_W64 Lsl n) else
       if s = "Shift64Lsr" then SOME (ast_Shift ast_W64 Lsr n) else
       if s = "Shift64Asr" then SOME (ast_Shift ast_W64 Asr n) else
       if s = "Shift64Ror" then SOME (ast_Shift ast_W64 Ror n) else
         NONE)
        | (SX_CONS (SX_SYM s) (SX_CONS x y)) ->
       (if s = "Arith" then
         (match (sexparith x,decode_prim_type y) with (SOME a,SOME
           prim_type) -> SOME (ast_Arith a prim_type) | _15 -> NONE)
           else if s = "FromTo" then
         (match (decode_prim_type x,decode_prim_type y) with (SOME
           ty1,SOME ty2) -> SOME (ast_FromTo ty1 ty2) | _16 -> NONE)
           else if s = "Test" then
         (match (fromSexp_decode_test x,decode_prim_type y) with
           (SOME test,SOME prim_type) -> SOME (ast_Test test prim_type)
           | _17 -> NONE) else NONE)
        | _18 -> NONE`;;

let sexplocpt_def = cake_define
  `sexplocpt s =
        match s with
          SX_SYM s ->
       (if s = "unk" then SOME UNKNOWNpt else if s = "eof" then SOME
         EOFpt else NONE)
        | s ->
      OPTION_BIND (strip_sxcons s) (\
        ls.
        (\b m. monad_unitbind (assert b) m) (LENGTH ls = 2) (lift2
          POSN
                              (odestSXNUM (EL 0 ls))
                              (odestSXNUM (EL 1 ls))))`;;

let sexplocn_def = cake_define
  `sexplocn s =
     OPTION_BIND (strip_sxcons s) (\
       ls.
       (\b m. monad_unitbind (assert b) m) (LENGTH ls = 2)
             (lift2 Locs
              (sexplocpt (EL 0 ls))
              (sexplocpt (EL 1 ls))))`;;

let _ = size_thms "sexp";;
(* HOL4 termination: >> rw[]>> imp_res_tac dstrip_sexp_size >>
   imp_res_tac sxMEM_sizelt >> gvs[sexp_size_def,DB.fetch
   "quantHeuristics" "LIST_LENGTH_3",SF DNF_ss] *)
let sexpexp_def = cake_define_wf
  `MEASURE sexp_size`
  `sexpexp s =
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args).
       (\b m. monad_unitbind (assert b) m) (nm = "Raise" /\ LENGTH
         args = 1)
             (OPTION_MAP ast_Raise (sexpexp (EL 0 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Handle" /\ LENGTH
         args = 2)
             (lift2 ast_Handle
                    (sexpexp (EL 0 args))
                    (sexplist (sexppair sexppat sexpexp) (EL 1
                      args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Lit" /\ LENGTH args
         = 1)
             (OPTION_MAP ast_Lit (sexplit (EL 0 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Con" /\ LENGTH args
         = 2)
             (lift2 ast_Con
                    (sexpopt (sexpid odestSEXSTR) (EL 0 args))
                    (sexplist sexpexp (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Var" /\ LENGTH args
         = 1)
             (OPTION_MAP ast_Var (sexpid odestSEXSTR (EL 0 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Fun" /\ LENGTH args
         = 2)
             (lift2 ast_Fun (odestSEXSTR (EL 0 args)) (sexpexp (EL 1
               args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "App" /\ LENGTH args
         = 2)
             (lift2 ast_App (sexpop (EL 0 args)) (sexplist sexpexp
               (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Log" /\ LENGTH args
         = 3)
             (OPTION_MAP ast_Log (sexplog (EL 0 args)) <*>
                       (sexpexp (EL 1 args)) <*>
                       (sexpexp (EL 2 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "If" /\ LENGTH args
         = 3)
             (OPTION_MAP ast_If (sexpexp (EL 0 args)) <*>
                      (sexpexp (EL 1 args)) <*>
                      (sexpexp (EL 2 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Mat" /\ LENGTH args
         = 2)
             (lift2 ast_Mat
               (sexpexp (EL 0 args))
               (sexplist (sexppair sexppat sexpexp) (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Let" /\ LENGTH args
         = 3)
             (OPTION_MAP ast_Let (sexpopt odestSEXSTR (EL 0 args))
               <*>
                       (sexpexp (EL 1 args)) <*>
                       (sexpexp (EL 2 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Letrec" /\ LENGTH
         args = 2)
             (lift2 ast_Letrec
               (sexplist (sexppair odestSEXSTR (sexppair odestSEXSTR
                 sexpexp)) (EL 0 args))
               (sexpexp (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Tannot" /\ LENGTH
         args = 2)
             (lift2 ast_Tannot
               (sexpexp (EL 0 args))
               (sexptype (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Lannot" /\ LENGTH
         args = 2)
             (lift2 ast_Lannot
               (sexpexp (EL 0 args))
               (sexplocn (EL 1 args))))`;;

(* translator friendly version for bootstrapping *)
let sexpexp_alt_def = cake_define_list
  [`sexpexp_alt s =
         (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
              (if nm = "Raise" /\ LENGTH args = 1 then
                 OPTION_MAP ast_Raise (sexpexp_alt (EL 0 args)) else
              if nm = "Handle" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Handle (sexpexp_alt (EL 0 args))
                   (sexppes (EL 1 args)) else
              if nm = "Lit" /\ LENGTH args = 1 then
                 OPTION_MAP ast_Lit (sexplit (EL 0 args)) else
              if nm = "Con" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Con (sexpopt (sexpid odestSEXSTR)
                   (EL 0 args))
                   (sexpexp_list (EL 1 args)) else
              if nm = "Var" /\ LENGTH args = 1 then
                 OPTION_MAP ast_Var (sexpid odestSEXSTR (EL 0 args))
                   else
              if nm = "Fun" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Fun (odestSEXSTR (EL 0 args))
                   (sexpexp_alt (EL 1 args)) else
              if nm = "App" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_App (sexpop (EL 0 args))
                   (sexpexp_list (EL 1 args)) else
              if nm = "Log" /\ LENGTH args = 3 then
                 OPTION_MAP ast_Log (sexplog (EL 0 args)) <*>
                   sexpexp_alt (EL 1 args) <*>
                 sexpexp_alt (EL 2 args) else
              if nm = "If" /\ LENGTH args = 3 then
                 OPTION_MAP ast_If (sexpexp_alt (EL 0 args)) <*>
                   sexpexp_alt (EL 1 args) <*>
                 sexpexp_alt (EL 2 args) else
              if nm = "Mat" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Mat (sexpexp_alt (EL 0 args))
                   (sexppes (EL 1 args)) else
              if nm = "Let" /\ LENGTH args = 3 then
                 OPTION_MAP ast_Let (sexpopt odestSEXSTR (EL 0
                   args)) <*>
                 sexpexp_alt (EL 1 args) <*> sexpexp_alt (EL 2 args)
                   else
              if nm = "Letrec" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Letrec
                   (sexpfuns (EL 0 args))
                   (sexpexp_alt (EL 1 args)) else
              if nm = "Tannot" /\ LENGTH args = 2 then
                 OPTION_MAP2 ast_Tannot (sexpexp_alt (EL 0 args))
                   (sexptype_alt (EL 1 args)) else
              if nm = "Lannot" /\ LENGTH args = 2 then
                OPTION_MAP2 ast_Lannot (sexpexp_alt (EL 0 args))
                  (sexplocn (EL 1 args)) else NONE))`;
   `sexpexp_list s =
          (match s with SX_SYM nm -> (if nm = "nil" then SOME []
            else NONE) | SX_CONS a d ->
            (match sexpexp_alt a with NONE -> NONE | SOME h ->
             (match sexpexp_list d with NONE -> NONE | SOME t ->
               SOME (h :: t))) | _19 -> NONE)`;
   `sexppes s =
       (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
         NONE) | SX_CONS a d ->
         (match sexppatexp a with NONE -> NONE | SOME h ->
          (match sexppes d with NONE -> NONE | SOME t -> SOME (h
            :: t))) | _20 -> NONE)`;
   `sexpfuns s =
       (match s with SX_SYM nm -> (if nm = "nil" then SOME [] else
         NONE) | SX_CONS a d ->
         (match sexpfun a with NONE -> NONE | SOME h ->
          (match sexpfuns d with NONE -> NONE | SOME t -> SOME (h
            :: t))) | _21 -> NONE)`;
   `sexppatexp s =
        (match s with SX_CONS a d ->
          (match (sexppat_alt a,sexpexp_alt d) with (SOME p,SOME
            e) -> SOME (p,e) | _22 -> NONE) | _23 -> NONE)`;
   `sexpfun s =
         (match s with SX_CONS a d ->
           (match d with SX_CONS b d ->
           (match (odestSEXSTR a,odestSEXSTR b,sexpexp_alt d)
             with (SOME x,SOME y,SOME z) -> SOME (x,y,z) | _24 ->
             NONE) | _25 -> NONE) | _26 -> NONE)`];;

let sexptype_def_def = cake_define
  `sexptype_def =
   sexplist
     (sexppair (sexplist odestSEXSTR)
       (sexppair odestSEXSTR
         (sexplist (sexppair odestSEXSTR (sexplist sexptype)))))`;;

(* TERMINATION: wf_rel_tac`measure sexp_size`
   \\ rw[LENGTH_EQ_NUM_compute] \\ fs[]
   \\ metis_tac[sxMEM_sizelt,dstrip_sexp_size,MEM,LESS_TRANS] *)
let sexpdec_def = cake_define
  `sexpdec s =
     OPTION_BIND (dstrip_sexp s) (\
       (nm,args).
       (\b m. monad_unitbind (assert b) m) (nm = "Dlet" /\ LENGTH
         args = 3)
             (OPTION_MAP Dlet (sexplocn (HD args)) <*>
                        (sexppat (EL 1 args)) <*>
                        (sexpexp (EL 2 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Dletrec" /\ LENGTH
         args = 2)
             (lift2 Dletrec (sexplocn (HD args))
                            (sexplist (sexppair odestSEXSTR (sexppair
                              odestSEXSTR sexpexp)) (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Dtype" /\ LENGTH
         args = 2)
             (lift2 Dtype (sexplocn (HD args)) (sexptype_def (EL 1
               args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Dtabbrev" /\ LENGTH
         args = 4)
             (OPTION_MAP Dtabbrev (sexplocn (EL 0 args)) <*>
                            (sexplist odestSEXSTR (EL 1 args)) <*>
                            (odestSEXSTR (EL 2 args)) <*>
                            (sexptype (EL 3 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Denv" /\ LENGTH
         args = 1)
             (OPTION_MAP Denv (odestSEXSTR (EL 0 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Dexn" /\ LENGTH
         args = 3)
             (OPTION_MAP Dexn (sexplocn (EL 0 args)) <*>
                        (odestSEXSTR (EL 1 args)) <*>
                        (sexplist sexptype (EL 2 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Dmod" /\ LENGTH
         args = 2)
             (lift2 Dmod (odestSEXSTR (EL 0 args))
                         (sexplist sexpdec (EL 1 args))) ++
       (\b m. monad_unitbind (assert b) m) (nm = "Dlocal" /\ LENGTH
         args = 2)
             (lift2 Dlocal (sexplist sexpdec (EL 0 args))
                 (sexplist sexpdec (EL 1 args))))`;;

(* translator friendly version for bootstrapping *)
let sexpdec_alt_def = cake_define_list
  [`sexpdec_alt s =
        (match dstrip_sexp s with NONE -> NONE | SOME (nm,args) ->
          (if nm = "Dlet" /\ LENGTH args = 3 then
              (OPTION_MAP Dlet (sexplocn (HD args)) <*>
                           (sexppat_alt (EL 1 args)) <*>
                           (sexpexp_alt (EL 2 args))) else
          if nm = "Dletrec" /\ LENGTH args = 2 then
                (lift2 Dletrec (sexplocn (HD args))
                              (sexpfuns (EL 1 args))) else
          if nm = "Dtype" /\ LENGTH args = 2 then
                (lift2 Dtype (sexplocn (HD args)) (sexptype_def (EL
                  1 args))) else
          if nm = "Dtabbrev" /\ LENGTH args = 4 then
                (OPTION_MAP Dtabbrev (sexplocn (EL 0 args)) <*>
                              (sexplist odestSEXSTR (EL 1 args)) <*>
                              (odestSEXSTR (EL 2 args)) <*>
                              (sexptype_alt (EL 3 args))) else
          if nm = "Denv" /\ LENGTH args = 1 then
                (OPTION_MAP Denv (odestSEXSTR (EL 0 args))) else
          if nm = "Dexn" /\ LENGTH args = 3 then
                (OPTION_MAP Dexn (sexplocn (EL 0 args)) <*>
                           (odestSEXSTR (EL 1 args)) <*>
                           (sexptype_list (EL 2 args))) else
          if nm = "Dmod" /\ LENGTH args = 2 then
                (lift2 Dmod (odestSEXSTR (EL 0 args))
                            (sexpdec_list (EL 1 args))) else
          if nm = "Dlocal" /\ LENGTH args = 2 then
                (lift2 Dlocal (sexpdec_list (EL 0 args))
                            (sexpdec_list (EL 1 args))) else
                              NONE))`;
   `sexpdec_list s =
          (match s with SX_SYM nm -> (if nm = "nil" then SOME []
            else NONE) | SX_CONS a d ->
            (match sexpdec_alt a with NONE -> NONE | SOME h ->
             (match sexpdec_list d with NONE -> NONE | SOME t ->
               SOME (h :: t))) | _27 -> NONE)`];;

(* HOL4 ML code, not ported:
val sexpdec_alt_ind = theorem"sexpdec_alt_ind";
*)

(* now the reverse: toSexp *)

let listsexp_def = cake_define
  `listsexp = FOLDR SX_CONS nil`;;

let optsexp_def = cake_define_list
  [`optsexp NONE = SX_SYM "NONE"`;
   `optsexp (SOME x) = listsexp [SX_SYM "SOME"; x]`];;

let idsexp_def = cake_define_list
  [`idsexp (Short n) = listsexp [SX_SYM "Short"; SEXSTR (explode n)]`;
   `idsexp (Long ns n) = listsexp [SX_SYM "Long"; SEXSTR (explode
  ns); idsexp n]`];;

let typesexp_def = cake_define_list
  [`typesexp (Atvar s) = listsexp [SX_SYM "Atvar"; SEXSTR (explode
  s)]`;
   `typesexp (Atfun t1 t2) = listsexp [SX_SYM "Atfun"; typesexp t1;
  typesexp t2]`;
   `typesexp (Attup ts) = listsexp [SX_SYM "Attup"; listsexp (MAP
  typesexp ts)]`;
   `typesexp (Atapp ts tc) = listsexp [SX_SYM "Atapp"; listsexp (MAP
  typesexp ts); idsexp tc]`];;

let litsexp_def = cake_define_list
  [`litsexp (ast_IntLit i) =
       (if i < 0 then listsexp [SX_SYM "-"; SX_NUM (num_of_int
         (--i))] else SX_NUM (num_of_int i))`;
   `litsexp (ast_Char c) = listsexp [SX_SYM "char"; SEXSTR [c]]`;
   `litsexp (ast_StrLit s) = SEXSTR (explode s)`;
   `litsexp (ast_Word8 w) = listsexp [SX_SYM "word8"; SX_NUM (w2n w)]`;
   `litsexp (ast_Word64 w) = listsexp [SX_SYM "word64"; SX_NUM (w2n
  w)]`;
   `litsexp (ast_Float64 w) = listsexp [SX_SYM "float64"; SX_NUM (w2n
  w)]`];;

let patsexp_def = cake_define_list
  [`patsexp ast_Pany = listsexp [SX_SYM "Pany"]`;
   `patsexp (ast_Pvar s) = SEXSTR (explode s)`;
   `patsexp (ast_Plit l) = listsexp [SX_SYM "Plit"; litsexp l]`;
   `patsexp (ast_Pcon cn ps) = listsexp [SX_SYM "Pcon"; optsexp
  (OPTION_MAP idsexp cn); listsexp (MAP patsexp ps)]`;
   `patsexp (ast_Pas p i) = listsexp [SX_SYM "Pas"; patsexp p; SEXSTR
  (explode i)]`;
   `patsexp (ast_Pref p) = listsexp [SX_SYM "Pref"; patsexp p]`;
   `patsexp (ast_Ptannot p t) = listsexp [SX_SYM "Ptannot"; patsexp
  p; typesexp t]`];;

let testsexp_def = cake_define
  `testsexp x1 =
      match x1 with
        Equal -> SX_SYM "Equal"
      | (ast_Compare ast_Lt) -> SX_SYM "Less"
      | (ast_Compare ast_Leq) -> SX_SYM "LessEq"
      | (ast_Compare ast_Gt) -> SX_SYM "Greater"
      | (ast_Compare ast_Geq) -> SX_SYM "GreaterEq"
      | (ast_AltCompare ast_Lt) -> SX_SYM "AltLess"
      | (ast_AltCompare ast_Leq) -> SX_SYM "AltLessEq"
      | (ast_AltCompare ast_Gt) -> SX_SYM "AltGreater"
      | (ast_AltCompare ast_Geq) -> SX_SYM "AltGreaterEq"`;;

let arithsexp_def = cake_define_list
  [`arithsexp ast_Add = SX_SYM "Add"`;
   `arithsexp ast_Sub = SX_SYM "Sub"`;
   `arithsexp ast_Mul = SX_SYM "Mul"`;
   `arithsexp ast_Div = SX_SYM "Div"`;
   `arithsexp ast_Mod = SX_SYM "Mod"`;
   `arithsexp ast_And = SX_SYM "And"`;
   `arithsexp ast_Xor = SX_SYM "Xor"`;
   `arithsexp ast_Or = SX_SYM "Or"`;
   `arithsexp ast_Not = SX_SYM "Not"`;
   `arithsexp ast_Neg = SX_SYM "Neg"`;
   `arithsexp ast_Abs = SX_SYM "Abs"`;
   `arithsexp ast_Sqrt = SX_SYM "Sqrt"`;
   `arithsexp ast_FMA = SX_SYM "FMA"`];;

let prim_typesexp_def = cake_define
  `prim_typesexp x1 =
      match x1 with
        ast_BoolT -> SX_SYM "BoolT"
      | ast_IntT -> SX_SYM "IntT"
      | ast_CharT -> SX_SYM "CharT"
      | ast_StrT -> SX_SYM "StrT"
      | (ast_WordT ast_W8) -> SX_SYM "Word8T"
      | (ast_WordT ast_W64) -> SX_SYM "Word64T"
      | ast_Float64T -> SX_SYM "Float64T"`;;

let opsexp_def = cake_define
  `opsexp x1 =
        match x1 with
          ast_Shift ast_W8 Lsl n -> SX_CONS (SX_SYM "Shift8Lsl")
            (SX_NUM n)
        | (ast_Shift ast_W8 Lsr n) -> SX_CONS (SX_SYM "Shift8Lsr")
          (SX_NUM n)
        | (ast_Shift ast_W8 Asr n) -> SX_CONS (SX_SYM "Shift8Asr")
          (SX_NUM n)
        | (ast_Shift ast_W8 Ror n) -> SX_CONS (SX_SYM "Shift8Ror")
          (SX_NUM n)
        | (ast_Shift ast_W64 Lsl n) -> SX_CONS (SX_SYM "Shift64Lsl")
          (SX_NUM n)
        | (ast_Shift ast_W64 Lsr n) -> SX_CONS (SX_SYM "Shift64Lsr")
          (SX_NUM n)
        | (ast_Shift ast_W64 Asr n) -> SX_CONS (SX_SYM "Shift64Asr")
          (SX_NUM n)
        | (ast_Shift ast_W64 Ror n) -> SX_CONS (SX_SYM "Shift64Ror")
          (SX_NUM n)
        | ast_Equality -> SX_SYM "Equality"
        | ast_Opapp -> SX_SYM "Opapp"
        | ast_Opassign -> SX_SYM "Opassign"
        | ast_Opref -> SX_SYM "Opref"
        | ast_Opderef -> SX_SYM "Opderef"
        | ast_Aw8alloc -> SX_SYM "Aw8alloc"
        | ast_Aw8sub -> SX_SYM "Aw8sub"
        | ast_Aw8length -> SX_SYM "Aw8length"
        | ast_Aw8update -> SX_SYM "Aw8update"
        | ast_Aw8sub_unsafe -> SX_SYM "Aw8subunsafe"
        | ast_Aw8update_unsafe -> SX_SYM "Aw8updateunsafe"
        | ast_CopyStrStr -> SX_SYM "CopyStrStr"
        | ast_CopyStrAw8 -> SX_SYM "CopyStrAw8"
        | ast_CopyAw8Str -> SX_SYM "CopyAw8Str"
        | ast_CopyAw8Aw8 -> SX_SYM "CopyAw8Aw8"
        | ast_XorAw8Str_unsafe -> SX_SYM "XorAw8Strunsafe"
        | ast_Implode -> SX_SYM "Implode"
        | ast_Explode -> SX_SYM "Explode"
        | ast_Strsub -> SX_SYM "Strsub"
        | ast_Strlen -> SX_SYM "Strlen"
        | ast_Strcat -> SX_SYM "Strcat"
        | ast_VfromList -> SX_SYM "VfromList"
        | ast_Vsub -> SX_SYM "Vsub"
        | ast_Vsub_unsafe -> SX_SYM "Vsubunsafe"
        | ast_Vlength -> SX_SYM "Vlength"
        | ast_ListAppend -> SX_SYM "ListAppend"
        | ast_Aalloc -> SX_SYM "Aalloc"
        | ast_AallocEmpty -> SX_SYM "AallocEmpty"
        | ast_AallocFixed -> SX_SYM "AallocFixed"
        | ast_Asub -> SX_SYM "Asub"
        | ast_Alength -> SX_SYM "Alength"
        | ast_Aupdate -> SX_SYM "Aupdate"
        | ast_Asub_unsafe -> SX_SYM "Asubunsafe"
        | ast_Aupdate_unsafe -> SX_SYM "Aupdateunsafe"
        | ast_ConfigGC -> SX_SYM "ConfigGC"
        | ast_Eval -> SX_SYM "Eval"
        | ast_Env_id -> SX_SYM "Envid"
        | (ast_FFI s) -> SX_CONS (SX_SYM "FFI") (SEXSTR (explode s))
        | (ast_ThunkOp ForceThunk) -> SX_SYM "ForceThunk"
        | (ast_ThunkOp (AllocThunk m)) ->
       SX_CONS (SX_SYM "AllocThunk") (SX_SYM (encode_thunk_mode m))
        | (ast_ThunkOp (UpdateThunk m)) ->
       SX_CONS (SX_SYM "UpdateThunk") (SX_SYM (encode_thunk_mode m))
        | (ast_Arith a prim_type) ->
       SX_CONS (SX_SYM "Arith")
       (SX_CONS (arithsexp a)
               (prim_typesexp prim_type))
        | (ast_FromTo ty1 ty2) ->
       SX_CONS (SX_SYM "FromTo")
       (SX_CONS (prim_typesexp ty1)
               (prim_typesexp ty2))
        | (ast_Test test prim_type) ->
       SX_CONS (SX_SYM "Test")
       (SX_CONS (testsexp test)
               (prim_typesexp prim_type))`;;

let logsexp_def = cake_define_list
  [`logsexp Andalso = SX_SYM "Andalso"`;
   `logsexp Orelse = SX_SYM "Orelse"`];;

let locnsexp_def = cake_define_list
  [`locnsexp (POSN n1 n2) = listsexp (MAP SX_NUM [n1; n2])`;
   `locnsexp UNKNOWNpt = SX_SYM "unk"`;
   `locnsexp EOFpt = SX_SYM "eof"`];;

let locssexp_def = cake_define
  `locssexp (Locs p1 p2) = listsexp (MAP locnsexp [p1; p2])`;;

let expsexp_def = cake_define_list
  [`expsexp (ast_Raise e) = (SX_SYM "Raise"; expsexp e)`;
   `expsexp (ast_Handle e pes) =
      (SX_SYM "Handle"; expsexp e;
       listsexp (MAP (λ(p,e). SX_CONS (patsexp p) (expsexp e))
         pes))`;
   `expsexp (ast_Lit l) = listsexp [SX_SYM "Lit"; litsexp l]`;
   `expsexp (ast_Con cn es) =
      listsexp [SX_SYM "Con"; optsexp (OPTION_MAP idsexp cn);
                listsexp (MAP expsexp es)]`;
   `expsexp (ast_Var id') = listsexp [SX_SYM "Var"; idsexp id']`;
   `expsexp (ast_Fun x e) = listsexp [SX_SYM "Fun"; SEXSTR (explode
  x); expsexp e]`;
   `expsexp (ast_App op es) =
      listsexp [SX_SYM "App"; opsexp op; listsexp (MAP expsexp
        es)]`;
   `expsexp (ast_Log lop e1 e2) = (SX_SYM "Log"; logsexp lop; expsexp
  e1; expsexp e2)`;
   `expsexp (ast_If e1 e2 e3) = (SX_SYM "If"; expsexp e1; expsexp e2;
  expsexp e3)`;
   `expsexp (ast_Mat e pes) =
      (SX_SYM "Mat"; expsexp e;
       listsexp (MAP (λ(p,e). SX_CONS (patsexp p) (expsexp e))
         pes))`;
   `expsexp (ast_Let so e1 e2) =
      (SX_SYM "Let"; optsexp (OPTION_MAP (SEXSTR ∘ explode) so);
        expsexp e1; expsexp e2)`;
   `expsexp (ast_Letrec funs e) =
    (SX_SYM "Letrec";
     listsexp (MAP (λ(x,y,z). SX_CONS (SEXSTR (explode x))
                              (SX_CONS (SEXSTR (explode y)) (expsexp
                                z))) funs);
     expsexp e)`;
   `expsexp (ast_Tannot e t) = (SX_SYM "Tannot"; expsexp e; typesexp
  t)`;
   `expsexp (ast_Lannot e loc) = (SX_SYM "Lannot"; expsexp e;
  locssexp loc)`];;

let type_defsexp_def = cake_define
  `type_defsexp = listsexp o
     MAP (\(xs,x,ls).
       SX_CONS (listsexp (MAP (SEXSTR o explode) xs))
         (SX_CONS (SEXSTR (explode x))
           (listsexp (MAP (\(y,ts). SX_CONS (SEXSTR (explode y))
             (listsexp (MAP typesexp ts))) ls))))`;;

let decsexp_def = cake_define_list
  [`decsexp (Dlet locs p e) =
      (SX_SYM "Dlet"; locssexp locs; patsexp p; expsexp e)`;
   `decsexp (Dletrec locs funs) =
       listsexp [
           SX_SYM "Dletrec";
           locssexp locs;
           listsexp
             (MAP (\(f,x,e). SX_CONS (SEXSTR (explode f)) (SX_CONS
               (SEXSTR (explode x)) (expsexp e)))
              funs)]`;
   `decsexp (Dtype locs td) = (SX_SYM "Dtype"; locssexp locs;
  type_defsexp td)`;
   `decsexp (Dtabbrev locs ns x t) = (SX_SYM "Dtabbrev"; locssexp
  locs; listsexp (MAP (SEXSTR ∘ explode) ns); SEXSTR (explode x);
  typesexp t)`;
   `decsexp (Denv name) = (SX_SYM "Denv"; SEXSTR (explode name))`;
   `decsexp (Dexn locs x ts) =
      (SX_SYM "Dexn"; locssexp locs; SEXSTR (explode x); listsexp
        (MAP typesexp ts))`;
   `decsexp (Dmod name decs) =
      (SX_SYM "Dmod"; SEXSTR (explode name); listsexp (MAP
        decsexp decs))`;
   `decsexp (Dlocal ldecs decs) =
      listsexp [SX_SYM "Dlocal"; listsexp (MAP decsexp ldecs);
                listsexp (MAP decsexp decs)]`];;

(* round trip *)

(* HOL4 ML code, not ported:
val exists_g_tac =
  (fn (g as (asl,w)) =>
    let
      val (x,b) = dest_exists w
      val tm = find_term (fn y => type_of x = type_of y andalso not
        (is_var y)) b
    in EXISTS_TAC tm end g)
*)

(* valid sexps *)
