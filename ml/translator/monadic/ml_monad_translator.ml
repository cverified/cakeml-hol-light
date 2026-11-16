(* ======================================================== *)
(*  ml_monad_translator: ported from HOL4's
    translator/monadic/ml_monad_translatorScript.sml
    A definition theory, with 19 definitions and 131 theorems.
    Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  Defines EvalM and other judgements that are central to the monadic
  translator.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cf.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/patternMatches.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_pmatch.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;
needs "translator/monadic/ml_monad_translatorBase.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_monad_translator"
  ["ast"; "cf"; "cfHeapsBase"; "cfStore"; "cfTactics"; "evaluate";
   "evaluateProps"; "ml_monadBase"; "ml_monad_translatorBase"; "ml_pmatch";
   "ml_prog"; "ml_translator"; "semanticPrimitives"];;

let _ = do_list hide_constant ["ABS"; "Subscript"; "TYPE"; "get_var";
       "set_var"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["vars","vars"];;

(* HOL4 ml_monad_translatorScript.sml:14: the overload CONTAINER, which the
   port expands *)

(* HOL4 ml_monad_translatorScript.sml:18-24: ML code, not ported *)

(* HOL4 ml_monad_translatorScript.sml:26-30: ML code, not ported *)

(* TODO: move *)
let s_with_same_clock = prove
 (`!s. (semanticPrimitives_state_clock_fupd (K
  (semanticPrimitives_state_clock s)) s) = s`,
  CHEAT_TAC);;
add_simp s_with_same_clock;;
(* -- *)

(* GC_ABSORB_L[local] *)
let ml_monad_translator_GC_ABSORB_L = prove
 (`!A B s. (A * B * GC) s ==> (A * GC) s`,
  CHEAT_TAC);;

(* [local] *)
let GC_ABSORB_R = prove
 (`!A B s. (A * GC * B) s ==> (A * GC) s`,
  CHEAT_TAC);;

(* HOL4 ml_monad_translatorScript.sml:60: ML code, not ported *)

(* [local] *)
let REF_EXISTS_LOC = prove
 (`(REF rv v * H) s ==> (?l. rv = semanticPrimitives_Loc T l)`,
  CHEAT_TAC);;

(* [local] *)
let ARRAY_EXISTS_LOC = prove
 (`(ARRAY rv v * H) s ==> (?l. rv = semanticPrimitives_Loc T l)`,
  CHEAT_TAC);;

(* [local] *)
let UNIQUE_CELLS = prove
 (`!p s. !l xv xv' H H'. (cell l xv * H) (st2heap p s) /\ (cell l xv' * H')
  (st2heap p s) ==> xv' = xv`,
  CHEAT_TAC);;

(* Should be moved *)
(* HOL4 ml_monad_translatorScript.sml:83-85: ML code, not ported *)
(* *)

(*********** Comes from cfLetAutoLib.sml ***********************************************)
(* [dest_pure_fact]
   Deconstruct a pure fact (a heap predicate of the form &P) *)
(* HOL4 ml_monad_translatorScript.sml:91-97: the ML values that the
   definitions below antiquote *)
(***************************************************************************************)

(* HOL4 ml_monad_translatorScript.sml:100-109: ML code, not ported *)
          (* For some strange reason, AC_CONV doesn't work *)
(* HOL4 ml_monad_translatorScript.sml:111-115: ML code, not ported *)

(* HOL4 ml_monad_translatorScript.sml:117-121: ML code, not ported *)

(* TODO: use EXTRACT_PURE_FACT_CONV to rewrite EXTRACT_PURE_FACTS_TAC *)
(* HOL4 ml_monad_translatorScript.sml:124-132: a proof *)
(***********************************************************************************************)

(* HOL4 ml_monad_translatorScript.sml:135-136: ML code, not ported *)

(* HOL4 ml_monad_translatorScript.sml:138: the type abbreviation state,
   which the port expands *)

(***)

(*
 * Definition of EvalM
 * `ro`: references only
 *)

let EvalM_def = new_definition
  `EvalM ro env st exp P H <=>
     (!(s:'ffi semanticPrimitives_state).
       REFS_PRED H st s ==>
       (?s2 res st2 ck.
         evaluate (semanticPrimitives_state_clock_fupd (K ck) s) env [exp] =
           (s2,res) /\
         P st (st2,res) /\ REFS_PRED_FRAME ro H (st,s) (st2,s2)))`;;

(* refinement invariant for ``:('a, 'b, 'c) M`` *)
(* HOL4 ml_monad_translatorScript.sml:157: the type abbreviation M, which
   the port expands *)

let MONAD_def = new_definition
  `MONAD (a:'a->semanticPrimitives_v->bool) (b:'b->semanticPrimitives_v->bool)
  (x:'refs->('a,'b)exc#'refs) (state1:'refs)
  ((state2:'refs),(res:(semanticPrimitives_v
  list,semanticPrimitives_v)semanticPrimitives_result)) =
     match (x state1,res) with
       ((M_success y,st),Rval [v]) -> (st = state2) /\ a y v
     | ((M_failure e,st),Rerr (Rraise v)) -> (st = state2) /\
                              b e v
     | _ -> F`;;

(* HOL4 ml_monad_translatorScript.sml:170: the ML values that the
   definitions below antiquote *)

(* return *)
let EvalM_return = prove
 (`!H b. ast_Eval env exp (a x) ==>
         EvalM ro env st exp (MONAD a b (st_ex_return x))
           ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
           (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
           cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* bind *)
let EvalM_bind = prove
 (`(a1 ==> EvalM ro env st e1 (MONAD b c (x:'refs->('b,'c)exc#'refs))
             (H:('refs->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
               (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
               cfHeapsBase_ffi_result) option)) list)) /\
   (!z v. b z v ==> a2 z ==>
      EvalM ro (ml_prog_write name v env) (SND (x st)) e2
        (MONAD a c ((f z):'refs->('a,'c)exc#'refs)) H) ==>
   (a1 /\ (!z. (CONTAINER (FST (x st) = M_success z) ==> a2 z))) ==>
   EvalM ro env st (ast_Let (SOME name) e1 e2) (MONAD a c (st_ex_bind x
     f)) H`,
  CHEAT_TAC);;

(* bind ignore *)
let EvalM_bind_ignore = prove
 (`(EvalM ro env st e1 (MONAD b c (x:'refs->('b,'c)exc#'refs))
          (H:('refs->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
            (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
            cfHeapsBase_ffi_result) option)) list)) /\
   (EvalM ro env (SND (x st)) e2 (MONAD a c (f:'refs->('a,'c)exc#'refs)) H)
     ==>
   EvalM ro env st (ast_Let NONE e1 e2) (MONAD a c (st_ex_ignore_bind x
     f)) H`,
  CHEAT_TAC);;

let EvalM_pure_seq = prove
 (`ast_Eval env e1 (c y) /\
   EvalM ro env st e2 (MONAD a b x)
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
     option)) list)) ==>
   EvalM ro env st (ast_Let NONE e1 e2) (MONAD a b (pure_seq y x))
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* lift ro refinement invariants *)

(* HOL4 ml_monad_translatorScript.sml:286: the type abbreviation H, which
   the port expands *)

let PURE_def = new_definition
  `PURE a (x:'a) (st1:'refs) (st2,(res:(semanticPrimitives_v
  list,semanticPrimitives_v)semanticPrimitives_result)) =
     (?(v:semanticPrimitives_v). (res = Rval [v]) /\ (st1 = st2) /\ a x
       v)`;;

let EqSt_def = new_definition
  `EqSt abs' st = (\x st1 (st2,res). st = st1 /\ abs' x st1 (st2,res))`;;

let state_update_clock_id = prove
 (`(semanticPrimitives_state_refs_fupd (K refs')
  (semanticPrimitives_state_clock_fupd (K (semanticPrimitives_state_clock s))
  s)) = semanticPrimitives_state_refs_fupd (K refs')
    s`,
  CHEAT_TAC);;
add_simp state_update_clock_id;;

let Eval_IMP_PURE = prove
 (`!H env exp P x. ast_Eval env exp (P x) ==> EvalM ro env st exp (PURE P x)
  ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list))`,
  CHEAT_TAC);;

let Eval_IMP_PURE_EvalM_T = prove
 (`!H env exp P x. ast_Eval env exp (P x) ==> EvalM T env st exp (PURE P x)
  ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list))`,
  CHEAT_TAC);;

(* function abstraction and application *)

let ArrowP_def = new_definition
  `ArrowP ro H (a:'a->'refs->'refs#(semanticPrimitives_v
  list,semanticPrimitives_v)semanticPrimitives_result->bool) b f c =
      (!x st1 s1 st2 (res:(semanticPrimitives_v
        list,semanticPrimitives_v)semanticPrimitives_result).
        a x st1 (st2,res) /\ REFS_PRED H st1 s1 ==>
        (?v env exp.
          (st2 = st1) /\
          (res = Rval [v]) /\ semanticPrimitives_do_opapp [c; v] = SOME
            (env,exp) /\
          (!junk. ?st3 s3 res3 ck.
            evaluate (semanticPrimitives_state_clock_fupd (K ck)
              (semanticPrimitives_state_refs_fupd (K (APPEND
              (semanticPrimitives_state_refs s1) junk)) s1))
              env [exp] = (s3,res3) /\
            b (f x) st1 (st3,res3) /\
            REFS_PRED_FRAME ro H (st1,s1) (st3,s3))))`;;

let ArrowM_def = new_definition
  `ArrowM ro H (a:'a->'refs->'refs#(semanticPrimitives_v
  list,semanticPrimitives_v)semanticPrimitives_result->bool)
  (b:'b->'refs->'refs#(semanticPrimitives_v
  list,semanticPrimitives_v)semanticPrimitives_result->bool) =
      (PURE (ArrowP ro H a
        b):('a->'b)->'refs->'refs#(semanticPrimitives_v
        list,semanticPrimitives_v)semanticPrimitives_result->bool)`;;

(* HOL4 ml_monad_translatorScript.sml:344-373: a proof *)

let EvalM_ArrowM = prove
 (`EvalM ro env st x1 ((ArrowM ro H (PURE a) b) f) H ==>
   EvalM ro env st x2 (PURE a x) H ==>
   EvalM ro env st (ast_App ast_Opapp [x1; x2]) (b (f x))
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_ArrowM_EqSt = prove
 (`EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE a) st) b) f) H ==>
   EvalM ro env st x2 (PURE a x) H ==>
   EvalM ro env st (ast_App ast_Opapp [x1; x2]) (b (f x))
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_ArrowM_Eq = prove
 (`EvalM ro env st x1 ((ArrowM ro H (PURE (ml_translator_Eq a x)) b) f) H ==>
   EvalM ro env st x2 (PURE a x) H ==>
   EvalM ro env st (ast_App ast_Opapp [x1; x2]) (b (f x))
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_ArrowM_EqSt_Eq = prove
 (`EvalM ro env st x1 ((ArrowM ro H (EqSt (PURE (ml_translator_Eq a x)) st) b)
  f) H ==>
    EvalM ro env st x2 (PURE a x) H ==>
    EvalM ro env st (ast_App ast_Opapp [x1; x2]) (b (f x))
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_Fun = prove
 (`(!v x. a x v ==> EvalM ro (ml_prog_write name v env) n_st body (b (f x)) H)
  ==>
    EvalM ro env st (ast_Fun name body) (ArrowM ro H (EqSt (PURE a) n_st)
      b f)
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_Fun_Var_intro = prove
 (`EvalM ro cl_env st (ast_Fun n exp) (PURE P f) H ==>
   (!name. LOOKUP_VAR name env (semanticPrimitives_Closure cl_env n exp) ==>
          EvalM ro env st (ast_Var (Short name)) (PURE P f)
            ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
            (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
            cfHeapsBase_ffi_result) option)) list)))`,
  CHEAT_TAC);;

let EvalM_Fun_Eq = prove
 (`(!v. a x v ==> EvalM ro (ml_prog_write name v env) n_st body (b (f x)) H)
  ==>
   EvalM ro env st (ast_Fun name body)
     ((ArrowM ro H (EqSt (PURE (ml_translator_Eq a x)) n_st) b) f)
       ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;


(* More proofs *)

let LOOKUP_VAR_EvalM_ArrowM_IMP = prove
 (`(!st env. LOOKUP_VAR n env v ==>
             EvalM ro env st (ast_Var (Short n)) (ArrowM ro H a b f) H) ==>
    ArrowP ro
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list)) a b f v`,
  CHEAT_TAC);;

let EvalM_Var_SIMP = prove
 (`EvalM ro (ml_prog_write n x env) st (ast_Var (Short y)) P
  (H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) =
    if n = y then EvalM ro (ml_prog_write n x env) st (ast_Var (Short y)) P
      H
             else EvalM ro env st (ast_Var (Short y)) P H`,
  CHEAT_TAC);;

let EvalM_Var_SIMP_ArrowM = prove
 (`(!st. EvalM ro (ml_prog_write nv v env) st (ast_Var (Short n)) (ArrowM ro H
  a b x) H) =
    if nv = n then ArrowP ro H a b x v
    else (!st. EvalM ro env st (ast_Var (Short n)) (ArrowM ro H a b x)
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list)))`,
  CHEAT_TAC);;

let EvalM_Recclosure_ALT = prove
 (`!H funs fname name body.
     ALL_DISTINCT (MAP (\(f,x,e). f) funs) ==>
     (!st v.
        a n v ==>
        EvalM ro (ml_prog_write name v (write_rec funs env2 env2)) st body
          (b (f n)) H) ==>
     LOOKUP_VAR fname env (semanticPrimitives_Recclosure env2 funs fname)
       ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (ast_Var (Short fname)) ((ArrowM ro H (PURE
       (ml_translator_Eq a n)) b) f)
       ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_Recclosure_ALT2 = prove
 (`!H funs fname.
     A n_st ==>
     (!name body.
     ALL_DISTINCT (MAP (\(f,x,e). f) funs) ==>
     (!st v.
        A st ==>
        a n v ==>
        EvalM ro (ml_prog_write name v (write_rec funs env2 env2)) st body
          (b (f n)) H) ==>
     LOOKUP_VAR fname env (semanticPrimitives_Recclosure env2 funs fname)
       ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (ast_Var (Short fname))
       ((ArrowM ro H (EqSt (PURE (ml_translator_Eq a n)) n_st) b) f)
         ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
         (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list)))`,
  CHEAT_TAC);;

let EvalM_Recclosure_ALT3 = prove
 (`!H funs fname name body.
     (!st v.
        A st ==>
        a n v ==>
        EvalM ro (ml_prog_write name v (write_rec funs env2 env2)) st body
          (b (f n)) H) ==>
     A n_st ==>
     ALL_DISTINCT (MAP (\(f,x,e). f) funs) ==>
     LOOKUP_VAR fname env (semanticPrimitives_Recclosure env2 funs fname)
       ==>
     find_recfun fname funs = SOME (name,body) ==>
     EvalM ro env st (ast_Var (Short fname))
       ((ArrowM ro H (EqSt (PURE (ml_translator_Eq a n)) n_st) b) f)
         ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
         (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_Recclosure = prove
 (`!H. (!st v. a n v ==>
         EvalM ro (ml_prog_write name v (write_rec [(fname,name,body)] env2
           env2))
               st body (b (f n)) H) ==>
    LOOKUP_VAR fname env (semanticPrimitives_Recclosure env2
      [(fname,name,body)] fname) ==>
    EvalM ro env st (ast_Var (Short fname)) ((ArrowM ro H (PURE
      (ml_translator_Eq a n)) b) f)
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_Eq_Recclosure = prove
 (`LOOKUP_VAR name env (semanticPrimitives_Recclosure x1 x2 x3) ==>
    (ArrowP ro H a b f (semanticPrimitives_Recclosure x1 x2 x3) =
     (!st. EvalM ro env st (ast_Var (Short name)) (ArrowM ro H a b f)
       ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list))))`,
  CHEAT_TAC);;

let EvalM_Var_ArrowP = prove
 (`(!st. EvalM ro env st (ast_Var (Short n)) (ArrowM ro H (PURE a) b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list)) (PURE a) b x v`,
  CHEAT_TAC);;

let EvalM_Var_ArrowP_EqSt = prove
 (`(!st. EvalM ro env st (ast_Var (Short n)) (ArrowM ro H (EqSt (PURE a) n_st)
  b x) H) ==>
   LOOKUP_VAR n env v ==>
   ArrowP ro
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list)) (EqSt (PURE a) n_st) b x v`,
  CHEAT_TAC);;

(* Eq simps *)

let EvalM_FUN_FORALL = prove
 (`(!x. EvalM ro env st exp (PURE (P x) f) H) ==>
    EvalM ro env st exp (PURE (FUN_FORALL (\x. P x)) f)
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_FUN_FORALL_EQ = prove
 (`(!x. EvalM ro env st exp (PURE (P x) f) H) =
    EvalM ro env st exp (PURE (FUN_FORALL (\x. P x)) f)
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* [local] *)
let M_FUN_FORALL_PUSH1 = prove
 (`(FUN_FORALL (\x. ArrowP ro
  ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) a (PURE (b x)))) =
    (ArrowP ro H a (PURE (FUN_FORALL (\x. b x))))`,
  CHEAT_TAC);;

let M_FUN_FORALL_PUSH2 = prove
 (`(FUN_FORALL (\x. ArrowP ro H ((PURE (a x))) b)) =
       (ArrowP ro
         ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
         (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list)) (PURE (FUN_EXISTS (\x. a
         x))) b)`,
  CHEAT_TAC);;

let M_FUN_FORALL_PUSH3 = prove
 (`(FUN_FORALL (\st. ArrowP ro H (EqSt a st) b)) =
       (ArrowP ro
         ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
         (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list)) a b)`,
  CHEAT_TAC);;

(* FUN_EXISTS_Eq *)
let ml_monad_translator_FUN_EXISTS_Eq = prove
 (`(FUN_EXISTS (\x. ml_translator_Eq a x)) = a`,
  CHEAT_TAC);;

let M_FUN_QUANT_SIMP =
  end_itlist CONJ [ml_monad_translator_FUN_EXISTS_Eq; M_FUN_FORALL_PUSH1;
  M_FUN_FORALL_PUSH2; M_FUN_FORALL_PUSH3];;

let EvalM_Eq = prove
 (`EvalM ro env st exp (PURE a x) H ==> EvalM ro env st exp (PURE
  (ml_translator_Eq a x) x)
  ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list))`,
  CHEAT_TAC);;

let ArrowM_EqSt_elim = prove
 (`(!st_v. EvalM ro env st exp (ArrowM ro H (EqSt a st_v) b f) H) ==>
   EvalM ro env st exp (ArrowM ro H a b f)
     ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
     list#(mlstring->word8 list->word8 list->ffi->(ffi
     cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let ArrowP_EqSt_elim = prove
 (`(!st_v. ArrowP ro H (EqSt a st_v) b f v) ==> ArrowP ro
  ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list)) a b f v`,
  CHEAT_TAC);;

(* otherwise *)

let EvalM_otherwise = prove
 (`!H b n.
     ((a1 ==> EvalM ro env st exp1 (MONAD a b x1) H) /\
     (!st i. a2 st ==> EvalM ro (ml_prog_write n i env) st exp2 (MONAD a b
       x2) H)) ==>
     (a1 /\ (!st'. (CONTAINER (SND (x1 st) = st') ==> a2 st'))) ==>
     EvalM ro env st (ast_Handle exp1 [(ast_Pvar n,exp2)])
       (MONAD a b (otherwise x1 x2))
         ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
         (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* if *)

let EvalM_If = prove
 (`!H.
     (a1 ==> ast_Eval env x1 (BOOL b1)) /\
     (a2 ==> EvalM ro env st x2 (a b2) H) /\
     (a3 ==> EvalM ro env st x3 (a b3) H) ==>
     (a1 /\ (CONTAINER b1 ==> a2) /\ (~(CONTAINER b1) ==> a3) ==>
     EvalM ro env st (ast_If x1 x2 x3) (a (if b1 then b2 else b3))
       ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list)))`,
  CHEAT_TAC);;

(* Let *)

let EvalM_Let = prove
 (`!H.
    ast_Eval env exp (a res) /\
    (!v. a res v ==> EvalM ro (ml_prog_write name v env) st body (b (f res))
      H) ==>
    EvalM ro env st (ast_Let (SOME name) exp body) (b (LET f res))
      ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi
      cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* PMATCH *)

let EvalM_PMATCH_NIL = prove
 (`!H b x xv a.
      ast_Eval env x (a xv) ==>
      pmatch_all_no_type_error (sem_env_c env) a ([]:(ast_pat#ast_exp) list)
        /\
      (CONTAINER F ==>
       EvalM ro env st (ast_Mat x []) (b (PMATCH xv []))
         ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
         (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list)))`,
  CHEAT_TAC);;

let EvalM_PMATCH = prove
 (`!H b a x xv.
      ALL_DISTINCT (ast_pat_bindings pt) ==>
      (!v1 v2. pat v1 = pat v2 ==> v1 = v2) ==>
      ast_Eval env x (a xv) ==>
      (pt1 xv ==> EvalM ro env st (ast_Mat x ys) (b (PMATCH xv yrs)) H) ==>
      EvalPatRel env a pt pat ==>
      (!env2 vars'.
        EvalPatBind env a pt pat vars' env2 /\ pt2 vars' ==>
        EvalM ro env2 st e (b (res vars')) H) ==>
      pmatch_all_no_type_error (sem_env_c env) a ys ==>
      pmatch_all_no_type_error (sem_env_c env) a (CONS (pt,e) ys) /\
      ((!vars'. PMATCH_ROW_COND pat (K T) xv vars' ==> pt2 vars') /\
       ((!vars'. ~(PMATCH_ROW_COND pat (K T) xv vars')) ==> pt1 xv) ==>
       EvalM ro env st (ast_Mat x (CONS (pt,e) ys))
         (b (PMATCH xv (CONS (PMATCH_ROW pat (K T) res) yrs)))
           ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring,ffi)fmap)#
           (mlstring list#(mlstring->word8 list->word8 list->ffi->(ffi
           cfHeapsBase_ffi_result) option)) list)))`,
  CHEAT_TAC);;

(* Exception handling *)
let ml_monad_translator_write_list_def,ml_monad_translator_write_list_ind =
  define_guess
  `(ml_monad_translator_write_list [] [] env = env) /\
   (ml_monad_translator_write_list (CONS n nl) (CONS v vl) env =
    ml_monad_translator_write_list nl vl (ml_prog_write n v env))`;;

(* [local] *)
let pats_bindings_MAP_Pvar = prove
 (`!bind_names.
   ast_pats_bindings (MAP (\x. ast_Pvar x) bind_names) =
   (REVERSE bind_names)`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_pats_bindings = prove
 (`!bind_names. ALL_DISTINCT bind_names ==>
   ALL_DISTINCT (ast_pats_bindings (MAP (\x. ast_Pvar x) bind_names))`,
  CHEAT_TAC);;

(* pmatch_list_MAP_Pvar[local] *)
let ml_monad_translator_pmatch_list_MAP_Pvar = prove
 (`!bind_names paramsv env already_bound s.
   LENGTH paramsv = LENGTH bind_names ==>
   semanticPrimitives_pmatch_list env s (MAP (\x. ast_Pvar x) bind_names)
     paramsv already_bound = Match (APPEND (REVERSE (ZIP bind_names paramsv))
     already_bound)`,
  CHEAT_TAC);;

(* [local] *)
let nsAppend_append = prove
 (`!a b env. nsAppend (Bind (APPEND a b) []) env = nsAppend (Bind a [])
  (nsAppend (Bind b []) env)`,
  CHEAT_TAC);;

(* [local] *)
let write_list_eq = prove
 (`!bind_names paramsv l1 l2 cenv.
   LENGTH paramsv = LENGTH bind_names ==>
   ml_monad_translator_write_list bind_names paramsv (sem_env (Bind l1 l2)
     cenv) = sem_env (Bind (APPEND (REVERSE (ZIP bind_names paramsv)) l1) l2)
     cenv`,
  CHEAT_TAC);;

(* [local] *)
let nsAppend_write_list_eq = prove
 (`!bind_names paramsv env.
   LENGTH paramsv = LENGTH bind_names ==> sem_env_v_fupd (K (nsAppend
     (alist_to_ns (REVERSE (ZIP bind_names paramsv))) (sem_env_v env)))
   env = ml_monad_translator_write_list bind_names paramsv env`,
  CHEAT_TAC);;

let EvalM_handle = prove
 (`!cons_name stamp CORRECT_CONS PARAMS_CONDITIONS EXN_TYPE
    handle_fun x1 x2 arity a2 bind_names a H.
   (!s E s1.
      CORRECT_CONS E ==>
      x1 s = (M_failure E,s1) ==>
      handle_fun x1 x2 s = x2 E s1) ==>
   (!s.
     (!E s1.
        CORRECT_CONS E ==> ~(x1 s = (M_failure E,s1))) ==>
        handle_fun x1 x2 s = x1 s) ==>
   (!E ev. EXN_TYPE E ev ==>
           CORRECT_CONS E ==>
    (?paramsv.
    ev = semanticPrimitives_Conv (SOME (ExnStamp stamp)) paramsv /\
    PARAMS_CONDITIONS E paramsv /\ LENGTH paramsv = arity)) ==>
   (!E ev.
      EXN_TYPE E ev ==>
      ~(CORRECT_CONS E) ==>
      (?paramsv stamp_1.
      ev = semanticPrimitives_Conv (SOME (ExnStamp stamp_1)) paramsv
        /\ ~(stamp_1 = stamp))) ==>
   ALL_DISTINCT bind_names ==>
   LENGTH bind_names = arity ==>
   lookup_cons cons_name env = SOME (arity,ExnStamp stamp) ==>
     ((a1 ==> EvalM ro env st exp1 (MONAD a EXN_TYPE x1) H) /\
      (!st E paramsv.
         PARAMS_CONDITIONS E paramsv ==>
         a2 st E ==>
         EvalM ro (ml_monad_translator_write_list bind_names paramsv env) st
           exp2
           (MONAD a EXN_TYPE (x2 E)) H)) ==>
      (!st' E.
         a1 /\
         (CONTAINER (x1 st = (M_failure E,st') /\ CORRECT_CONS E) ==> a2 st'
           E)) ==>
       EvalM ro env st
         (ast_Handle exp1 [(ast_Pcon (SOME cons_name)
                             (MAP (\x. ast_Pvar x) bind_names),exp2)])
         (MONAD a EXN_TYPE (handle_fun x1 x2)) H`,
  CHEAT_TAC);;

let ZIP3_def,ZIP3_ind = define_guess
  `(ZIP3 ([],[],[]) = []) /\
   (ZIP3 (CONS x1 l1,CONS x2 l2,CONS x3 l3) = CONS (x1,x2,x3) (ZIP3
    (l1,l2,l3)))`;;

let LIST_CONJ_def = define_cases
  `(LIST_CONJ [] = T) /\
   (LIST_CONJ (CONS x l) = (x /\ LIST_CONJ l))`;;

(* [local] *)
let LIST_CONJ_APPEND = prove
 (`!a b. LIST_CONJ (APPEND a b) = (LIST_CONJ a /\ LIST_CONJ b)`,
  CHEAT_TAC);;

(* [local] *)
let LIST_CONJ_REVERSE = prove
 (`!x. LIST_CONJ (REVERSE x) = LIST_CONJ x`,
  CHEAT_TAC);;

(* [local] *)
let LIST_CONJ_Eval = prove
 (`!xs Ps (s:'d semanticPrimitives_state).
     LIST_CONJ (MAP (\(exp,P). ast_Eval env exp P) (ZIP xs Ps)) /\
     LENGTH xs = LENGTH Ps ==>
     (?ck vs junk.
        evaluate (semanticPrimitives_state_clock_fupd (K ck) s) env xs =
          (semanticPrimitives_state_refs_fupd (K (APPEND
            (semanticPrimitives_state_refs s) junk)) s,Rval vs) /\ ALL2 (\f
            x. f x) Ps vs)`,
  CHEAT_TAC);;

let LIST_REL_EQ_LIST_CONJ_MAP = prove
 (`!xs ys.
      LENGTH xs = LENGTH ys ==>
      ALL2 (\f x. f x) xs ys =
      LIST_CONJ (MAP (\(P,v). P v) (ZIP xs ys))`,
  CHEAT_TAC);;

let EvalM_raise = prove
 (`!cons_name stamp EXN_TYPE EVAL_CONDS arity E exprs f a H.
   (!values.
      LENGTH values = arity ==>
      LIST_CONJ (MAP (\(P,v). P v) (ZIP EVAL_CONDS values)) ==>
      EXN_TYPE E (semanticPrimitives_Conv (SOME (ExnStamp stamp)) values))
        ==>
   f st = (M_failure E,st) ==>
   LENGTH exprs = arity ==>
   LENGTH EVAL_CONDS = arity ==>
   lookup_cons cons_name env = SOME (arity,ExnStamp stamp) ==>
   LIST_CONJ (MAP (\(exp,P). ast_Eval env exp P) (ZIP exprs EVAL_CONDS)) ==>
   EvalM ro env st (ast_Raise (ast_Con (SOME cons_name) exprs))
     (MONAD a EXN_TYPE f) H`,
  CHEAT_TAC);;

(* read and update refs *)

let EvalM_read_heap = prove
 (`!vname loc TYPE' EXC_TYPE H get_var.
    (nsLookup (sem_env_v env) (Short vname) = SOME loc) ==>
    EvalM ro env st (ast_App ast_Opderef [ast_Var (Short vname)])
    (MONAD TYPE' EXC_TYPE (\refs. (M_success (get_var refs),refs)))
    ((\refs. REF_REL TYPE' loc (get_var refs) * H
      refs),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

let EvalM_write_heap = prove
 (`!vname loc TYPE' PINV EXC_TYPE H get_var set_var x exp env.
   (!refs x. get_var (set_var x refs) = x) ==>
   (!refs x. H (set_var x refs) = H refs) ==>
   nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
   CONTAINER (PINV st ==> PINV (set_var x st)) ==>
   ast_Eval env exp (TYPE' x) ==>
   EvalM ro env st (ast_App ast_Opassign [ast_Var (Short vname); exp])
   ((MONAD UNIT_TYPE EXC_TYPE) (\refs. (M_success one,set_var x refs)))
   ((\refs. REF_REL TYPE' loc (get_var refs) * H refs * &(PINV
     refs)),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* Dynamic allocation of references *)

let STATE_REF_def = new_definition
  `STATE_REF A r x = SEP_EXISTS (\v. REF r v * &(A x v))`;;

let STATE_REFS_def,STATE_REFS_ind = define_guess
  `(STATE_REFS A [] [] = emp) /\
   (STATE_REFS A (CONS r refs) (CONS x state) = STATE_REF A r x *
    STATE_REFS A refs state) /\
   (STATE_REFS A [] (CONS x state) = &F) /\
   (STATE_REFS A (CONS r refs) [] = &F)`;;

let RES_MONAD = new_definition
  `RES_MONAD A = MONAD A (\x v. F)`;;

(* Validity of a store extension *)
(* [local] *)
let valid_state_refs_frame_extension = prove
 (`!H junk. A (cons x) res ==>
             (STATE_REFS A ptrs state * H) (st2heap
               (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
               list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
               list) s) ==>
     (STATE_REFS A (CONS (semanticPrimitives_Loc T (LENGTH (APPEND
       (semanticPrimitives_state_refs s) junk))) ptrs)
      (CONS (cons x) state) * H * GC) (st2heap p
         (semanticPrimitives_state_refs_fupd (K (APPEND (APPEND
           (semanticPrimitives_state_refs s) junk) [semanticPrimitives_Refv
           res])) s))`,
  CHEAT_TAC);;

(* [local] *)
let valid_state_refs_extension = prove
 (`A (cons x) res ==>
    REFS_PRED (STATE_REFS A ptrs,(p:('ffi->(mlstring,ffi)fmap)#(mlstring
      list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
      option)) list)) refs s ==>
    REFS_PRED (STATE_REFS A (CONS (semanticPrimitives_Loc T (LENGTH (APPEND
      (semanticPrimitives_state_refs s) junk))) ptrs),p)
              (CONS (cons x) refs)
              (semanticPrimitives_state_refs_fupd (K (APPEND (APPEND
                (semanticPrimitives_state_refs s) junk)
                [semanticPrimitives_Refv res])) s)`,
  CHEAT_TAC);;

(* [local] *)
let STATE_REFS_LENGTH = prove
 (`!ptrs state H.
    (STATE_REFS A ptrs state * H) s ==> LENGTH ptrs = LENGTH state`,
  CHEAT_TAC);;

(* [local] *)
let valid_state_refs_reduction = prove
 (`(STATE_REFS A (CONS rv ptrs) refs * H * GC) s ==>
    (STATE_REFS A ptrs (TL refs) * H * GC) s`,
  CHEAT_TAC);;

(* Validity of ref_bind *)

let EvalM_ref_bind = prove
 (`ast_Eval env xexpr (A (cons x)) ==>
   (!rv r.
      EvalM ro (ml_prog_write rname rv env) (CONS (cons x) st) exp
        (MONAD TYPE MON_EXN_TYPE (f r))
        (STATE_REFS A (CONS rv ptrs),(p:('ffi->(mlstring,ffi)fmap)#(mlstring
          list#(mlstring->word8 list->word8 list->ffi->(ffi
          cfHeapsBase_ffi_result) option)) list))) ==>
   EvalM ro env st (ast_Let (SOME rname) (ast_App ast_Opref [xexpr]) exp)
     (MONAD TYPE MON_EXN_TYPE (ref_bind (Mref cons x) f (Mpop_ref e)))
     (STATE_REFS A ptrs,p)`,
  CHEAT_TAC);;

(* Validity of a deref operation *)
(* [local] *)
let STATE_REFS_EXTRACT = prove
 (`!ptrs1 r ptrs2 refs TYPE' H (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s.
    ((STATE_REFS TYPE' (APPEND (APPEND ptrs1 [r]) ptrs2) refs) * H) (st2heap
      p s) ==>
    ((STATE_REFS TYPE' ptrs1 (TAKE (LENGTH ptrs1) refs) *
    (STATE_REF TYPE' r (EL (LENGTH ptrs1) refs)) *
    (STATE_REFS TYPE' ptrs2 (DROP (LENGTH ptrs1 + 1) refs)) * H)) (st2heap
      p s)`,
  CHEAT_TAC);;

(* [local] *)
let STATE_REFS_EXTRACT_2 = prove
 (`!ptrs1 r ptrs2 refs1 x refs2 TYPE' H (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s.
   LENGTH ptrs1 = LENGTH refs1 ==>
   LENGTH ptrs2 = LENGTH refs2 ==>
   (STATE_REFS TYPE' (APPEND (APPEND ptrs1 [r]) ptrs2) (APPEND (APPEND refs1
     [x]) refs2) * H) (st2heap p s) ==>
   (STATE_REFS TYPE' ptrs1 refs1 *
   STATE_REF TYPE' r x *
   STATE_REFS TYPE' ptrs2 refs2 *
   H) (st2heap p s)`,
  CHEAT_TAC);;

(* [local] *)
let STATE_REFS_RECONSTRUCT = prove
 (`!ptrs1 r ptrs2 refs1 y refs2 TYPE' H (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s.
   ((STATE_REFS TYPE' ptrs1 refs1) *
   (STATE_REF TYPE' r y) *
   (STATE_REFS TYPE' ptrs2 refs2) *
   H) (st2heap p s) ==>
   ((STATE_REFS TYPE' (APPEND (APPEND ptrs1 [r]) ptrs2) (APPEND (APPEND
     refs1 [y]) refs2)) * H) (st2heap p s)`,
  CHEAT_TAC);;

let STATE_REFS_DECOMPOSE = prove
 (`!ptrs1 r ptrs2 refs TYPE' H (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s. ((STATE_REFS TYPE' (APPEND (APPEND ptrs1 [r]) ptrs2) refs)
  * H) (st2heap p s) <=>
   (?refs1 y refs2.
   refs = APPEND (APPEND refs1 [y]) refs2 /\
   ((STATE_REFS TYPE' ptrs1 refs1 *
   (STATE_REF TYPE' r y) *
   (STATE_REFS TYPE' ptrs2 refs2) *
   H)) (st2heap p s))`,
  CHEAT_TAC);;

let STATE_REFS_DECOMPOSE_2 = prove
 (`!ptrs1 r ptrs2 refs1 x refs2 TYPE' H (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s.
   LENGTH ptrs1 = LENGTH refs1 ==>
   LENGTH ptrs2 = LENGTH refs2 ==>
   (((STATE_REFS TYPE' (APPEND (APPEND ptrs1 [r]) ptrs2) (APPEND (APPEND
     refs1 [x]) refs2)) * H) (st2heap p s) <=>
   ((STATE_REFS TYPE' ptrs1 refs1 *
   (STATE_REF TYPE' r x) *
   (STATE_REFS TYPE' ptrs2 refs2) *
   H)) (st2heap p s))`,
  CHEAT_TAC);;

let store_lookup_CELL_st2heap = prove
 (`(cell l res * H) (st2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s) ==> store_lookup l (APPEND (semanticPrimitives_state_refs
  s) junk) = SOME res`,
  CHEAT_TAC);;

let store_lookup_REF_st2heap = prove
 (`(REF (semanticPrimitives_Loc T l) v * H) (st2heap
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) s) ==> store_lookup
  l (semanticPrimitives_state_refs s) = SOME (semanticPrimitives_Refv v)`,
  CHEAT_TAC);;

let store_lookup_REF_st2heap_junk = prove
 (`(REF (semanticPrimitives_Loc T l) v * H) (st2heap
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) s) ==> store_lookup
  l (APPEND (semanticPrimitives_state_refs s) junk) = SOME
  (semanticPrimitives_Refv v)`,
  CHEAT_TAC);;

let store_lookup_ARRAY_st2heap = prove
 (`(ARRAY (semanticPrimitives_Loc T l) av * H) (st2heap
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) s) ==> store_lookup
  l (semanticPrimitives_state_refs s) = SOME (semanticPrimitives_Varray av)`,
  CHEAT_TAC);;

let EvalM_Mdref = prove
 (`nsLookup (sem_env_v env) (Short rname) = SOME rv ==>
   r = LENGTH ptrs2 ==>
   EvalM ro env st (ast_App ast_Opderef [ast_Var (Short rname)])
   (MONAD TYPE (\x v. F) (Mdref e (StoreRef r)))
    (STATE_REFS TYPE (APPEND (APPEND ptrs1 [rv])
      ptrs2),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* Validity of an assigment operation *)
let store_assign_REF_st2heap = prove
 (`(REF (semanticPrimitives_Loc T l) v * H) (st2heap
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) s) ==>
   store_assign l (semanticPrimitives_Refv res) (APPEND
     (semanticPrimitives_state_refs s) junk) = SOME (LUPDATE
     (semanticPrimitives_Refv res) l (APPEND (semanticPrimitives_state_refs
     s) junk))`,
  CHEAT_TAC);;

(* [local] *)
let UPDATE_STATE_REFS = prove
 (`!ptrs2 l ptrs1 x res TYPE' junk refs p s.
   TYPE' x res ==>
   REFS_PRED_FRAME ro (STATE_REFS TYPE' (APPEND (APPEND ptrs1
     [semanticPrimitives_Loc T l])
     ptrs2),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))
     (refs,s)
   (ref_assign (LENGTH ptrs2) x refs,semanticPrimitives_state_refs_fupd (K
     (LUPDATE (semanticPrimitives_Refv res) l (APPEND
     (semanticPrimitives_state_refs s) junk))) s)`,
  CHEAT_TAC);;

let EvalM_Mref_assign = prove
 (`nsLookup (sem_env_v env) (Short rname) = SOME rv ==>
   r = LENGTH ptrs2 ==>
   ast_Eval env xexpr (TYPE x) ==>
   EvalM ro env st (ast_App ast_Opassign [ast_Var (Short rname); xexpr])
   (MONAD UNIT_TYPE (\x v. F) (Mref_assign e (StoreRef r) x)) (STATE_REFS
     TYPE (APPEND (APPEND ptrs1 [rv])
     ptrs2),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* Allocation of the initial store for dynamic references *)
let STATE_REFS_EXTEND = prove
 (`!H s refs. (STATE_REFS A ptrs refs * H) (st2heap
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) s) ==>
   (!x xv. A x xv ==>
   (STATE_REFS A (CONS (semanticPrimitives_Loc T (LENGTH
     (semanticPrimitives_state_refs s))) ptrs) (CONS x refs) * H) (st2heap p
     (semanticPrimitives_state_refs_fupd (K (APPEND
     (semanticPrimitives_state_refs s) [semanticPrimitives_Refv xv])) s)))`,
  CHEAT_TAC);;

(* Resizable arrays *)
(* [local] *)
let ABS_NUM_EQ = prove
 (`num_of_int (abs (&n)) = n`,
  CHEAT_TAC);;

(* [local] *)
let do_app_Opderef_REF = prove
 (`(REF (semanticPrimitives_Loc T loc) v * H refs) (st2heap
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) s) ==>
   (!junk. semanticPrimitives_do_app (APPEND (semanticPrimitives_state_refs
     s) junk,semanticPrimitives_state_ffi s) ast_Opderef
     [semanticPrimitives_Loc T loc] =
     SOME ((APPEND (semanticPrimitives_state_refs s)
       junk,semanticPrimitives_state_ffi s),Rval v))`,
  CHEAT_TAC);;

(* [local] *)
let do_app_Alength_ARRAY = prove
 (`(ARRAY rv v * H) (st2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s) ==>
   semanticPrimitives_do_app (semanticPrimitives_state_refs
     s,semanticPrimitives_state_ffi s) ast_Alength [rv] =
   SOME ((semanticPrimitives_state_refs s,semanticPrimitives_state_ffi
     s),Rval (semanticPrimitives_Litv (ast_IntLit (int_of_num (LENGTH v)))))`,
  CHEAT_TAC);;

let EvalM_R_Marray_length = prove
 (`!vname loc TYPE' EXC_TYPE H get_arr x env.
    nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
    EvalM ro env st (ast_App ast_Alength [ast_App ast_Opderef [ast_Var
      (Short vname)]])
    ((MONAD NUM EXC_TYPE) (Marray_length get_arr))
    ((\refs. RARRAY_REL TYPE' loc (get_arr refs) * H
      refs),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* HOL4 ml_monad_translatorScript.sml:1993-1994: the ML values that the
   definitions below antiquote *)

(* [local] *)
let do_app_Asub_ARRAY = prove
 (`(ARRAY rv v * H) (st2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) s) ==>
   (!junk. semanticPrimitives_do_app (APPEND (semanticPrimitives_state_refs
     s) junk,semanticPrimitives_state_ffi s) ast_Asub [rv;
     semanticPrimitives_Litv (ast_IntLit (&n))] =
     (if n < LENGTH v then SOME ((APPEND (semanticPrimitives_state_refs s)
       junk,semanticPrimitives_state_ffi s),Rval (EL n v))
     else SOME ((APPEND (semanticPrimitives_state_refs s)
       junk,semanticPrimitives_state_ffi s),Rerr (Rraise (sub_exn_v)))))`,
  CHEAT_TAC);;

(* HOL4 ml_monad_translatorScript.sml:2010-2013: ML code, not ported *)

(* HOL4 ml_monad_translatorScript.sml:2015-2018: ML code, not ported *)

(* HOL4 ml_monad_translatorScript.sml:2020-2070: a theorem whose statement
   the port cannot state yet: EvalM_R_Marray_sub_subscript *)

(* HOL4 ml_monad_translatorScript.sml:2072-2134: a theorem whose statement
   the port cannot state yet: EvalM_R_Marray_sub_handle *)

(* HOL4 ml_monad_translatorScript.sml:2136-2242: a theorem whose statement
   the port cannot state yet: EvalM_R_Marray_update_subscript *)

(* HOL4 ml_monad_translatorScript.sml:2244-2366: a theorem whose statement
   the port cannot state yet: EvalM_R_Marray_update_handle *)

(* [local] *)
let HPROP_TO_GC_R = prove
 (`(A * B) s ==> (A * GC) s`,
  CHEAT_TAC);;

(* [local] *)
let HPROP_TO_GC_L = prove
 (`(A * B) s ==> (GC * B) s`,
  CHEAT_TAC);;

let EvalM_R_Marray_alloc = prove
 (`!vname loc TYPE' EXC_TYPE H get_arr set_arr n x env nexp xexp.
   nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
   (!refs x. get_arr (set_arr x refs) = x) ==>
   (!refs x. H (set_arr x refs) = H refs) ==>
   ast_Eval env nexp (NUM n) ==>
   ast_Eval env xexp (TYPE' x) ==>
   EvalM ro env st (ast_App ast_Opassign [ast_Var (Short vname); ast_App
     ast_Aalloc [nexp; xexp]])
   ((MONAD UNIT_TYPE EXC_TYPE) (Marray_alloc set_arr n x))
   ((\refs. RARRAY_REL TYPE' loc (get_arr refs) * H
     refs),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* Fixed-size arrays *)
let EvalM_F_Marray_length = prove
 (`!vname loc TYPE' EXC_TYPE H get_arr x env.
    nsLookup (sem_env_v env) (Short vname) = SOME loc ==>
    EvalM ro env st (ast_App ast_Alength [ast_Var (Short vname)])
    ((MONAD NUM EXC_TYPE) (Marray_length get_arr))
    ((\refs. ARRAY_REL TYPE' loc (get_arr refs) * H
      refs),(p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list))`,
  CHEAT_TAC);;

(* HOL4 ml_monad_translatorScript.sml:2495-2534: a theorem whose statement
   the port cannot state yet: EvalM_F_Marray_sub_subscript *)

(* HOL4 ml_monad_translatorScript.sml:2536-2595: a theorem whose statement
   the port cannot state yet: EvalM_F_Marray_sub_handle *)

(* HOL4 ml_monad_translatorScript.sml:2597-2678: a theorem whose statement
   the port cannot state yet: EvalM_F_Marray_update_subscript *)

(* HOL4 ml_monad_translatorScript.sml:2680-2769: a theorem whose statement
   the port cannot state yet: EvalM_F_Marray_update_handle *)

(* TODO: implement support for 2d arrays *)
let ARRAY2D_def = new_definition
  `ARRAY2D av l = SEP_EXISTS (\fl. ARRAY av fl * &(fl = FLAT l))`;;

let RARRAY2D_def = new_definition
  `RARRAY2D rv l = SEP_EXISTS (\av. REF rv av * ARRAY2D av l)`;;

(* TODO: implement support for n-dimensional arrays? *)

(* translation of cases and cons terms *)

let IMP_EvalM_Mat_cases = prove
 (`!st a (r1:'b) env exp r2 y.
      ast_Eval env exp (a r1) /\
      (match y with INL (vars',exp) ->
                   (ALL_DISTINCT (ast_pats_bindings (MAP ast_Pvar vars')) /\
                    (!v. a r1 v ==>
                         (?name vals t.
                           v = semanticPrimitives_Conv NONE vals /\
                           LENGTH vals = LENGTH vars' /\
                           EvalM ro (ml_monad_translator_write_list (ZIP
                             vars' vals) env) st exp r2
                             ((H:('a->(heap_part->bool)->bool)#('ffi->(mlstring
                             ,ffi)fmap)#(mlstring list#(mlstring->word8
                             list->word8 list->ffi->(ffi
                             cfHeapsBase_ffi_result) option)) list)))))
       | INR ps -> ALL_DISTINCT (MAP (SND o SND o SND) ps) /\
                   good_cons_env ps env /\
                   (!v. a r1 v ==>
                        (?name vals t vars' exp.
                          v = semanticPrimitives_Conv (SOME t) vals /\
                          MEM (name,vars',exp,t) ps /\
                          LENGTH vals = LENGTH vars' /\
                          EvalM ro (ml_monad_translator_write_list (ZIP
                            vars' vals) env) st exp r2 H))) ==>
      EvalM ro env st (ast_Mat exp (Mat_cases y)) r2 H`,
  CHEAT_TAC);;

(*
 * Run
 *)
let EvalSt_def = new_definition
  `EvalSt env st exp P H =
     (!(s:1 semanticPrimitives_state). REFS_PRED H st s ==>
     (?s2 res st2 ck.
       evaluate (semanticPrimitives_state_clock_fupd (K ck) s) env [exp] =
         (s2,Rval [res]) /\
       P res /\ REFS_PRED_FRAME T H (st,s) (st2,s2)))`;;

(* [local] *)
let LENGTH_Mem_IN_store2heap = prove
 (`!refs n. n < LENGTH refs ==> (cfHeapsBase_Mem n (EL n refs)) IN
  (store2heap refs)`,
  CHEAT_TAC);;

(* [local] *)
let REFS_PRED_FRAME_partial_frame_rule = prove
 (`!s refs'.
      (!F'. F' (st2heap p s) ==>
      (F' * GC) (st2heap p (semanticPrimitives_state_refs_fupd (K refs')
        s))) ==>
   (?junk. refs' = APPEND (semanticPrimitives_state_refs s) junk)`,
  CHEAT_TAC);;

let EvalSt_to_Eval = prove
 (`EvalSt env st exp P ((\s. emp),p) ==> ast_Eval env exp P`,
  CHEAT_TAC);;

let handle_mult_def = new_definition
  `handle_mult x1 exp1 ename =
   match x1 with
     [] -> exp1
   | (_:string list) ->
     ast_Handle exp1 [(ast_Pvar (implode "e"),(ast_Con (SOME (Short
       ename)) [ast_Var (Short (implode "e"))]))]`;;

(* [local] *)
let evaluate_handle_mult_Rval = prove
 (`!cons_names exp1 ename res s s2 env.
      evaluate s env [exp1] = (s2,Rval res) ==>
      evaluate s env [handle_mult cons_names exp1 ename] = (s2,Rval res)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_handle_mult_Rabort = prove
 (`!cons_names exp1 ename res s s2 env.
      evaluate s env [exp1] = (s2,Rerr (Rabort res)) ==>
      evaluate s env [handle_mult cons_names exp1 ename] =
        (s2,Rerr (Rabort res))`,
  CHEAT_TAC);;

(* HOL4 ml_monad_translatorScript.sml:3019-3020: ML code, not ported *)

(* EvalM_to_EvalSt *)

let handle_all_def = new_definition
  `handle_all exp ename =
     ast_Handle exp [(ast_Pvar (implode "e"),(ast_Con (SOME (Short
       ename)) [ast_Var (Short (implode "e"))]))]`;;

(* [local] *)
let evaluate_handle_all_Rval = prove
 (`!exp1 ename res s s2 env.
      evaluate s env [exp1] = (s2,Rval res) ==>
      evaluate s env [handle_all exp1 ename] = (s2,Rval res)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_handle_all_Rabort = prove
 (`!exp1 ename res s s2 env.
      evaluate s env [exp1] = (s2,Rerr (Rabort res)) ==>
      evaluate s env [handle_all exp1 ename] = (s2,Rerr (Rabort res))`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Success_CONS = prove
 (`evaluate s env [e] = (s',Rval [v]) ==>
   lookup_cons (Short (implode "M_success")) env = SOME (1,TypeStamp
     (implode "M_success") exc_stamp) ==>
   evaluate s env [ast_Con (SOME (Short (implode "M_success"))) [e]] =
     (s',Rval [semanticPrimitives_Conv (SOME (TypeStamp (implode "M_success")
     exc_stamp)) [v]])`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Success_CONS_err = prove
 (`evaluate s env [e] = (s',Rerr v) ==>
   lookup_cons (Short (implode "M_success")) env = SOME (1,TypeStamp
     (implode "M_success") exc_stamp) ==>
   evaluate s env [ast_Con (SOME (Short (implode "M_success"))) [e]] =
     (s',Rerr v)`,
  CHEAT_TAC);;

(* For the dynamic store initialisation *)
(* It is not possible to use register_type here... *)
let EXC_TYPE_aux_def = define_cases
  `(EXC_TYPE_aux stamp a b (M_failure x_2) v <=>
            (?v2_1.
                            v = semanticPrimitives_Conv (SOME
                                (TypeStamp (implode "M_failure") stamp))
                                [v2_1] /\ b x_2 v2_1)) /\
   (EXC_TYPE_aux stamp a b (M_success x_1) v <=>
            (?v1_1.
                            v = semanticPrimitives_Conv (SOME
                                (TypeStamp (implode "M_success") stamp))
                                [v1_1] /\ a x_1 v1_1))`;;

let EvalM_to_EvalSt = prove
 (`!exc_stamp TYPE' EXN_TYPE x exp H init_state' env.
     EvalM T env init_state' exp (MONAD TYPE' EXN_TYPE x) H ==>
     lookup_cons (Short (implode "M_success")) env = SOME (1,TypeStamp
       (implode "M_success") exc_stamp) ==>
     lookup_cons (Short (implode "M_failure")) env = SOME (1,TypeStamp
       (implode "M_failure") exc_stamp) ==>
     EvalSt env init_state'
       (handle_all (ast_Con (SOME (Short (implode "M_success"))) [exp])
         (implode "M_failure"))
       (EXC_TYPE_aux exc_stamp TYPE' EXN_TYPE (ml_monadBase_run x
         init_state')) H`,
  CHEAT_TAC);;

let EvalSt_Let_Fun = prove
 (`EvalSt (ml_prog_write vname (semanticPrimitives_Closure env xv fexp) env) st
  exp P H ==>
   EvalSt env st (ast_Let (SOME vname) (ast_Fun xv fexp) exp) P H`,
  CHEAT_TAC);;

(* [local] *)
let nsAppend_build_rec_env_eq_lemma = prove
 (`!funs funs0 cl_env v0 v1.
     nsAppend (ITLIST (\(f,x,e) env'. nsBind f
       (semanticPrimitives_Recclosure cl_env funs0 f) env') funs v1) v0 =
     ITLIST (\(f,x,e) env'. nsBind f
       (semanticPrimitives_Recclosure cl_env funs0 f) env') funs (nsAppend
         v1 v0)`,
  CHEAT_TAC);;

(* [local] *)
let nsAppend_build_rec_env_eq = prove
 (`!funs cl_env v0 v1.
      nsAppend (semanticPrimitives_build_rec_env funs cl_env v1) v0 =
      semanticPrimitives_build_rec_env funs cl_env (nsAppend v1 v0)`,
  CHEAT_TAC);;

(* [local] *)
let merge_build_rec_env = prove
 (`!funs env1 env0.
      merge_env (mk_sem_env (semanticPrimitives_build_rec_env funs
        (merge_env env1 env0) (sem_env_v env1)) (sem_env_c env1)) env0 =
        sem_env_v_fupd (K
         (semanticPrimitives_build_rec_env funs (merge_env env1 env0)
           (sem_env_v (merge_env env1 env0))))
      (merge_env env1 env0)`,
  CHEAT_TAC);;

let EvalSt_Letrec_Fun = prove
 (`!funs env exp st P H.
   (ALL_DISTINCT (MAP (\(x,y,z). x) funs)) ==>
   EvalSt (mk_sem_env (semanticPrimitives_build_rec_env funs env (sem_env_v
     env)) (sem_env_c env)) st exp P H ==>
   EvalSt env st (ast_Letrec funs exp) P H`,
  CHEAT_TAC);;

let merge_env_bind_empty = prove
 (`merge_env (mk_sem_env (Bind [] []) (Bind [] [])) env = env`,
  CHEAT_TAC);;

(* Bind_list_to_write *)
let bind_list_to_write = prove
 (`merge_env (mk_sem_env (Bind (CONS (vname,v) binds) []) (Bind [] [])) env =
   ml_prog_write vname v (merge_env (mk_sem_env (Bind binds []) (Bind []
     [])) env)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Var_IMP = prove
 (`evaluate s1 env [ast_Var (Short name)] = (s2,Rval [v]) ==>
   nsLookup (sem_env_v env) (Short name) = SOME v`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Var_same_state = prove
 (`evaluate s1 env [ast_Var (Short name)] = (s2,res) <=>
   evaluate s1 env [ast_Var (Short name)] = (s2,res) /\ s2 = s1`,
  CHEAT_TAC);;

let EvalSt_Opref = prove
 (`!exp get_ref_exp get_ref loc_name TYPE' st_name env H P st.
    ast_Eval env get_ref_exp (TYPE' (get_ref st)) ==>
    (!loc. EvalSt (ml_prog_write loc_name loc env) st exp P
      ((\st. REF_REL TYPE' loc (get_ref st) * H st),p)) ==>
    EvalSt env st
      (ast_Let (SOME loc_name) (ast_App ast_Opref [get_ref_exp]) exp) P
        (H,p)`,
  CHEAT_TAC);;

let EQ_def = new_definition
  `ml_monad_translator_EQ x y <=> x = y`;;

let EvalSt_AllocEmpty = prove
 (`!exp get_ref loc_name TYPE' st_name env H P st.
     binary_ieee_EQ (get_ref st) [] ==>
     (!loc.
       EvalSt (ml_prog_write loc_name loc env) st exp P
         ((\st. RARRAY_REL TYPE' loc (get_ref st) * H st),p)) ==>
     EvalSt env st
       (ast_Let (SOME loc_name) (ast_App ast_Opref [ast_App ast_AallocEmpty
         [ast_Con NONE []]]) exp)
         P (H,p)`,
  CHEAT_TAC);;

let EvalSt_Alloc = prove
 (`!exp nexp n xexp x get_farray loc_name TYPE' env H P st.
     binary_ieee_EQ (get_farray st) (REPLICATE n x) ==>
     ast_Eval env nexp (\v. v = semanticPrimitives_Litv (ast_IntLit (&n)))
       ==>
     ast_Eval env xexp (TYPE' x) ==>
     (!loc.
        EvalSt (ml_prog_write loc_name loc env) st exp P
          ((\st. ARRAY_REL TYPE' loc (get_farray st) * H st),p)) ==>
     EvalSt env st (ast_Let (SOME loc_name) (ast_App ast_Aalloc [nexp;
       xexp]) exp) P (H,p)`,
  CHEAT_TAC);;

(* Eval_lookup_var *)
let eval_lookup_var = prove
 (`!env vname xv x TYPE'. nsLookup (sem_env_v env) (Short vname) = SOME xv ==>
   (ast_Eval env (ast_Var (Short vname)) (TYPE' x) <=> TYPE' x xv)`,
  CHEAT_TAC);;

(* [local] *)
let nsBind_to_write = prove
 (`mk_sem_env (nsBind name v env1) env2 =
    ml_prog_write name v (mk_sem_env env1 env2)`,
  CHEAT_TAC);;

(* [local] *)
let nsLookup_write_simp = prove
 (`nsLookup (sem_env_v (ml_prog_write name1 exp env)) (Short name2) =
    (if name1 = name2 then SOME exp
    else nsLookup (sem_env_v env) (Short name2))`,
  CHEAT_TAC);;

(* [local] *)
let sem_env_same_components = prove
 (`mk_sem_env (sem_env_v env) (sem_env_c env) = (env:semanticPrimitives_v
  sem_env)`,
  CHEAT_TAC);;

(* [local] *)
let lookup_cons_write_simp = prove
 (`lookup_cons name2 (ml_prog_write name1 exp env) =
    lookup_cons name2 env`,
  CHEAT_TAC);;

(* [local] *)
let lookup_cons_build_rec_env_simp = prove
 (`lookup_cons name2 (mk_sem_env (semanticPrimitives_build_rec_env exp env
  (sem_env_v env)) (sem_env_c env)) =
    lookup_cons name2 env`,
  CHEAT_TAC);;

let LOOKUP_ASSUM_SIMP =
  end_itlist CONJ [nsBind_to_write; Eval_Var_SIMP; eval_lookup_var;
  nsLookup_write_simp; sem_env_same_components; lookup_cons_write_simp;
  lookup_cons_build_rec_env_simp];;

let EVAL_T_F =
  end_itlist CONJ [CAKE_EVAL [CONTAINER_def; TRUE_def] `CONTAINER TRUE`;
  CAKE_EVAL [CONTAINER_def; FALSE_def] `CONTAINER FALSE`];;

let EVAL_PRECONDITION_T = CAKE_EVAL [PRECONDITION_def] `PRECONDITION T`;;

let H_STAR_emp = prove
 (`H * emp = H`,
  CHEAT_TAC);;

let H_STAR_TRUE = prove
 (`(H * &T = H) /\ (&T * H = H)`,
  CHEAT_TAC);;

let PreImp_PRECONDITION_T_SIMP = prove
 (`PreImp T a /\ PRECONDITION T <=> a`,
  CHEAT_TAC);;

(* IF_T *)
let ml_monad_translator_IF_T = prove
 (`(if T then x else y) = (x:'a)`,
  CHEAT_TAC);;

(* IF_F *)
let ml_monad_translator_IF_F = prove
 (`(if F then x else y) = (y:'a)`,
  CHEAT_TAC);;

(* IMP_EQ_T *)
let ml_monad_translator_IMP_EQ_T = prove
 (`a ==> (a <=> T)`,
  CHEAT_TAC);;

let BETA_PAIR_THM = prove
 (`(\(x,y). f x y) (x,y) = (\x y. f x y) x y`,
  CHEAT_TAC);;

(* HOL4 ml_monad_translatorScript.sml:3567: ML code, not ported *)

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["ABS";
   "Subscript";
   "TYPE";
   "get_var";
   "set_var"];;

(* and the interface *)
let _ = unhide_overloads ();;
