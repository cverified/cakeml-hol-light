(* ======================================================== *)
(*  ml_translator: ported from HOL4's
    translator/ml_translatorScript.sml
    A definition theory, with 76 definitions and 271 theorems.
    Needed by 83 files of the port.  *)
(* ======================================================== *)

(*
    This script defines Eval and other core definitions used by the
    translator. The theorems about Eval serve as an interface between
    the source semantics and the translator's automation.
*)

needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/integer_word.ml";;
needs "lib/machine_ieee.ml";;
needs "lib/regexp_compiler.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ml_translator"
  ["ast"; "evaluate"; "evaluateProps"; "fpSem"; "ml_prog"; "mlstring";
   "mlvector"; "semanticPrimitives"; "semanticPrimitivesProps"];;

let _ = do_list hide_constant ["ABS"; "Num"; "id"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["vars","vars"];;
(* HOL4 ancestors outside the port: integer *)

(* HOL4 ml_translatorScript.sml:15: ML code, not ported *)

(* HOL4 ml_translatorScript.sml:17: the type abbreviation state, which the
   port expands *)

(* HOL4 ml_translatorScript.sml:19-20: the overload True_ast, which the port
   expands *)

(* HOL4 ml_translatorScript.sml:22-23: the overload False_ast, which the
   port expands *)

(* Definitions *)
let empty_state_def = new_definition
  `ml_translator_empty_state = mk_semanticPrimitives_state 0 empty_store
  (initial_ffi_state ARB one) 0 0 NONE
   // force the ffi state to unit
   // the monadic translator must be used for FFI calls`;;

let eval_def = new_definition
  `ml_translator_Eval env exp P =
     (!refs. ?res refs'.
       eval_rel (semanticPrimitives_state_refs_fupd (K refs)
         ml_translator_empty_state) env exp
                (semanticPrimitives_state_refs_fupd (K (APPEND refs refs'))
                  ml_translator_empty_state) res /\
       P (res:semanticPrimitives_v))`;;

let AppReturns_def,AppReturns_ind = define_guess
  `// think of this as a Hoare triple {P} cl {Q}
   AppReturns P cl Q =
     (!v. P v ==>
       (!refs. ?env exp refs' u.
         semanticPrimitives_do_opapp [cl; v] = SOME (env,exp) /\
         eval_rel (semanticPrimitives_state_refs_fupd (K refs)
           ml_translator_empty_state) env exp
                  (semanticPrimitives_state_refs_fupd (K (APPEND refs
                    refs')) ml_translator_empty_state) u /\
         Q u))`;;

let arrow_def = new_definition
  `Arrow a b =
     (\f v. !x. AppReturns (a x) v (b (f x)))`;;

(* HOL4 ml_translatorScript.sml:61: the overload -->, which the port expands *)

let eq_def = new_definition
  `ml_translator_Eq (abs':'a->semanticPrimitives_v->bool) x =
     (\y v. (x = y) /\ abs' y v)`;;

let and_def = new_definition
  `ml_translator_And a P x v = (P x /\ a (x:'a) (v:semanticPrimitives_v))`;;

let UNIT_TYPE_def = new_definition
  `UNIT_TYPE (u:1) (v:semanticPrimitives_v) = (v = semanticPrimitives_Conv
  NONE [])`;;

let INT_def = new_definition
  `INT i = (\(v:semanticPrimitives_v). (v = semanticPrimitives_Litv
  (ast_IntLit i)))`;;

let NUM_def = new_definition
  `NUM n = INT (&n)`;;

let BOOL_def = new_definition
  `BOOL b = (\(v:semanticPrimitives_v). (v = semanticPrimitives_Boolv b))`;;

let WORD_def = new_definition
  `WORD (w:'a word) =
     (\(v:semanticPrimitives_v). dimindex (:'a) <= 64 /\
           (v = semanticPrimitives_Litv (if dimindex (:'a) <= 8 then
             ast_Word8 (w2w w << (8 - dimindex (:'a)))
                      else ast_Word64 (w2w w << (64 - dimindex (:'a))))))`;;

let FLOAT64_def = new_definition
  `FLOAT64 (f:(52,11)float) =
     (\(v:semanticPrimitives_v). v = semanticPrimitives_Litv (ast_Float64
       (float_to_fp64 f)))`;;

let CHAR_def = new_definition
  `CHAR (c:char) = (\(v:semanticPrimitives_v). (v = semanticPrimitives_Litv
  (ast_Char c)))`;;

let STRING_TYPE_def = new_definition
  `STRING_TYPE s = (\(v:semanticPrimitives_v). (v = semanticPrimitives_Litv
  (ast_StrLit s)))`;;

let explode_eq = prove
 (`explode s = l <=> s = implode l`,
  CHEAT_TAC);;

let eq_explode = prove
 (`l = explode s <=> s = implode l`,
  CHEAT_TAC);;

let HOL_STRING_TYPE_def = new_definition
  `HOL_STRING_TYPE cs = STRING_TYPE (implode cs)`;;

let CONTAINER_def = new_definition
  `CONTAINER x = x`;;

let TAG_def = new_definition
  `TAG n x = x`;;

let PRECONDITION_def = new_definition
  `PRECONDITION b = (b:bool)`;;

let PreImp_def = new_definition
  `PreImp b1 b2 = (PRECONDITION b1 ==> b2)`;;

let PreImpEval_def = new_definition
  `PreImpEval b env code P = PreImp b (ast_Eval env code P)`;;

(* Theorems *)

let AppReturns_thm = prove
 (`AppReturns P cl Q <=>
     (!v. P v ==>
         (?env exp.
           semanticPrimitives_do_opapp [cl; v] = SOME (env,exp) /\
           (!refs.
             ?refs' u.
               eval_rel (semanticPrimitives_state_refs_fupd (K refs)
                 ml_translator_empty_state) env exp
                        (semanticPrimitives_state_refs_fupd (K (APPEND refs
                          refs')) ml_translator_empty_state) u /\
               Q u)))`,
  CHEAT_TAC);;

(* Eval_lemma *)
let eval_lemma = prove
 (`!env exp P.
           ast_Eval env exp P <=>
            (!refs.
                ?ck1 res refs' ck2.
                    evaluate (semanticPrimitives_state_refs_fupd (K refs)
                      (semanticPrimitives_state_clock_fupd (K ck1)
                      ml_translator_empty_state))
                      env [exp] =
                    (semanticPrimitives_state_refs_fupd (K (APPEND refs
                      refs')) (semanticPrimitives_state_clock_fupd (K ck2)
                      ml_translator_empty_state),
                     Rval [res]) /\ P res)`,
  CHEAT_TAC);;

let evaluate_empty_state_IMP = prove
 (`eval_rel (semanticPrimitives_state_refs_fupd (K
  (semanticPrimitives_state_refs s)) ml_translator_empty_state) env exp
  (semanticPrimitives_state_refs_fupd (K (APPEND (semanticPrimitives_state_refs
  s) refs')) ml_translator_empty_state) x ==>
   eval_rel (s:'ffi ml_translator_state) env exp
     (semanticPrimitives_state_refs_fupd (K (APPEND
     (semanticPrimitives_state_refs s) refs')) s) x`,
  CHEAT_TAC);;

let Eval_Arrow = prove
 (`ast_Eval env x1 ((a (Arrow) b) f) ==>
   ast_Eval env x2 (a x) ==>
   ast_Eval env (ast_App ast_Opapp [x1; x2]) (b (f x))`,
  CHEAT_TAC);;

let Eval_Fun = prove
 (`(!v x. a x v ==> ast_Eval (ml_prog_write name v env) body (b ((f:'a->'b)
  x))) ==>
    ast_Eval env (ast_Fun name body) ((a (Arrow) b) f)`,
  CHEAT_TAC);;

let Eval_Fun_Eq = prove
 (`(!v. a x v ==> ast_Eval (ml_prog_write name v env) body (b (f x))) ==>
    ast_Eval env (ast_Fun name body) ((ml_translator_Eq a x (Arrow) b) f)`,
  CHEAT_TAC);;

let And_IMP_Eq = prove
 (`ast_Eval env exp ((ast_And a P (Arrow) b) f) ==>
    (P x ==> ast_Eval env exp ((ml_translator_Eq a x (Arrow) b) f))`,
  CHEAT_TAC);;

let Eq_IMP_And = prove
 (`(!x. P x ==> ast_Eval env (ast_Fun name exp) ((ml_translator_Eq a x (Arrow)
  b) f)) ==>
    ast_Eval env (ast_Fun name exp) ((ast_And a P (Arrow) b) f)`,
  CHEAT_TAC);;

let Eval_Fun_And = prove
 (`(!v x. P x ==> a x v ==> ast_Eval (ml_prog_write name v env) body (b (f x)))
  ==>
    ast_Eval env (ast_Fun name body) ((ast_And a P (Arrow) b) f)`,
  CHEAT_TAC);;

let Eval_Let = prove
 (`ast_Eval env exp (a res) /\
    (!v. a res v ==> ast_Eval (ml_prog_write name v env) body (b (f res)))
      ==>
    ast_Eval env (ast_Let (SOME name) exp body) (b (LET f res))`,
  CHEAT_TAC);;

let Eval_Var_general = prove
 (`P v ==> (!iden. nsLookup (sem_env_v env) iden = SOME v ==> ast_Eval env
  (ast_Var iden) P)`,
  CHEAT_TAC);;

let Eval_Var_Short = prove
 (`P v ==> (!name env.
               (nsLookup (sem_env_v env) (Short name) = SOME v) ==>
               ast_Eval env (ast_Var (Short name)) P)`,
  CHEAT_TAC);;

let Eval_Var_Long = prove
 (`P v ==> (!m name env.
               (nsLookup (sem_env_v env) (Long m (Short name)) = SOME v) ==>
               ast_Eval env (ast_Var (Long m (Short name))) P)`,
  CHEAT_TAC);;

let Eval_Var_SWAP_ENV = prove
 (`!env1.
      ast_Eval env1 (ast_Var (Short name)) P /\
      (ml_prog_lookup_var name env = ml_prog_lookup_var name env1) ==>
      ast_Eval env (ast_Var (Short name)) P`,
  CHEAT_TAC);;

let LOOKUP_VAR_def = new_definition
  `LOOKUP_VAR name env x = (ml_prog_lookup_var name env = SOME x)`;;

let LOOKUP_VAR_THM = prove
 (`LOOKUP_VAR name env x ==> ast_Eval env (ast_Var (Short name)) ((=) x)`,
  CHEAT_TAC);;

let LOOKUP_VAR_SIMP = prove
 (`LOOKUP_VAR name (ml_prog_write x v env) y =
    if x = name then (v = y) else LOOKUP_VAR name env y`,
  CHEAT_TAC);;

let Eval_Val_INT = prove
 (`!n. ast_Eval env (ast_Lit (ast_IntLit n)) (INT n)`,
  CHEAT_TAC);;

let Eval_Val_NUM = prove
 (`!n. ast_Eval env (ast_Lit (ast_IntLit (&n))) (NUM n)`,
  CHEAT_TAC);;

let Eval_Val_UNIT = prove
 (`ast_Eval env (ast_Con NONE []) (UNIT_TYPE one)`,
  CHEAT_TAC);;

let Eval_Val_BOOL_T = prove
 (`ast_Eval env (ast_App (ast_Test (ast_Compare ast_Leq) ast_IntT) [ast_Lit
  (ast_IntLit (&0)); ast_Lit (ast_IntLit (&0))]) (BOOL T)`,
  CHEAT_TAC);;

let Eval_Val_BOOL_F = prove
 (`ast_Eval env (ast_App (ast_Test (ast_Compare ast_Lt) ast_IntT) [ast_Lit
  (ast_IntLit (&0)); ast_Lit (ast_IntLit (&0))]) (BOOL F)`,
  CHEAT_TAC);;

let Eval_Val_CHAR = prove
 (`!c. ast_Eval env (ast_Lit (ast_Char c)) (CHAR c)`,
  CHEAT_TAC);;

let Eval_Val_STRING = prove
 (`!s. ast_Eval env (ast_Lit (ast_StrLit s)) (STRING_TYPE s)`,
  CHEAT_TAC);;

let Eval_Val_WORD = prove
 (`!(w:'a word).
    dimindex (:'a) <= 64 ==>
    ast_Eval env (ast_Lit (if dimindex (:'a) <= 8 then ast_Word8 (w2w w <<
      (8 - dimindex (:'a)))
                   else ast_Word64 (w2w w << (64 - dimindex (:'a)))))
             (WORD w)`,
  CHEAT_TAC);;

let Eval_Val_FLOAT64 = prove
 (`!(f:(52,11)float).
     ast_Eval env (ast_Lit (ast_Float64 (float_to_fp64 f))) (FLOAT64 f)`,
  CHEAT_TAC);;

(* Equality *)

(* the termination relation that HOL4 gives is
     MEASURE semanticPrimitives_v_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ml_translatorScript.sml:403-408: the tactic that proves the
   termination *)
let no_closures_def,no_closures_ind = define_guess
  `no_closures x1 =
     match x1 with
       semanticPrimitives_Conv _ vs -> ALL no_closures vs
     | semanticPrimitives_Vectorv vs -> ALL no_closures vs
     | semanticPrimitives_Closure _ _ _ -> F
     | semanticPrimitives_Recclosure _ _ _ -> F
     | semanticPrimitives_Env _ _ -> F
     | _ -> T`;;

(* the clauses in two quotations: l1 is lit and num; l2 is lit and num; vs1
   is (v list) and (_)list; vs2 is (v list) and (_)list, which one quotation
   cannot typecheck *)
let types_match_def,types_match_ind = define_guess_clauses
  [`(types_match (semanticPrimitives_Litv l1) (semanticPrimitives_Litv l2) =
    lit_same_type l1 l2) /\
    (types_match (semanticPrimitives_Conv cn1 vs1) (semanticPrimitives_Conv cn2
    vs2) =
        (semanticPrimitives_ctor_same_type cn1 cn2 /\ ((cn1 = cn2) ==>
            types_match_list vs1 vs2))) /\
    (types_match _ _ = F) /\
    (types_match_list [] [] = T) /\
    (types_match_list (CONS v1 vs1) (CONS v2 vs2) =
        (types_match v1 v2 /\ types_match_list vs1 vs2)) /\
    // We could change this case to T, or change the semantics to have a type error
    // * when equality reaches unequal-length lists
    (types_match_list _ _ = F)`;
   `types_match (semanticPrimitives_Loc b1 l1) (semanticPrimitives_Loc b2
    l2) = (b1 /\ b2)`];;

let EqualityType_def = new_definition
  `EqualityType (abs':'a->semanticPrimitives_v->bool) <=>
     (!x1 v1. abs' x1 v1 ==> no_closures v1) /\
     (!x1 v1 x2 v2. abs' x1 v1 /\ abs' x2 v2 ==> ((v1 = v2) = (x1 = x2))) /\
     (!x1 v1 x2 v2. abs' x1 v1 /\ abs' x2 v2 ==> types_match v1 v2)`;;

(* [local] *)
let LSL_n2w_eq = prove
 (`a < 2 EXP (dimindex (:'a) - n) /\ b < 2 EXP (dimindex (:'a) - n) /\
     n <= dimindex (:'a) ==>
   ((n2w a << n) = ((n2w b:'a word) << n) <=> a = b)`,
  CHEAT_TAC);;

let EqualityType_NUM_BOOL = prove
 (`EqualityType NUM /\ EqualityType INT /\
   EqualityType BOOL /\ EqualityType WORD /\
   EqualityType CHAR /\ EqualityType STRING_TYPE /\
   EqualityType UNIT_TYPE /\ EqualityType HOL_STRING_TYPE /\
   EqualityType WORD /\ EqualityType FLOAT64`,
  CHEAT_TAC);;

let EqualityType_at_def = new_definition
  `EqualityType_at (abs':'a->semanticPrimitives_v->bool) x <=>
     (!v. abs' x v ==> no_closures v) /\
     (!v x2 v2. abs' x v /\ abs' x2 v2 ==> ((v = v2) = (x = x2))) /\
     (!v x2 v2. abs' x v /\ abs' x2 v2 ==> types_match v v2)`;;

let EqualityType_eq_at = prove
 (`EqualityType TY = (!x. EqualityType_at TY x)`,
  CHEAT_TAC);;

let EqualityType_at_eq_Case_rearranged = prove
 (`EqualityType_at TY x <=>
   (!y vx vy. Case (x,y,vx,vy) ==>
   TY x vx /\ TY y vy ==>
   (x = y ==> vx = vy ==> no_closures vx) /\ (vx = vy <=> x = y)
     /\ types_match vx vy)`,
  CHEAT_TAC);;

let EqualityType_def_rearranged = prove
 (`EqualityType abs = (!x y vx vy.
    abs x vx /\ abs y vy ==>
        (x = y ==> vx = vy ==> no_closures vx) /\ (vx = vy <=> x = y)
          /\ types_match vx vy)`,
  CHEAT_TAC);;

let EqualityType_from_ONTO = prove
 (`(!a. ?r. (a = num2a r) /\ r < (N:num)) ==> (!TY stamps stn.
        (
                list_of_seq (\n v. TY (num2a n) v) N = MAP (\st v. v =
                  semanticPrimitives_Conv (SOME (TypeStamp st stn)) []) stamps)
                  ==>
        ALL_DISTINCT stamps ==> EqualityType TY)`,
  CHEAT_TAC);;

let EqualityType_from_ONTO_Exn = prove
 (`(!a. ?r. (a = num2a r) /\ r < (N:num)) ==> (!TY stamps.
        (
                list_of_seq (\n v. TY (num2a n) v) N = MAP (\st v. v =
                  semanticPrimitives_Conv (SOME (ExnStamp st)) []) stamps) ==>
        ALL_DISTINCT stamps ==> EqualityType TY)`,
  CHEAT_TAC);;

let UNIT_v_def = new_definition
  `UNIT_v (u:1) = (semanticPrimitives_Conv NONE [])`;;

let INT_v_def = new_definition
  `INT_v i = semanticPrimitives_Litv (ast_IntLit i)`;;

let NUM_v_def = new_definition
  `NUM_v n = INT_v (&n)`;;

let BOOL_v_def = new_definition
  `BOOL_v b = semanticPrimitives_Boolv b`;;

let WORD_v_def = new_definition
  `WORD_v (w:'a word) =
     if dimindex (:'a) <= 8 then semanticPrimitives_Litv (ast_Word8 (w2w w
       << (8 - dimindex (:'a))))
     else if dimindex (:'a) <= 64 then semanticPrimitives_Litv (ast_Word64
       (w2w w << (64 - dimindex (:'a))))
     else semanticPrimitives_Conv NONE []`;;

let CHAR_v_def = new_definition
  `CHAR_v (c:char) = semanticPrimitives_Litv (ast_Char c)`;;

let STRING_v_def = new_definition
  `STRING_v s = semanticPrimitives_Litv (ast_StrLit s)`;;

let HOL_STRING_v_def = new_definition
  `HOL_STRING_v cs = STRING_v (implode cs)`;;

(* [local] *)
let types_match_list_REPLICATE = prove
 (`!n m. types_match_list (REPLICATE n x) (REPLICATE m y) =
   (n = m /\ (0 < n ==> types_match x y))`,
  CHEAT_TAC);;

(* nearly all types with equality will be fully representable within v *)
let IsTypeRep_def = new_definition
  `IsTypeRep f R <=> (!x. R x (f x:semanticPrimitives_v))`;;

let IsTypeRep_EqualityType_Unique = prove
 (`EqualityType R ==> IsTypeRep f R ==> IsTypeRep g R ==>
   g = f`,
  CHEAT_TAC);;

let IsTypeRep_EqualityType_INJ = prove
 (`EqualityType R ==> IsTypeRep f R ==> INJ f UNIV UNIV`,
  CHEAT_TAC);;

let DUMMY_TYPE_REP_v = new_definition
  `DUMMY_TYPE_REP_v x = UNIT_v one`;;

let IsTypeRep_NUM_BOOL = prove
 (`IsTypeRep NUM_v NUM /\ IsTypeRep INT_v INT /\
   IsTypeRep BOOL_v BOOL /\
   IsTypeRep CHAR_v CHAR /\
   IsTypeRep UNIT_v UNIT_TYPE /\
   IsTypeRep STRING_v STRING_TYPE /\
   IsTypeRep HOL_STRING_v HOL_STRING_TYPE /\
   (dimindex (:'a) <= 64 ==> IsTypeRep WORD_v (WORD:'a
     word->semanticPrimitives_v->bool))`,
  CHEAT_TAC);;

let types_match_list_length = prove
 (`!vs1 vs2. types_match_list vs1 vs2 ==> LENGTH vs1 = LENGTH vs2`,
  CHEAT_TAC);;

let type_match_implies_do_eq_succeeds = prove
 (`(!v1 v2. types_match v1 v2 ==> (semanticPrimitives_do_eq v1 v2 = Eq_val (v1
  = v2))) /\
   (!vs1 vs2.
      types_match_list vs1 vs2 ==> (semanticPrimitives_do_eq_list vs1 vs2
        = Eq_val (vs1 = vs2)))`,
  CHEAT_TAC);;

(* [local] *)
let do_eq_succeeds = prove
 (`(!a x1 v1 x2 v2. EqualityType a /\ a x1 v1 /\ a x2 v2 ==>
                    (semanticPrimitives_do_eq v1 v2 = Eq_val (x1 = x2)))`,
  CHEAT_TAC);;

(* [local] *)
let empty_state_with_refs_eq = prove
 (`semanticPrimitives_state_refs_fupd (K r)
     ml_translator_empty_state = semanticPrimitives_state_ffi_fupd (K f)
       (semanticPrimitives_state_refs_fupd (K r')
      s2) <=>
      (?refs ffi.
      s2 = semanticPrimitives_state_ffi_fupd (K ffi)
        (semanticPrimitives_state_refs_fupd (K refs) ml_translator_empty_state)
        /\
      r' = r /\ f = semanticPrimitives_state_ffi
        ml_translator_empty_state)`,
  CHEAT_TAC);;

(* [local] *)
let empty_state_with_ffi_elim = prove
 (`semanticPrimitives_state_ffi_fupd (K (semanticPrimitives_state_ffi
  ml_translator_empty_state)) (semanticPrimitives_state_refs_fupd (K r)
     ml_translator_empty_state) = semanticPrimitives_state_refs_fupd (K r)
       ml_translator_empty_state`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:670-677: a proof *)

let Eval_Equality = prove
 (`ast_Eval env x1 (a y1) /\ ast_Eval env x2 (a y2) ==>
    EqualityType a ==>
    ast_Eval env (ast_App ast_Equality [x1; x2]) (BOOL (y1 = y2))`,
  CHEAT_TAC);;

(* booleans *)

let Eval_Or = prove
 (`(a1 ==> ast_Eval env x1 (BOOL b1)) /\
   (a2 ==> ast_Eval env x2 (BOOL b2)) ==>
   (a1 /\ (~(CONTAINER b1) ==> a2) ==>
    ast_Eval env (ast_Log Orelse x1 x2) (BOOL (b1 \/ b2)))`,
  CHEAT_TAC);;

let Eval_And = prove
 (`(a1 ==> ast_Eval env x1 (BOOL b1)) /\
   (a2 ==> ast_Eval env x2 (BOOL b2)) ==>
   (a1 /\ (CONTAINER b1 ==> a2) ==>
    ast_Eval env (ast_Log Andalso x1 x2) (BOOL (b1 /\ b2)))`,
  CHEAT_TAC);;

let Eval_If = prove
 (`(a1 ==> ast_Eval env x1 (BOOL b1)) /\
   (a2 ==> ast_Eval env x2 (a b2)) /\
   (a3 ==> ast_Eval env x3 (a b3)) ==>
   (a1 /\ (CONTAINER b1 ==> a2) /\ (~(CONTAINER b1) ==> a3) ==>
    ast_Eval env (ast_If x1 x2 x3) (a (if b1 then b2 else b3)))`,
  CHEAT_TAC);;

let Eval_Bool_Not = prove
 (`ast_Eval env x1 (BOOL b1) ==>
   ast_Eval env (ast_App (ast_Arith ast_Not ast_BoolT) [x1]) (BOOL (~b1))`,
  CHEAT_TAC);;

let Eval_Implies = prove
 (`ast_Eval env x1 (BOOL b1) ==>
   ast_Eval env x2 (BOOL b2) ==>
   ast_Eval env (ast_If x1 x2 (ast_App (ast_Test (ast_Compare ast_Leq)
     ast_IntT) [ast_Lit (ast_IntLit (&0)); ast_Lit (ast_IntLit (&0))])) (BOOL
     (b1 ==> b2))`,
  CHEAT_TAC);;

let Eval_BOOL_EQ = prove
 (`ast_Eval env x1 (BOOL b1) ==>
   ast_Eval env x2 (BOOL b2) ==>
   ast_Eval env (ast_App (ast_Test ast_Equal ast_BoolT) [x1; x2]) (BOOL
     (b1 = b2))`,
  CHEAT_TAC);;

(* misc *)

let Eval_Var_SIMP = prove
 (`ast_Eval (ml_prog_write x v env) (ast_Var (Short y)) p =
      if x = y then p v else ast_Eval env ((ast_Var (Short y):ast_exp)) p`,
  CHEAT_TAC);;

let Eval_Eq = prove
 (`ast_Eval env exp (a x) ==> ast_Eval env exp ((ml_translator_Eq a x) x)`,
  CHEAT_TAC);;

let FUN_FORALL = new_definition
  `(FUN_FORALL) = (\(abs':'a->'b->semanticPrimitives_v->bool) a v. !y. abs'
  y a v)`;;

let FUN_EXISTS = new_definition
  `(FUN_EXISTS) = (\(abs':'a->'b->semanticPrimitives_v->bool) a v. ?y. abs'
  y a v)`;;

let FUN_FORALL_INTRO = prove
 (`(!x. p x f v) ==> (FUN_FORALL (\x. p x)) f v`,
  CHEAT_TAC);;

let eval_rel_11 = prove
 (`eval_rel s1 env e s2 x2 /\ eval_rel s1 env e s3 x3 ==>
    s2 = s3 /\ x2 = x3`,
  CHEAT_TAC);;

let Eval_FUN_FORALL = prove
 (`(!x. ast_Eval env exp ((p x) f)) ==>
    ast_Eval env exp ((FUN_FORALL (\x. p x)) f)`,
  CHEAT_TAC);;

let Eval_FUN_FORALL_EQ = prove
 (`(!x. ast_Eval env exp ((p x) f)) =
    ast_Eval env exp ((FUN_FORALL (\x. p x)) f)`,
  CHEAT_TAC);;

let FUN_FORALL_PUSH1 = prove
 (`(FUN_FORALL (\x. a (Arrow) (b x))) = (a (Arrow) (FUN_FORALL (\x. b x)))`,
  CHEAT_TAC);;

let FUN_FORALL_PUSH2 = prove
 (`(FUN_FORALL (\x. (a x) (Arrow) b)) = ((FUN_EXISTS (\x. a x)) (Arrow) b)`,
  CHEAT_TAC);;

let FUN_EXISTS_Eq = prove
 (`(FUN_EXISTS (\x. ml_translator_Eq a x)) = a`,
  CHEAT_TAC);;

let FUN_QUANT_SIMP =
  end_itlist CONJ [FUN_EXISTS_Eq; FUN_FORALL_PUSH1; FUN_FORALL_PUSH2];;

let Eval_Recclosure_ALT = prove
 (`!funs fname name body.
      (ALL_DISTINCT (MAP (\(f,x,e). f) funs)) ==>
      (!v. a n v ==>
           ast_Eval (ml_prog_write name v (write_rec funs env2 env2)) body
             (b (f n))) ==>
      LOOKUP_VAR fname env (semanticPrimitives_Recclosure env2 funs fname)
        ==>
      (find_recfun fname funs = SOME (name,body)) ==>
      ast_Eval env (ast_Var (Short fname)) ((ml_translator_Eq a n (Arrow)
        b) f)`,
  CHEAT_TAC);;

let Eval_Recclosure = prove
 (`(!v. a n v ==>
         ast_Eval (ml_prog_write name v (write_rec [(fname,name,body)] env2
           env2))
              body (b (f n))) ==>
    LOOKUP_VAR fname env (semanticPrimitives_Recclosure env2
      [(fname,name,body)] fname) ==>
    ast_Eval env (ast_Var (Short fname)) ((ml_translator_Eq a n (Arrow) b)
      f)`,
  CHEAT_TAC);;

let SafeVar_def = new_definition
  `SafeVar = ast_Var`;;

let Eval_Eq_Recclosure = prove
 (`LOOKUP_VAR name env (semanticPrimitives_Recclosure x1 x2 x3) ==>
    (P f (semanticPrimitives_Recclosure x1 x2 x3) =
     ast_Eval env (ast_Var (Short name)) (P f))`,
  CHEAT_TAC);;

let Eval_Eq_Fun = prove
 (`ast_Eval env (ast_Fun v x) p ==>
    (!env2. ast_Eval env2 (ast_Var name) ((=) (semanticPrimitives_Closure
      env v x)) ==>
           ast_Eval env2 (ast_Var name) p)`,
  CHEAT_TAC);;

let Eval_WEAKEN = prove
 (`ast_Eval env exp P ==> (!v. P v ==> Q v) ==> ast_Eval env exp Q`,
  CHEAT_TAC);;

let Eval_CONST = prove
 (`(!v. P v = (v = x)) ==>
    ast_Eval env (ast_Var name) ((=) x) ==> ast_Eval env (ast_Var name) P`,
  CHEAT_TAC);;

(* arithmetic for integers *)

let Eval_INT_ADD = prove
 (`!n1 n2.
     ast_Eval env x1 (INT n1) ==>
     ast_Eval env x2 (INT n2) ==>
     ast_Eval env (ast_App (ast_Arith ast_Add ast_IntT) [x1; x2]) (INT (n1
       + n2))`,
  CHEAT_TAC);;

let Eval_INT_SUB = prove
 (`!n1 n2.
     ast_Eval env x1 (INT n1) ==>
     ast_Eval env x2 (INT n2) ==>
     ast_Eval env (ast_App (ast_Arith ast_Sub ast_IntT) [x1; x2]) (INT (n1
       - n2))`,
  CHEAT_TAC);;

let Eval_INT_MULT = prove
 (`!n1 n2.
     ast_Eval env x1 (INT n1) ==>
     ast_Eval env x2 (INT n2) ==>
     ast_Eval env (ast_App (ast_Arith ast_Mul ast_IntT) [x1; x2]) (INT (n1
       * n2))`,
  CHEAT_TAC);;

let Eval_INT_DIV = prove
 (`!n1 n2.
     ast_Eval env x1 (INT n1) ==>
     ast_Eval env x2 (INT n2) ==>
     PRECONDITION (~(n2 = 0)) ==>
     ast_Eval env (ast_App (ast_Arith ast_Div ast_IntT) [x1; x2]) (INT (n1
       / n2))`,
  CHEAT_TAC);;

let Eval_INT_MOD = prove
 (`!n1 n2.
     ast_Eval env x1 (INT n1) ==>
     ast_Eval env x2 (INT n2) ==>
     PRECONDITION (~(n2 = 0)) ==>
     ast_Eval env (ast_App (ast_Arith ast_Mod ast_IntT) [x1; x2]) (INT (n1
       % n2))`,
  CHEAT_TAC);;

(* [local] *)
let Eval_INT_CMP = prove
 (`!f n1 n2.
     ast_Eval env x1 (INT n1) ==>
     ast_Eval env x2 (INT n2) ==>
     ast_Eval env (ast_App (ast_Test (ast_Compare f) ast_IntT) [x1; x2])
       (BOOL (semanticPrimitives_int_cmp f n1 n2))`,
  CHEAT_TAC);;

let Eval_INT_LESS = SIMP_RULE [int_cmp_def] (CAKE_SPEC `ast_Lt` Eval_INT_CMP);;
let Eval_INT_LESS_EQ =
  SIMP_RULE [int_cmp_def] (CAKE_SPEC `ast_Leq` Eval_INT_CMP);;
let Eval_INT_GREATER =
  SIMP_RULE [int_cmp_def] (CAKE_SPEC `ast_Gt` Eval_INT_CMP);;
let Eval_INT_GREATER_EQ =
  SIMP_RULE [int_cmp_def] (CAKE_SPEC `ast_Geq` Eval_INT_CMP);;

let Eval_INT_EQ = prove
 (`ast_Eval env x1 (INT i1) ==>
   ast_Eval env x2 (INT i2) ==>
   ast_Eval env (ast_App (ast_Test ast_Equal ast_IntT) [x1; x2]) (BOOL (i1
     = i2))`,
  CHEAT_TAC);;

let Eval_NUM_EQ = prove
 (`ast_Eval env x1 (NUM n1) ==>
   ast_Eval env x2 (NUM n2) ==>
   ast_Eval env (ast_App (ast_Test ast_Equal ast_IntT) [x1; x2]) (BOOL (n1
     = n2))`,
  CHEAT_TAC);;

let Eval_Num = prove
 (`ast_Eval env x1 (INT i) ==> PRECONDITION ((&0) <= i) ==>
   ast_Eval env x1 (NUM (num_of_int i))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:1043: ML code, not ported *)

(* HOL4 ml_translatorScript.sml:1045-1057: the ML values that the
   definitions below antiquote *)

(* HOL4 ml_translatorScript.sml:1059: ML code, not ported *)

let Eval_Num_ABS = prove
 (`ast_Eval env x1 (INT i) ==>
   ast_Eval env (ast_Let (SOME (implode "k")) x1
       (ast_If (ast_App (ast_Test (ast_Compare ast_Lt) ast_IntT) [ast_Var
         (Short (implode "k")); ast_Lit (ast_IntLit (&0))])
          (ast_App (ast_Arith ast_Sub ast_IntT) [ast_Lit (ast_IntLit (&0));
            ast_Var (Short (implode "k"))])
          (ast_Var (Short (implode "k"))))) (NUM (num_of_int (abs i)))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:1075: ML code, not ported *)

let num_of_int_def = new_definition
  `ml_translator_num_of_int i = num_of_int (abs i)`;;

let num_of_int_num = prove
 (`ml_translator_num_of_int (&n) = n /\ ml_translator_num_of_int (--(&n)) = n`,
  CHEAT_TAC);;
add_simp num_of_int_num;;

let eval_num_of_int = REWRITE_RULE [GSYM num_of_int_def] Eval_Num_ABS;;

(* Eval_int_of_num *)
let eval_int_of_num = prove
 (`ast_Eval env x1 (NUM n) ==>
   ast_Eval env x1 (INT (int_of_num n))`,
  CHEAT_TAC);;

(* Eval_int_of_num_o *)
let eval_int_of_num_o = prove
 (`ast_Eval env x1 ((A (Arrow) NUM) f) ==>
   ast_Eval env x1 ((A (Arrow) INT) (int_of_num o f))`,
  CHEAT_TAC);;

(* Eval_o_int_of_num *)
let eval_o_int_of_num = prove
 (`ast_Eval env x1 ((INT (Arrow) A) f) ==>
   ast_Eval env x1 ((NUM (Arrow) A) (f o int_of_num))`,
  CHEAT_TAC);;

(* Eval_int_negate *)
let eval_int_negate = prove
 (`ast_Eval env x1 (INT i) ==>
   ast_Eval env (ast_App (ast_Arith ast_Sub ast_IntT) [ast_Lit (ast_IntLit
     (&0)); x1]) (INT (--i))`,
  CHEAT_TAC);;

(* arithmetic for num *)
(* HOL4 ml_translatorScript.sml:1124-1131: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_SUB *)

(* HOL4 ml_translatorScript.sml:1133-1135: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_ADD *)

(* HOL4 ml_translatorScript.sml:1137-1139: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_MULT *)

(* HOL4 ml_translatorScript.sml:1141-1148: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_DIV *)

(* HOL4 ml_translatorScript.sml:1150-1157: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_MOD *)

(* HOL4 ml_translatorScript.sml:1159-1161: ML code, not ported *)

(* HOL4 ml_translatorScript.sml:1163: ML code, not ported *)

(* HOL4 ml_translatorScript.sml:1165-1174: the ML values that the
   definitions below antiquote *)

(* HOL4 ml_translatorScript.sml:1176: ML code, not ported *)

let sub_check_def = new_definition
  `sub_check (n:num) m = n - m`;;

let Eval_NUM_SUB_check = prove
 (`ast_Eval env x1 (NUM m) ==>
   ast_Eval env x2 (NUM n) ==>
   ast_Eval env (ast_Let (SOME (implode "k")) (ast_App (ast_Arith ast_Sub
     ast_IntT) [x1; x2])
       (ast_If (ast_App (ast_Test (ast_Compare ast_Lt) ast_IntT) [ast_Var
         (Short (implode "k")); ast_Lit (ast_IntLit (&0))])
           (ast_Lit (ast_IntLit (&0))) (ast_Var (Short (implode
             "k")))):ast_exp) (NUM (sub_check m n))`,
  CHEAT_TAC);;

let Eval_NUM_SUB_check' = prove
 (`ast_Eval env x1 (NUM m) ==>
   ast_Eval env x2 (NUM n) ==>
   ast_Eval env (ast_Let (SOME (implode "k")) (ast_App (ast_Arith ast_Sub
     ast_IntT) [x1; x2])
       (ast_If (ast_App (ast_Test (ast_Compare ast_Lt) ast_IntT) [ast_Var
         (Short (implode "k")); ast_Lit (ast_IntLit (&0))])
           (ast_Lit (ast_IntLit (&0))) (ast_Var (Short (implode
             "k")))):ast_exp) (NUM (m - n))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:1209: ML code, not ported *)

(* HOL4 ml_translatorScript.sml:1211-1213: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_LESS *)

(* HOL4 ml_translatorScript.sml:1215-1217: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_LESS_EQ *)

(* HOL4 ml_translatorScript.sml:1219-1222: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_GREATER *)

(* HOL4 ml_translatorScript.sml:1224-1227: a theorem that HOL4 states as the
   value of an ML expression: Eval_NUM_GREATER_EQ *)

let Eval_NUM_EQ_0 = prove
 (`!n. ast_Eval env x (NUM n) ==>
        ast_Eval env (ast_App (ast_Test ast_Equal ast_IntT) [x; ast_Lit
          (ast_IntLit (&0))]) (BOOL (n = 0))`,
  CHEAT_TAC);;

(* word operations *)

(* HOL4 ml_translatorScript.sml:1242-1251: a proof *)

(* Eval_word_and *)
let eval_word_and = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
        (ast_App (ast_Arith ast_And (if dimindex (:'a) <= 8 then ast_WordT
          ast_W8 else ast_WordT ast_W64)) [x1; x2])
        (WORD (word_and w1 w2))`,
  CHEAT_TAC);;

(* Eval_word_or *)
let eval_word_or = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
        (ast_App (ast_Arith ast_Or (if dimindex (:'a) <= 8 then ast_WordT
          ast_W8 else ast_WordT ast_W64)) [x1; x2])
        (WORD (word_or w1 w2))`,
  CHEAT_TAC);;

(* Eval_word_xor *)
let eval_word_xor = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
        (ast_App (ast_Arith ast_Xor (if dimindex (:'a) <= 8 then ast_WordT
          ast_W8 else ast_WordT ast_W64)) [x1; x2])
        (WORD (word_xor w1 w2))`,
  CHEAT_TAC);;

(* [local] *)
let DISTRIB_ANY = prove
 (`(p * m + p * n = p * (m + n)) /\
     (p * m + n * p = p * (m + n)) /\
     (m * p + p * n = p * (m + n)) /\
     (m * p + n * p = p * (m + (n:num))) /\
     (p * m - p * n = p * (m - n)) /\
     (p * m - n * p = p * (m - n)) /\
     (m * p - p * n = p * (m - n)) /\
     (m * p - n * p = p * (m - (n:num)))`,
  CHEAT_TAC);;

(* [local] *)
let MOD_COMMON_FACTOR_ANY = prove
 (`!n p q. 0 < n /\ 0 < q ==>
             ((n * p) MOD (n * q) = n * (p MOD q)) /\
             ((p * n) MOD (n * q) = n * (p MOD q)) /\
             ((n * p) MOD (q * n) = n * (p MOD q)) /\
             ((p * n) MOD (q * n) = n * (p MOD q))`,
  CHEAT_TAC);;

(* Eval_word_add_lemma[local] *)
let eval_word_add_lemma = prove
 (`dimindex (:'a) <= k ==>
     (2 EXP (k - dimindex (:'a)) * (q MOD dimword (:'a))) MOD 2 EXP k =
     (2 EXP (k - dimindex (:'a)) * q) MOD 2 EXP k`,
  CHEAT_TAC);;

(* Eval_word_add *)
let eval_word_add = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
        (ast_App (ast_Arith ast_Add (if dimindex (:'a) <= 8 then ast_WordT
          ast_W8 else ast_WordT ast_W64)) [x1; x2])
        (WORD (word_add w1 w2))`,
  CHEAT_TAC);;

(* Eval_word_sub_lemma[local] *)
let eval_word_sub_lemma = prove
 (`dimindex (:'a) <= k /\ n' < dimword (:'a) ==>
     (n * 2 EXP (k - dimindex (:'a)) +
       (2 EXP k - (n' * 2 EXP (k - dimindex (:'a))) MOD 2 EXP k) MOD 2 EXP
         k) MOD 2 EXP k =
     (((n + dimword (:'a)) - n') * 2 EXP (k - dimindex (:'a))) MOD 2 EXP k`,
  CHEAT_TAC);;

(* Eval_word_sub *)
let eval_word_sub = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
        (ast_App (ast_Arith ast_Sub (if dimindex (:'a) <= 8 then ast_WordT
          ast_W8 else ast_WordT ast_W64)) [x1; x2])
        (WORD (word_sub w1 w2))`,
  CHEAT_TAC);;

(* Eval_word_eq *)
let eval_word_eq = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
     (ast_App (ast_Test ast_Equal (ast_WordT (if dimindex (:'a) <= 8 then
       ast_W8 else ast_W64))) [x1; x2])
     (BOOL (w1 = w2))`,
  CHEAT_TAC);;

(* [local] *)
let less_two_pow_lemma = prove
 (`(n:num) < 2 EXP k /\ k <= d ==> n * 2 EXP (d - k) < 2 EXP d`,
  CHEAT_TAC);;

(* Eval_word_lo *)
let eval_word_lo = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
     (if dimindex (:'a) <= 8 then
        ast_App (ast_Test (ast_Compare ast_Lt) (ast_WordT ast_W8)) [x1; x2]
      else ast_App (ast_Test (ast_Compare ast_Lt) ast_IntT) [ast_App
        (ast_FromTo (ast_WordT ast_W64) ast_IntT) [x1];
                              ast_App (ast_FromTo (ast_WordT ast_W64)
                                ast_IntT) [x2]])
     (BOOL (w1 <+ w2))`,
  CHEAT_TAC);;

(* Eval_word_ls *)
let eval_word_ls = prove
 (`ast_Eval env x1 (WORD (w1:'a word)) /\
   ast_Eval env x2 (WORD (w2:'a word)) ==>
   ast_Eval env
     (if dimindex (:'a) <= 8 then
        ast_App (ast_Test (ast_Compare ast_Leq) (ast_WordT ast_W8)) [x1; x2]
      else ast_App (ast_Test (ast_Compare ast_Leq) ast_IntT) [ast_App
        (ast_FromTo (ast_WordT ast_W64) ast_IntT) [x1];
                              ast_App (ast_FromTo (ast_WordT ast_W64)
                                ast_IntT) [x2]])
     (BOOL (w1 <=+ w2))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:1454-1457: a theorem that HOL4 states as the
   value of an ML expression: Eval_word_hi *)

(* HOL4 ml_translatorScript.sml:1459-1462: a theorem that HOL4 states as the
   value of an ML expression: Eval_word_hs *)

(* [local] *)
let w2n_w2w_8 = prove
 (`dimindex (:'a) < 8 ==>
     w2n ((w2w:'a word->word8) w << (8 - dimindex (:'a)) >>>
             (8 - dimindex (:'a))) = w2n w`,
  CHEAT_TAC);;

(* [local] *)
let w2n_w2w_64 = prove
 (`dimindex (:'a) < 64 ==>
     w2n ((w2w:'a word->word64) w << (64 - dimindex (:'a)) >>>
             (64 - dimindex (:'a))) = w2n w`,
  CHEAT_TAC);;

(* Eval_w2n *)
let eval_w2n = prove
 (`ast_Eval env x1 (WORD (w:'a word)) ==>
   ast_Eval env
     (if dimindex (:'a) = 8 then
        ast_App (ast_FromTo (ast_WordT ast_W8) ast_IntT) [x1]
      else if dimindex (:'a) = 64 then
        ast_App (ast_FromTo (ast_WordT ast_W64) ast_IntT) [x1]
      else if dimindex (:'a) < 8 then
        ast_App (ast_FromTo (ast_WordT ast_W8) ast_IntT) [ast_App (ast_Shift
          ast_W8 Lsr (8 - dimindex (:'a))) [x1]]
      else ast_App (ast_FromTo (ast_WordT ast_W64) ast_IntT) [ast_App
        (ast_Shift ast_W64 Lsr (64 - dimindex (:'a))) [x1]])
     (NUM (w2n w))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:1515-1543: a theorem that HOL4 states as the
   value of an ML expression: lemma *)
(* HOL4 ml_translatorScript.sml:1515-1543: a theorem that HOL4 states as the
   value of an ML expression: Eval_w2i *)

(* Eval_i2w *)
let eval_i2w = prove
 (`dimindex (:'a) <= 64 ==>
   ast_Eval env x1 (INT n) ==>
   ast_Eval env
     (if dimindex (:'a) = 8 then
        ast_App (ast_FromTo ast_IntT (ast_WordT ast_W8)) [x1]
      else if dimindex (:'a) = 64 then
        ast_App (ast_FromTo ast_IntT (ast_WordT ast_W64)) [x1]
      else if dimindex (:'a) < 8 then
        ast_App (ast_Shift ast_W8 Lsl (8 - dimindex (:'a))) [ast_App
          (ast_FromTo ast_IntT (ast_WordT ast_W8)) [x1]]
      else ast_App (ast_Shift ast_W64 Lsl (64 - dimindex (:'a))) [ast_App
        (ast_FromTo ast_IntT (ast_WordT ast_W64)) [x1]])
     (WORD ((i2w n):'a word))`,
  CHEAT_TAC);;

(* Eval_n2w *)
let eval_n2w = prove
 (`dimindex (:'a) <= 64 ==>
   ast_Eval env x1 (NUM n) ==>
   ast_Eval env
     (if dimindex (:'a) = 8 then
        ast_App (ast_FromTo ast_IntT (ast_WordT ast_W8)) [x1]
      else if dimindex (:'a) = 64 then
        ast_App (ast_FromTo ast_IntT (ast_WordT ast_W64)) [x1]
      else if dimindex (:'a) < 8 then
        ast_App (ast_Shift ast_W8 Lsl (8 - dimindex (:'a))) [ast_App
          (ast_FromTo ast_IntT (ast_WordT ast_W8)) [x1]]
      else ast_App (ast_Shift ast_W64 Lsl (64 - dimindex (:'a))) [ast_App
        (ast_FromTo ast_IntT (ast_WordT ast_W64)) [x1]])
     (WORD ((n2w n):'a word))`,
  CHEAT_TAC);;

(* Eval_w2w *)
let eval_w2w = prove
 (`dimindex (:'a) <= 64 /\ dimindex (:'b) <= 64 ==>
   ast_Eval env x1 (WORD (w:'b word)) ==>
   ast_Eval env
     (if (dimindex (:'a) <= 8 <=> dimindex (:'b) <= 8) then
        let w = (if dimindex (:'a) <= 8 then ast_W8 else ast_W64) in
          if dimindex (:'b) <= dimindex (:'a) then
            ast_App (ast_Shift w Lsr (dimindex (:'a) - dimindex (:'b))) [x1]
          else ast_App (ast_Shift w Lsl (dimindex (:'b) - dimindex (:'a)))
            [x1]
      else if dimindex (:'b) <= 8 then
        ast_App (ast_Shift ast_W64 Lsl (64 - dimindex (:'a)))
          [ast_App (ast_Shift ast_W64 Lsr (8 - dimindex (:'b)))
             [ast_App (ast_FromTo ast_IntT (ast_WordT ast_W64)) [ast_App
               (ast_FromTo (ast_WordT ast_W8) ast_IntT) [x1]]]]
      else ast_App (ast_Shift ast_W8 Lsl (8 - dimindex (:'a)))
          [ast_App (ast_FromTo ast_IntT (ast_WordT ast_W8)) [ast_App
            (ast_FromTo (ast_WordT ast_W64) ast_IntT)
             [ast_App (ast_Shift ast_W64 Lsr (64 - dimindex (:'b))) [x1]]]])
     (WORD ((w2w w):'a word))`,
  CHEAT_TAC);;

(* Eval_word_lsl *)
let eval_word_lsl = prove
 (`!n.
      ast_Eval env x1 (WORD (w1:'a word)) ==>
      ast_Eval env (ast_App (ast_Shift (if dimindex (:'a) <= 8 then ast_W8
        else ast_W64) Lsl n) [x1])
        (WORD (word_lsl w1 n))`,
  CHEAT_TAC);;

(* Eval_word_lsr *)
let eval_word_lsr = prove
 (`!n.
      ast_Eval env x1 (WORD (w1:'a word)) ==>
      ast_Eval env (let w = (if dimindex (:'a) <= 8 then ast_W8 else
        ast_W64) in
                let k = (if dimindex (:'a) <= 8 then 8 else 64) - dimindex
                  (:'a) in
                  if dimindex (:'a) = 8 \/ dimindex (:'a) = 64 then
                    ast_App (ast_Shift w Lsr n) [x1]
                  else ast_App (ast_Shift w Lsl k) [ast_App (ast_Shift w Lsr
                    (n + k)) [x1]])
        (WORD (word_lsr w1 n))`,
  CHEAT_TAC);;

(* Eval_word_asr *)
let eval_word_asr = prove
 (`!n.
      ast_Eval env x1 (WORD (w1:'a word)) ==>
      ast_Eval env (let w = (if dimindex (:'a) <= 8 then ast_W8 else
        ast_W64) in
                let k = (if dimindex (:'a) <= 8 then 8 else 64) - dimindex
                  (:'a) in
                  if dimindex (:'a) = 8 \/ dimindex (:'a) = 64 then
                    ast_App (ast_Shift w Asr n) [x1]
                  else ast_App (ast_Shift w Lsl k) [ast_App (ast_Shift w Asr
                    (n + k)) [x1]])
        (WORD (word_asr w1 n))`,
  CHEAT_TAC);;

(* Eval_word_ror *)
let eval_word_ror = prove
 (`!n.
      ast_Eval env x1 (WORD (w1:'a word)) ==>
      (~(dimindex (:'a) = 8) ==> dimindex (:'a) = 64) ==>
      ast_Eval env (ast_App (ast_Shift (if dimindex (:'a) <= 8 then ast_W8
        else ast_W64) Ror n) [x1])
        (WORD (word_ror w1 n))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:1758-1760: ML code, not ported *)

let lift_fp_top_def = new_definition
  `lift_fp_top f f1 f2 f3 =
   fp64_to_float (fp_top_comp f (float_to_fp64 f1) (float_to_fp64 f2)
                              (float_to_fp64 f3))`;;

let float64_fma_def = new_definition
  `float64_fma (f1:(52,11)float) f2 f3 =
   SND (float_mul_add roundTiesToEven f1 f2 f3)`;;

let Eval_FLOAT_FMA = prove
 (`!f1 f2 f3.
     ast_Eval env x2 (FLOAT64 f2) ==>
     ast_Eval env x3 (FLOAT64 f3) ==>
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env
          (ast_App (ast_Arith ast_FMA ast_Float64T) [x1; x2; x3])
          (FLOAT64 (float64_fma f2 f3 f1))`,
  CHEAT_TAC);;

let lift_fp_bop_def = new_definition
  `lift_fp_bop f f1 f2 =
   fp64_to_float (fp_bop_comp f (float_to_fp64 f1) (float_to_fp64 f2))`;;

let float64_add_def = new_definition
  `float64_add = lift_fp_bop fpSem_FP_Add`;;

let float64_add_thm = prove
 (`float64_add f1 f2 = SND (float_add roundTiesToEven f1 f2)`,
  CHEAT_TAC);;

let float64_sub_def = new_definition
  `float64_sub = lift_fp_bop fpSem_FP_Sub`;;

let float64_sub_thm = prove
 (`float64_sub f1 f2 = SND (float_sub roundTiesToEven f1 f2)`,
  CHEAT_TAC);;

let float64_mul_def = new_definition
  `float64_mul = lift_fp_bop fpSem_FP_Mul`;;

let float64_mul_thm = prove
 (`float64_mul f1 f2 = SND (float_mul roundTiesToEven f1 f2)`,
  CHEAT_TAC);;

let float64_div_def = new_definition
  `float64_div = lift_fp_bop fpSem_FP_Div`;;

let float64_div_thm = prove
 (`float64_div f1 f2 = SND (float_div roundTiesToEven f1 f2)`,
  CHEAT_TAC);;

let Eval_FLOAT_ADD = prove
 (`!f1 f2.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env x2 (FLOAT64 f2) ==>
     ast_Eval env (ast_App (ast_Arith ast_Add ast_Float64T) [x1; x2])
       (FLOAT64 (float64_add f1 f2))`,
  CHEAT_TAC);;

let Eval_FLOAT_SUB = prove
 (`!f1 f2.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env x2 (FLOAT64 f2) ==>
     ast_Eval env (ast_App (ast_Arith ast_Sub ast_Float64T) [x1; x2])
       (FLOAT64 (float64_sub f1 f2))`,
  CHEAT_TAC);;

let Eval_FLOAT_MULT = prove
 (`!f1 f2.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env x2 (FLOAT64 f2) ==>
     ast_Eval env (ast_App (ast_Arith ast_Mul ast_Float64T) [x1; x2])
       (FLOAT64 (float64_mul f1 f2))`,
  CHEAT_TAC);;

let Eval_FLOAT_DIV = prove
 (`!f1 f2.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env x2 (FLOAT64 f2) ==>
     ast_Eval env (ast_App (ast_Arith ast_Div ast_Float64T) [x1; x2])
       (FLOAT64 (float64_div f1 f2))`,
  CHEAT_TAC);;

let lift_fp_cmp_def = new_definition
  `lift_fp_cmp f f1 f2 = fp_cmp f (float_to_fp64 f1) (float_to_fp64 f2)`;;

let float64_less_def = new_definition
  `float64_less = lift_fp_cmp ast_Lt`;;

let float64_less_thm = prove
 (`float64_less f1 f2 = float_less_than f1 f2`,
  CHEAT_TAC);;

let float64_less_equal_def = new_definition
  `float64_less_equal = lift_fp_cmp ast_Leq`;;

let float64_less_equal_thm = prove
 (`float64_less_equal f1 f2 = float_less_equal f1 f2`,
  CHEAT_TAC);;

let float64_greater_def = new_definition
  `float64_greater = lift_fp_cmp ast_Gt`;;

let float64_greater_thm = prove
 (`float64_greater f1 f2 = float_greater_than f1 f2`,
  CHEAT_TAC);;

let float64_greater_equal_def = new_definition
  `float64_greater_equal = lift_fp_cmp ast_Geq`;;

let float64_greater_equal_thm = prove
 (`float64_greater_equal f1 f2 = float_greater_equal f1 f2`,
  CHEAT_TAC);;

let float64_equal_def = new_definition
  `float64_equal f1 f2 = fp64_equal (float_to_fp64 f1) (float_to_fp64 f2)`;;

let float64_equal_thm = prove
 (`float64_equal f1 f2 = float_equal f1 f2`,
  CHEAT_TAC);;

(* [local] *)
let Eval_FP_cmp = prove
 (`!cmp f1 f2.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env x2 (FLOAT64 f2) ==>
     ast_Eval env (ast_App (ast_Test (ast_Compare cmp) ast_Float64T) [x1;
       x2]) (BOOL (lift_fp_cmp cmp f1 f2))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:1973-1990: a theorem that HOL4 states as the
   value of an ML expression: Eval_ *)

let Eval_FLOAT_EQ = prove
 (`ast_Eval env x1 (FLOAT64 f1) ==>
   ast_Eval env x2 (FLOAT64 f2) ==>
   ast_Eval env (ast_App (ast_Test ast_Equal ast_Float64T) [x1; x2]) (BOOL
     (float64_equal f1 f2))`,
  CHEAT_TAC);;

let lift_fp_uop_def = new_definition
  `lift_fp_uop f f1 = fp64_to_float (fp_uop_comp f (float_to_fp64 f1))`;;

let float64_abs_def = new_definition
  `float64_abs = lift_fp_uop fpSem_FP_Abs`;;

let float64_abs_thm = prove
 (`float64_abs f1 = float_abs f1`,
  CHEAT_TAC);;

let float64_neg_def = new_definition
  `float64_neg = lift_fp_uop fpSem_FP_Neg`;;

let float64_neg_thm = prove
 (`float64_neg f1 = float_negate f1`,
  CHEAT_TAC);;

let float64_sqrt_def = new_definition
  `float64_sqrt = lift_fp_uop fpSem_FP_Sqrt`;;

let float64_sqrt_thm = prove
 (`float64_sqrt f1 = SND (float_sqrt roundTiesToEven f1)`,
  CHEAT_TAC);;

let Eval_FLOAT_ABS = prove
 (`!f1.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env (ast_App (ast_Arith ast_Abs ast_Float64T) [x1]) (FLOAT64
       (float64_abs f1))`,
  CHEAT_TAC);;

let Eval_FLOAT_NEG = prove
 (`!f1.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env (ast_App (ast_Arith ast_Neg ast_Float64T) [x1]) (FLOAT64
       (float64_neg f1))`,
  CHEAT_TAC);;

let Eval_FLOAT_SQRT = prove
 (`!f1.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env (ast_App (ast_Arith ast_Sqrt ast_Float64T) [x1])
       (FLOAT64 (float64_sqrt f1))`,
  CHEAT_TAC);;

let Eval_FP_fromWord = prove
 (`!w1.
     ast_Eval env x1 (WORD (w1:word64)) ==>
     ast_Eval env (ast_App (ast_FromTo (ast_WordT ast_W64) ast_Float64T)
       [x1]) (FLOAT64 (fp64_to_float w1))`,
  CHEAT_TAC);;

let Eval_FP_toWord = prove
 (`!f1.
     ast_Eval env x1 (FLOAT64 f1) ==>
     ast_Eval env (ast_App (ast_FromTo ast_Float64T (ast_WordT ast_W64))
       [x1]) (WORD (float_to_fp64 f1))`,
  CHEAT_TAC);;


(* list definition *)

let LIST_TYPE_def = define_cases
  `(LIST_TYPE a (CONS x_2 x_1) v <=>
         (?v2_1 v2_2.
           v = semanticPrimitives_Conv (SOME (TypeStamp (implode "::") 1))
               [v2_1; v2_2] /\
           a x_2 v2_1 /\ LIST_TYPE a x_1 v2_2)) /\
   (LIST_TYPE a [] v <=>
         v = semanticPrimitives_Conv (SOME (TypeStamp (implode "[]")
             1)) [])`;;

(* HOL4 ml_translatorScript.sml:2115-2120: a theorem that HOL4 states as the
   value of an ML expression: LIST_TYPE_SIMP' *)

(* HOL4 ml_translatorScript.sml:2122-2123: a theorem that HOL4 states as the
   value of an ML expression: LIST_TYPE_SIMP *)

let LIST_TYPE_IF_ELIM = prove
 (`!v. LIST_TYPE (\x v. if MEM x l then P x v else Q x v) l v = LIST_TYPE P l
  v`,
  CHEAT_TAC);;

let LIST_TYPE_mono = prove
 (`!P Q l v.
   LIST_TYPE P l v /\ (!x v. MEM x l /\ P x v ==> Q x v) ==>
   LIST_TYPE Q l v`,
  CHEAT_TAC);;

let LIST_v_def,LIST_v_ind = define_guess
  `(LIST_v a_v [] = semanticPrimitives_Conv (SOME (TypeStamp (implode "[]")
    1)) []) /\
   (LIST_v a_v (CONS x xs) = semanticPrimitives_Conv (SOME (TypeStamp
    (implode "::") 1)) [a_v x; LIST_v a_v xs])`;;

let IsTypeRep_LIST = prove
 (`IsTypeRep a_v a ==> IsTypeRep (LIST_v a_v) (LIST_TYPE a)`,
  CHEAT_TAC);;

(* pair definition *)

let PAIR_TYPE_def = new_definition
  `PAIR_TYPE a b ((x_2:'a),(x_1:'b)) v <=>
   (?v1_1 v1_2. v = semanticPrimitives_Conv NONE [v1_1; v1_2] /\ a x_2
     v1_1 /\ b x_1 v1_2)`;;

(* HOL4 ml_translatorScript.sml:2163-2168: a theorem that HOL4 states as the
   value of an ML expression: PAIR_TYPE_SIMP *)

let PAIR_v_def = new_definition
  `PAIR_v a_v b_v (x,y) = semanticPrimitives_Conv NONE [a_v x; b_v y]`;;

let IsTypeRep_PAIR = prove
 (`IsTypeRep a_v a /\ IsTypeRep b_v b ==> IsTypeRep (PAIR_v a_v b_v)
  (PAIR_TYPE a b)`,
  CHEAT_TAC);;

(* characters *)

let Eval_Ord = prove
 (`ast_Eval env x (CHAR c) ==>
   ast_Eval env (ast_App (ast_FromTo ast_CharT ast_IntT) [x]) (NUM (ORD
     c))`,
  CHEAT_TAC);;

let Eval_Chr = prove
 (`ast_Eval env x (NUM n) ==>
   n < 256 ==>
   ast_Eval env (ast_App (ast_FromTo ast_IntT ast_CharT) [x]) (CHAR (CHR
     n))`,
  CHEAT_TAC);;

(* Eval_char_to_word8 *)
let eval_char_to_word8 = prove
 (`ast_Eval env x (CHAR c) ==>
   ast_Eval env (ast_App (ast_FromTo ast_CharT (ast_WordT ast_W8)) [x])
     (WORD (char_to_word8 c))`,
  CHEAT_TAC);;

(* Eval_word8_to_char *)
let eval_word8_to_char = prove
 (`ast_Eval env x (WORD c) ==>
   ast_Eval env (ast_App (ast_FromTo (ast_WordT ast_W8) ast_CharT) [x])
     (CHAR (word8_to_char c))`,
  CHEAT_TAC);;

(* Boolv_11 *)
let boolv_11 = prove
 (`(semanticPrimitives_Boolv b1 = semanticPrimitives_Boolv b2) <=> (b1 = b2)`,
  CHEAT_TAC);;

(* Eval_char_lt *)
let eval_char_lt = prove
 (`ast_Eval env x1 (CHAR c1) ==>
   ast_Eval env x2 (CHAR c2) ==>
   ast_Eval env (ast_App (ast_Test (ast_Compare ast_Lt) ast_CharT) [x1;
     x2]) (BOOL (c1 < c2))`,
  CHEAT_TAC);;

(* Eval_char_le *)
let eval_char_le = prove
 (`ast_Eval env x1 (CHAR c1) ==>
   ast_Eval env x2 (CHAR c2) ==>
   ast_Eval env (ast_App (ast_Test (ast_Compare ast_Leq) ast_CharT) [x1;
     x2]) (BOOL (c1 <= c2))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:2254-2258: a theorem that HOL4 states as the
   value of an ML expression: Eval_char_gt *)

(* HOL4 ml_translatorScript.sml:2260-2264: a theorem that HOL4 states as the
   value of an ML expression: Eval_char_ge *)

(* Eval_char_eq *)
let eval_char_eq = prove
 (`ast_Eval env x1 (CHAR c1) ==>
   ast_Eval env x2 (CHAR c2) ==>
   ast_Eval env (ast_App (ast_Test ast_Equal ast_CharT) [x1; x2]) (BOOL
     (c1 = c2))`,
  CHEAT_TAC);;

(* strings *)

let LIST_TYPE_CHAR_v_to_char_list = prove
 (`!l v. LIST_TYPE CHAR l v ==> semanticPrimitives_v_to_char_list v = SOME l`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:2288-2292: a proof *)

(* HOL4 ml_translatorScript.sml:2294-2297: a proof *)

(* Eval_implode *)
let eval_implode = prove
 (`!env x1 l.
      ast_Eval env x1 (LIST_TYPE CHAR l) ==>
      ast_Eval env (ast_App ast_Implode [x1]) (STRING_TYPE (implode l))`,
  CHEAT_TAC);;

(* Eval_explode *)
let eval_explode = prove
 (`!env x1 l.
      ast_Eval env x1 (STRING_TYPE s) ==>
      ast_Eval env (ast_App ast_Explode [x1]) (LIST_TYPE CHAR (explode s))`,
  CHEAT_TAC);;

(* Eval_strlen *)
let eval_strlen = prove
 (`!env x1 s.
      ast_Eval env x1 (STRING_TYPE s) ==>
      ast_Eval env (ast_App ast_Strlen [x1]) (NUM (strlen s))`,
  CHEAT_TAC);;

(* Eval_strsub *)
let eval_strsub = prove
 (`!env x1 x2 s n.
      ast_Eval env x1 (STRING_TYPE s) ==>
      ast_Eval env x2 (NUM n) ==>
      n < strlen s ==>
      ast_Eval env (ast_App ast_Strsub [x1; x2]) (CHAR (strsub s n))`,
  CHEAT_TAC);;

(* Eval_concat *)
let eval_concat = prove
 (`!env x ls.
     ast_Eval env x (LIST_TYPE STRING_TYPE ls) ==>
     ast_Eval env (ast_App ast_Strcat [x]) (STRING_TYPE (mlvector_concat
       ls))`,
  CHEAT_TAC);;

(* Eval_substring *)
let eval_substring = prove
 (`!env x1 x2 x3 len off st.
    ast_Eval env x1 (STRING_TYPE st) ==>
    ast_Eval env x2 (NUM off) ==>
    ast_Eval env x3 (NUM len) ==>
      off + len <= strlen st ==>
    ast_Eval env (ast_App ast_CopyStrStr [x1; x2; x3]) (STRING_TYPE
      (substring st off len))`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:2391-2396: a proof *)

(* Eval_str_eq *)
let eval_str_eq = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test ast_Equal ast_StrT) [x1; x2]) (BOOL (s1
     = s2))`,
  CHEAT_TAC);;

(* Eval_mlstring_lt *)
let eval_mlstring_lt = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_Compare ast_Lt) ast_StrT) [x1;
     x2]) (BOOL (mlstring_lt s1 s2))`,
  CHEAT_TAC);;

(* Eval_mlstring_le *)
let eval_mlstring_le = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_Compare ast_Leq) ast_StrT) [x1;
     x2]) (BOOL (mlstring_le s1 s2))`,
  CHEAT_TAC);;

(* Eval_mlstring_gt *)
let eval_mlstring_gt = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_Compare ast_Gt) ast_StrT) [x1;
     x2]) (BOOL (mlstring_gt s1 s2))`,
  CHEAT_TAC);;

(* Eval_mlstring_ge *)
let eval_mlstring_ge = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_Compare ast_Geq) ast_StrT) [x1;
     x2]) (BOOL (mlstring_ge s1 s2))`,
  CHEAT_TAC);;

(* Eval_fast_lt *)
let eval_fast_lt = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_AltCompare ast_Lt) ast_StrT) [x1;
     x2]) (BOOL (fast_lt s1 s2))`,
  CHEAT_TAC);;

(* Eval_fast_le *)
let eval_fast_le = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_AltCompare ast_Leq) ast_StrT) [x1;
     x2]) (BOOL (fast_le s1 s2))`,
  CHEAT_TAC);;

(* Eval_fast_gt *)
let eval_fast_gt = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_AltCompare ast_Gt) ast_StrT) [x1;
     x2]) (BOOL (fast_gt s1 s2))`,
  CHEAT_TAC);;

(* Eval_fast_ge *)
let eval_fast_ge = prove
 (`ast_Eval env x1 (STRING_TYPE s1) ==>
   ast_Eval env x2 (STRING_TYPE s2) ==>
   ast_Eval env (ast_App (ast_Test (ast_AltCompare ast_Geq) ast_StrT) [x1;
     x2]) (BOOL (fast_ge s1 s2))`,
  CHEAT_TAC);;

(* char list as string *)

(* Eval_implode_nop *)
let eval_implode_nop = prove
 (`ast_Eval env x (HOL_STRING_TYPE cs) ==>
   ast_Eval env x (STRING_TYPE (implode cs))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_explode = prove
 (`ast_Eval env x (STRING_TYPE s) ==>
   ast_Eval env x (HOL_STRING_TYPE (explode s))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_INTRO = prove
 (`ast_Eval env x (LIST_TYPE CHAR cs) ==>
   ast_Eval env (ast_App ast_Implode [x]) (HOL_STRING_TYPE cs)`,
  CHEAT_TAC);;

let Eval_HOL_STRING_DEST = prove
 (`ast_Eval env x (HOL_STRING_TYPE cs) ==>
   ast_Eval env (ast_App ast_Explode [x]) (LIST_TYPE CHAR cs)`,
  CHEAT_TAC);;

let Eval_HOL_STRING_LENGTH = prove
 (`!env x1 s.
      ast_Eval env x1 (HOL_STRING_TYPE s) ==>
      ast_Eval env (ast_App ast_Strlen [x1]) (NUM (LENGTH s))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_EL = prove
 (`!env x1 x2 s n.
      ast_Eval env x2 (NUM n) ==>
      ast_Eval env x1 (HOL_STRING_TYPE s) ==>
      n < LENGTH s ==>
      ast_Eval env (ast_App ast_Strsub [x1; x2]) (CHAR (EL n s))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_HD = prove
 (`!env x1 s n.
      ast_Eval env x1 (HOL_STRING_TYPE s) ==> ~(s = "") ==>
      ast_Eval env (ast_App ast_Strsub [x1; ast_Lit (ast_IntLit (&0))])
        (CHAR (HD s))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_APPEND = prove
 (`!env x1 x2 s1 s2 n.
      ast_Eval env x1 (HOL_STRING_TYPE s1) ==>
      ast_Eval env x2 (HOL_STRING_TYPE s2) ==>
      lookup_cons (Short (implode "::")) env = SOME (2,TypeStamp (implode
        "::") 1) /\
      lookup_cons (Short (implode "[]")) env = SOME (0,TypeStamp (implode
        "[]") 1) ==>
      ast_Eval env
        (ast_App ast_Strcat [ast_Con (SOME (Short (implode "::")))
                    [x1; ast_Con (SOME (Short (implode "::")))
                         [x2; ast_Con (SOME (Short (implode "[]"))) []]]])
        (HOL_STRING_TYPE (APPEND s1 s2))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_CONS = prove
 (`!env x1 x2 c s n.
      ast_Eval env x1 (CHAR c) ==>
      ast_Eval env x2 (HOL_STRING_TYPE s) ==>
      lookup_cons (Short (implode "::")) env = SOME (2,TypeStamp (implode
        "::") 1) /\
      lookup_cons (Short (implode "[]")) env = SOME (0,TypeStamp (implode
        "[]") 1) ==>
      ast_Eval env
        (ast_App ast_Strcat [ast_Con (SOME (Short (implode "::")))
                    [ast_App ast_Implode [ast_Con (SOME (Short (implode
                      "::")))
                              [x1; ast_Con (SOME (Short (implode "[]")))
                                []]];
                     ast_Con (SOME (Short (implode "::")))
                       [x2; ast_Con (SOME (Short (implode "[]"))) []]]])
        (HOL_STRING_TYPE (CONS c s))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_FLAT = prove
 (`!env x ls.
     ast_Eval env x (LIST_TYPE HOL_STRING_TYPE ls) ==>
     ast_Eval env (ast_App ast_Strcat [x]) (HOL_STRING_TYPE (FLAT ls))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_IMPLODE = prove
 (`!env x1 s.
      ast_Eval env x1 (LIST_TYPE CHAR s) ==>
      ast_Eval env (ast_App ast_Implode [x1]) (HOL_STRING_TYPE (IMPLODE
        s))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_EXPLODE = prove
 (`!env x1 s.
      ast_Eval env x1 (HOL_STRING_TYPE s) ==>
      ast_Eval env (ast_App ast_Explode [x1]) (LIST_TYPE CHAR (EXPLODE s))`,
  CHEAT_TAC);;

let Eval_HOL_STRING_LITERAL = prove
 (`!s. ast_Eval env (ast_Lit (ast_StrLit (implode s))) (HOL_STRING_TYPE s)`,
  CHEAT_TAC);;

(* vectors *)

let VECTOR_TYPE_def = new_definition
  `VECTOR_TYPE a (Vector l) v <=>
     (?l'. v = semanticPrimitives_Vectorv l' /\ LENGTH l = LENGTH l'
       /\ ALL2 a l l')`;;

let VECTOR_v_def = new_definition
  `VECTOR_v v_a (Vector l) = semanticPrimitives_Vectorv (MAP v_a l)`;;

let IsTypeRep_VECTOR = prove
 (`IsTypeRep v_a a ==> IsTypeRep (VECTOR_v v_a) (VECTOR_TYPE a)`,
  CHEAT_TAC);;

(* Eval_sub *)
let eval_sub = prove
 (`!env x1 x2 a n v.
      ast_Eval env x1 (VECTOR_TYPE a v) ==>
      ast_Eval env x2 (NUM n) ==>
      n < length v ==>
      ast_Eval env (ast_App ast_Vsub [x1; x2]) (a (regexp_compiler_sub v
        n))`,
  CHEAT_TAC);;

(* Eval_sub_unsafe *)
let eval_sub_unsafe = prove
 (`!env x1 x2 a n v.
      ast_Eval env x1 (VECTOR_TYPE a v) ==>
      ast_Eval env x2 (NUM n) ==>
      n < length v ==>
      ast_Eval env (ast_App ast_Vsub_unsafe [x1; x2]) (a (sub_unsafe v n))`,
  CHEAT_TAC);;

(* Eval_vector *)
let eval_vector = prove
 (`!env x1 a l.
      ast_Eval env x1 (LIST_TYPE a l) ==>
      ast_Eval env (ast_App ast_VfromList [x1]) (VECTOR_TYPE a (Vector l))`,
  CHEAT_TAC);;

let list_to_v_LIST_TYPE = prove
 (`!xs v ys.
     LIST_TYPE a xs v /\
     semanticPrimitives_v_to_list v = SOME ys ==>
       LIST_TYPE a xs (semanticPrimitives_list_to_v ys)`,
  CHEAT_TAC);;

(* ListAppend theorems *)

let list_to_v_LIST_TYPE_APPEND = prove
 (`!xs ys x y.
     LIST_TYPE a x (semanticPrimitives_list_to_v xs) /\
     LIST_TYPE a y (semanticPrimitives_list_to_v ys) ==>
       LIST_TYPE a (APPEND x y) (semanticPrimitives_list_to_v (APPEND xs
         ys))`,
  CHEAT_TAC);;

let v_to_list_LIST_TYPE = prove
 (`!x v.
     LIST_TYPE a x v ==> (?xs. semanticPrimitives_v_to_list v = SOME xs)`,
  CHEAT_TAC);;

let Eval_ListAppend = prove
 (`!env x1 x2 a l1 l2.
     ast_Eval env x2 (LIST_TYPE a l1) ==>
     ast_Eval env x1 (LIST_TYPE a l2) ==>
     ast_Eval env (ast_App ast_ListAppend [x2; x1]) (LIST_TYPE a (APPEND
       l1 l2))`,
  CHEAT_TAC);;

(* Eval_length *)
let eval_length = prove
 (`!env x1 x2 a n v.
      ast_Eval env x1 (VECTOR_TYPE a v) ==>
      ast_Eval env (ast_App ast_Vlength [x1]) (NUM (length v))`,
  CHEAT_TAC);;

(* This is useful to force the type inferencer to give the type unit
   to an unused argument. *)
let force_unit_type_def = new_definition
  `force_unit_type (u:1) x = x`;;
add_simp force_unit_type_def;;

(* Eval_force_unit_type *)
let eval_force_unit_type = prove
 (`ast_Eval env x1 (UNIT_TYPE u) ==>
   ast_Eval env x2 ((a:'a->semanticPrimitives_v->bool) y) ==>
   ast_Eval env (ast_Mat x1 [(ast_Pcon NONE [],x2)]) (a (force_unit_type u
     y))`,
  CHEAT_TAC);;

let force_gc_to_run_def = new_definition
  `force_gc_to_run (i1:int) (i2:int) = one`;;

(* Eval_force_gc_to_run *)
let eval_force_gc_to_run = prove
 (`ast_Eval env x1 (INT i1) ==>
   ast_Eval env x2 (INT i2) ==>
   ast_Eval env (ast_App ast_ConfigGC [x1; x2]) (UNIT_TYPE
     (force_gc_to_run i1 i2))`,
  CHEAT_TAC);;

let force_out_of_memory_error_def = new_definition
  `force_out_of_memory_error (x:'a) = x`;;

(* HOL4 ml_translatorScript.sml:2796: the ML values that the definitions
   below antiquote *)

(* Eval_force_out_of_memory_error *)
let eval_force_out_of_memory_error = prove
 (`ast_Eval env x (a i) ==>
   ast_Eval env (ast_Let (SOME (implode "a")) x
            (ast_Let (SOME (implode "n")) (ast_Lit (ast_IntLit (&((&2:int)
              EXP 64))))
            (ast_Let NONE (ast_App ast_Aalloc [ast_Var (Short (implode
              "n")); ast_Var (Short (implode "n"))])
              (ast_Var (Short (implode "a")))))) (a
                (force_out_of_memory_error i))`,
  CHEAT_TAC);;

(* Eval_empty_ffi *)
let eval_empty_ffi = prove
 (`ast_Eval env x (STRING_TYPE s) ==>
   ast_Eval env (ast_App (ast_FFI (implode "")) [x; ast_App ast_Aw8alloc
     [ast_Lit (ast_IntLit (&0)); ast_Lit (ast_Word8 (n2w 0))]])
     (UNIT_TYPE (empty_ffi s))`,
  CHEAT_TAC);;

let pure_seq_def = new_definition
  `pure_seq x y = y`;;

(* Eval_pure_seq *)
let eval_pure_seq = prove
 (`ast_Eval env x (a a1) ==>
   ast_Eval env y (b b1) ==>
   ast_Eval env (ast_Let NONE x y) (b (pure_seq a1 b1))`,
  CHEAT_TAC);;


(* a few misc. lemmas that help the automation *)

let IMP_PreImp = prove
 (`!b1 b2 b3. (b1 /\ b2 ==> b3) ==> b1 ==> PreImp b2 b3`,
  CHEAT_TAC);;

(* HOL4 ml_translatorScript.sml:2861-2871: code that the source has in a
   comment *)

(* [local] *)
let UNCURRY1 = prove
 (`!f. UNCURRY f = (\x. match x with (x,y) -> f x y)`,
  CHEAT_TAC);;

(* [local] *)
let UNCURRY2 = prove
 (`!x y f. pair_CASE x f y = pair_CASE x (\z1 z2. f z1 z2 y)`,
  CHEAT_TAC);;

let UNCURRY3 = prove
 (`pair_CASE (x,y) f = f x y`,
  CHEAT_TAC);;

let UNCURRY_SIMP = end_itlist CONJ [UNCURRY1; UNCURRY2; UNCURRY3];;

let num_case_thm = prove
 (`num_CASE = (\n b f. if n = 0 then b else f (n - 1))`,
  CHEAT_TAC);;

let PUSH_FORALL_INTO_IMP = prove
 (`!P Q. (!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)`,
  CHEAT_TAC);;

let FALSE_def = new_definition
  `FALSE = F`;;
let TRUE_def = new_definition
  `TRUE = T`;;

let Eval_Val_BOOL_FALSE = prove
 (`ast_Eval env (ast_App (ast_Test (ast_Compare ast_Lt) ast_IntT) [ast_Lit
  (ast_IntLit (&0)); ast_Lit (ast_IntLit (&0))]) (BOOL FALSE)`,
  CHEAT_TAC);;

let Eval_Val_BOOL_TRUE = prove
 (`ast_Eval env (ast_App (ast_Test (ast_Compare ast_Leq) ast_IntT) [ast_Lit
  (ast_IntLit (&0)); ast_Lit (ast_IntLit (&0))]) (BOOL TRUE)`,
  CHEAT_TAC);;

let MEMBER_def,MEMBER_ind = define_guess
  `(MEMBER (x:'a) [] <=> F) /\
   (MEMBER (x:'a) (CONS y ys) <=> (x = y) \/ MEMBER x ys)`;;

(* [local] *)
let MEM_EQ_MEMBER = prove
 (`!ys x. MEM x ys = MEMBER x ys`,
  CHEAT_TAC);;

let MEMBER_INTRO = prove
 (`(MEM = MEMBER) /\ (MEM x = MEMBER x) /\ (MEM x ys = MEMBER x ys)`,
  CHEAT_TAC);;

(* lookup cons *)

let lookup_cons_write = prove
 (`!funs n x env name env1.
      (lookup_cons name (ml_prog_write n x env) = lookup_cons name env) /\
      (lookup_cons name (write_rec funs env1 env) = lookup_cons name env)`,
  CHEAT_TAC);;

let DISJOINT_set_SIMP = prove
 (`(DISJOINT (set_of_list []) s <=> T) /\
   (DISJOINT (set_of_list (CONS x xs)) s <=> ~(x IN s) /\ DISJOINT
     (set_of_list xs) s)`,
  CHEAT_TAC);;

(* removing shadowed elements from an alist *)

(* the termination relation that HOL4 gives is
     MEASURE LENGTH
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ml_translatorScript.sml:2965-2969: the tactic that proves the
   termination *)
let ASHADOW_def,ASHADOW_ind = define_guess
  `(ASHADOW [] = []) /\
   (ASHADOW (CONS x xs) =
         if EX (\y. FST x = FST y) xs then CONS x (ASHADOW (FILTER (\y.
             ~(FST x = FST y)) xs))
         else CONS x (ASHADOW xs))`;;

(* [local] *)
let ASHADOW_PREFIX = prove
 (`!xs ys.
       ALL_DISTINCT (MAP FST xs) /\
       ALL (\y. ~(MEM y (MAP FST ys))) (MAP FST xs) ==>
       (ASHADOW (APPEND xs ys) = APPEND xs (ASHADOW ys))`,
  CHEAT_TAC);;

(* [local] *)
let MEM_MAP_ASHADOW = prove
 (`!xs y. MEM y (MAP FST (ASHADOW xs)) = MEM y (MAP FST xs)`,
  CHEAT_TAC);;

(* [local] *)
let EVERY_ALOOKUP_LEMMA = prove
 (`!xs. ALL_DISTINCT (MAP FST xs) ==>
          ALL (\(x,y,z). ALOOKUP xs x = SOME (y,z)) xs`,
  CHEAT_TAC);;

(* [local] *)
let ALOOKUP_FILTER = prove
 (`!t a q. ~(q = a) ==> (ALOOKUP (FILTER (\y. ~(q = FST y)) t) a = ALOOKUP t
  a)`,
  CHEAT_TAC);;

(* [local] *)
let ALOOKUP_ASHADOW = prove
 (`!xs a. ALOOKUP (ASHADOW xs) a = ALOOKUP xs a`,
  CHEAT_TAC);;

(* [local] *)
let ALL_DISTINCT_MAP_FST_ASHADOW = prove
 (`!xs. ALL_DISTINCT (MAP FST (ASHADOW xs))`,
  CHEAT_TAC);;

(* size lemmas *)

(* HOL4 ml_translatorScript.sml:3049-3054: a theorem whose statement the
   port cannot state yet: v1_size *)

(* introducing a module (Tmod) *)

let type_names_def,type_names_ind = define_guess
  `ml_translator_type_names x1 names =
     match x1 with
       [] -> names
     | CONS (Dtype _ tds) xs ->
        ml_translator_type_names xs (APPEND (MAP (FST o SND) tds) names)
     | CONS x xs -> ml_translator_type_names xs names`;;

(* [local] *)
let type_names_eq = prove
 (`!ds names.
      ml_translator_type_names ds names = APPEND (FLAT (REVERSE (MAP (\d.
                match d with
                  Dlet _ v6 v7 -> []
                | Dletrec _ v8 -> []
                | Dmod _ ds -> []
                | Dtype _ tds -> MAP (\(tvs,tn,ctors). tn) tds
                | Dtabbrev _ tvs tn t -> []
                | Dlocal _ _ -> []
                | Denv _ -> []
                | Dexn _ v10 v11 -> []) ds))) names`,
  CHEAT_TAC);;

(* [local] *)
let lookup_APPEND = prove
 (`!xs ys n. ~(MEM n (MAP FST ys)) ==>
               (ALOOKUP (APPEND xs ys) n = ALOOKUP xs n)`,
  CHEAT_TAC);;

let FEVERY_DRESTRICT_FUPDATE = prove
 (`FEVERY P (DRESTRICT (f |+ (x,y)) (COMPL s)) <=>
    (~(x IN s) ==> P (x,y)) /\
    FEVERY P (DRESTRICT f (COMPL (x INSERT s)))`,
  CHEAT_TAC);;

let PULL_EXISTS_EXTRA = prove
 (`(Q ==> (?x. P x)) <=> (?x. Q ==> P x)`,
  CHEAT_TAC);;

let Eval_Fun_rw = prove
 (`ast_Eval env (ast_Fun n exp) P <=> P (semanticPrimitives_Closure env n
  exp)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Var_nsLookup = prove
 (`eval_rel s env (ast_Var id) s' r <=>
     (?v. nsLookup (sem_env_v env) id = SOME r /\ s' = s)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_Var = prove
 (`eval_rel s env (ast_Var (Short n)) s' r <=>
     (?v. ml_prog_lookup_var n env = SOME r /\ s' = s)`,
  CHEAT_TAC);;

let Eval_Var_nsLookup = prove
 (`ast_Eval env (ast_Var id) P <=> (match nsLookup (sem_env_v env) id with
  NONE -> F | SOME v -> P v)`,
  CHEAT_TAC);;

let Eval_Var = prove
 (`ast_Eval env (ast_Var (Short n)) P <=>
   (?v. ml_prog_lookup_var n env = SOME v /\ P v)`,
  CHEAT_TAC);;

let Eval_Fun_Var_intro = prove
 (`ast_Eval cl_env (ast_Fun n exp) P ==>
   (!name. LOOKUP_VAR name env (semanticPrimitives_Closure cl_env n exp) ==>
   ast_Eval env (ast_Var (Short name)) P)`,
  CHEAT_TAC);;

let Eval_Var_LOOKUP_VAR_elim = prove
 (`(!env. LOOKUP_VAR name env v ==> ast_Eval env (ast_Var (Short name)) P)
  ==> P v`,
  CHEAT_TAC);;

let PRECONDITION_T = CAKE_EVAL [PRECONDITION_def] `PRECONDITION T`;;

(* the termination relation that HOL4 gives is
     MEASURE ast_exp_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 ml_translatorScript.sml:3202-3207: the tactic that proves the
   termination *)
let no_change_refs_def,no_change_refs_ind = define_guess
  `no_change_refs x1' =
   match x1' with
     ast_Lit _ -> T
   | ast_Var _ -> T
   | ast_Fun _ _ -> T
   | ast_Let _ e1 e2 -> (no_change_refs e1 /\ no_change_refs e2)
   | ast_If e1 e2 e3 ->
     (no_change_refs e1 /\ no_change_refs e2 /\ no_change_refs e3)
   | ast_Raise e -> no_change_refs e
   | ast_Letrec _ e -> no_change_refs e
   | ast_Con _ es -> ALL no_change_refs es
   | ast_Tannot e _ -> no_change_refs e
   | ast_Lannot e _ -> no_change_refs e
   | ast_Mat e pats ->
     (no_change_refs e /\ ALL no_change_refs (MAP SND pats))
   | ast_App oper es -> ((match oper with
           ast_Opassign -> F
         | ast_Opapp -> F
         | ast_Eval -> F
         | ast_Opref -> F
         | ast_Aw8alloc -> F
         | ast_Aw8update -> F
         | ast_Aw8update_unsafe -> F
         | ast_CopyStrAw8 -> F
         | ast_CopyAw8Aw8 -> F
         | ast_XorAw8Str_unsafe -> F
         | ast_Aalloc -> F
         | ast_AallocEmpty -> F
         | ast_AallocFixed -> F
         | ast_Aupdate -> F
         | ast_Aupdate_unsafe -> F
         | ast_FFI _ -> F
         | ast_ThunkOp _ -> F
         | _ -> T) /\ ALL no_change_refs es)
   | _ -> F`;;

let evaluate_no_change_refs = prove
 (`(!(s:'ffi ml_translator_state) env es s1 vs.
      evaluate s env es = (s1,Rval vs) /\ ALL no_change_refs es ==>
        semanticPrimitives_state_refs
      s1 = semanticPrimitives_state_refs s) /\
   (!(s:'ffi ml_translator_state) env v pes errv s1 vs.
      evaluate_evaluate_match s env v pes errv = (s1,Rval vs) /\ ALL
        no_change_refs (MAP SND pes) ==> semanticPrimitives_state_refs
      s1 = semanticPrimitives_state_refs s)`,
  CHEAT_TAC);;

let eval_rel_no_change_refs = prove
 (`!exp s1 s2 env res.
     eval_rel s1 env exp s2 res /\ no_change_refs exp ==>
       semanticPrimitives_state_refs s1 = semanticPrimitives_state_refs s2`,
  CHEAT_TAC);;

(* Eval_constant *)
let eval_constant = prove
 (`!refs.
     ast_Eval env exp P ==>
     (?v refs'. eval_rel (semanticPrimitives_state_refs_fupd (K refs)
       ml_translator_empty_state) env exp
                        (semanticPrimitives_state_refs_fupd (K (APPEND refs
                          refs')) ml_translator_empty_state) v /\
               (no_change_refs exp ==> refs' = []))`,
  CHEAT_TAC);;

let Eval_evaluate_IMP = prove
 (`ast_Eval env exp P /\
   eval_rel s env exp s' v ==>
   P v`,
  CHEAT_TAC);;

let pair_CASE_UNCURRY = prove
 (`!x y. pair_CASE x y = UNCURRY y x`,
  CHEAT_TAC);;

let IF_T = prove
 (`(if T then x else y) = (x:'a)`,
  CHEAT_TAC);;
let IF_F = prove
 (`(if F then x else y) = (y:'a)`,
  CHEAT_TAC);;

let sat_hyp_lemma = prove
 (`(b1 ==> (x1 = x2)) /\ (x1 ==> y) ==> b1 /\ x2 ==> y`,
  CHEAT_TAC);;

let IMP_EQ_F = prove
 (`~b ==> (b = F)`,
  CHEAT_TAC);;
let IMP_EQ_T = prove
 (`b ==> (b = T)`,
  CHEAT_TAC);;

let IF_TAKEN = prove
 (`!b x y. b ==> ((if b then x else y) = (x:'unlikely))`,
  CHEAT_TAC);;

let EQ_COND_INTRO = prove
 (`(b ==> c) ==> (c = (if b then T else c))`,
  CHEAT_TAC);;

let LIST_TYPE_And = prove
 (`LIST_TYPE (ast_And a P) = ast_And (LIST_TYPE a) (ALL (P:'a->bool))`,
  CHEAT_TAC);;

let EVERY_MEM_CONTAINER = prove
 (`!P l. ALL P l <=> (!e. CONTAINER (MEM e l) ==> P (e:'a))`,
  CHEAT_TAC);;

let PRECONDITION_EQ_CONTAINER = prove
 (`(PRECONDITION p = CONTAINER p) /\
    (CONTAINER (~p) = ~(CONTAINER p)) /\ CONTAINER T`,
  CHEAT_TAC);;

let CONTAINER_NOT_ZERO = prove
 (`!P. (~(CONTAINER (b = 0)) ==> P b) =
        (!n. (CONTAINER (b = SUC n)) ==> P (SUC n:num))`,
  CHEAT_TAC);;

let IMP_PreImp_LEMMA = prove
 (`!b1 b2 b3. (b1 ==> b3 ==> b2) ==> b3 ==> PreImp b1 b2`,
  CHEAT_TAC);;

let PRE_IMP = prove
 (`T /\ PRECONDITION b ==> PRECONDITION b`,
  CHEAT_TAC);;

let PreImp_IMP_T = prove
 (`PreImp b1 b2 /\ T ==> PreImp b1 b2`,
  CHEAT_TAC);;

let CONJ_IMP = prove
 (`!b1 b2 b12 b3 b4 b34.
         (b1 /\ b2 ==> b12) /\ (b3 /\ b4 ==> b34) ==>
         ((b1 /\ b3) /\ (b2 /\ b4) ==> b12 /\ b34)`,
  CHEAT_TAC);;

let IMP_SPLIT = prove
 (`!b12 b3 b4 b34.
         (b12 = b12) /\ (b3 /\ b4 ==> b34) ==>
         ((b12 ==> b3) /\ (b12 ==> b4) ==> (b12 ==> b34))`,
  CHEAT_TAC);;

let FORALL_SPLIT = prove
 (`(!x. P1 x /\ P2 x ==> P (x:'a)) ==>
    ((!) P1) /\ ((!) P2) ==> (!) P`,
  CHEAT_TAC);;

let DEFAULT_IMP = prove
 (`!b1. b1 /\ b1 ==> b1`,
  CHEAT_TAC);;

let combine_lemma = prove
 (`!b1 b2 b3 b4. (b1 /\ b2 ==> b3) /\ (b3 ==> b4) ==> b2 ==> b1 ==> b4`,
  CHEAT_TAC);;

let IMP_PreImp_THM = prove
 (`(b ==> PreImp x y) ==> ((x ==> b) ==> PreImp x y)`,
  CHEAT_TAC);;

let PreImp_IMP = prove
 (`(PRECONDITION x ==> PreImp x y) ==> PreImp x y`,
  CHEAT_TAC);;

let PreImp_LEMMA = prove
 (`(b1 ==> PreImp b1 b2) ==> PreImp b1 b2`,
  CHEAT_TAC);;

let SUC_SUB1_LEMMA = REWRITE_RULE [GSYM ADD1] (CAKE_SPECL [`n`; `1`] ADD_SUB);;

let LENGTH_EQ_SUC_IMP = prove
 (`LENGTH xs = SUC n ==> ~(xs = [])`,
  CHEAT_TAC);;

(* pattern match translation *)

let mat_cases_def = define_cases
  `(Mat_cases (INL (vars',(x:ast_exp))) = [(ast_Pcon NONE (MAP ast_Pvar
    vars'),x)]) /\
   (Mat_cases (INR ps) =
      MAP (\(name,vars',(x:ast_exp),(t:stamp)).
        (ast_Pcon (SOME name) (MAP ast_Pvar vars'),x)) ps)`;;

let good_cons_env_def = new_definition
  `good_cons_env ps env <=>
     ALL (\(name,vars',x,t).
       ALL_DISTINCT (ast_pats_bindings (MAP ast_Pvar vars')) /\
       lookup_cons name env = SOME (LENGTH vars',t)) ps /\
     (let (name,vars',x,t1) = HD ps in
       ALL (\(name,vars',x,t2). same_type t1 t2) ps)`;;

let evaluate_match_MAP = prove
 (`!l1 xs.
         MEM (x1,x2,x3,t1) full_ps /\ ~(full_ps = []) /\
         good_cons_env full_ps env /\ set_of_list l1 SUBSET set_of_list
           full_ps /\
         ~(MEM t1 (MAP (SND o SND o SND) l1)) ==>
         evaluate_evaluate_match (s:'ffi ml_translator_state) env
           (semanticPrimitives_Conv (SOME t1) vals)
           (APPEND (MAP (\(name,vars',x,t). (ast_Pcon (SOME name)
              (MAP ast_Pvar vars'),x)) l1) xs) err =
         evaluate_evaluate_match s env (semanticPrimitives_Conv (SOME t1)
           vals) xs err`,
  CHEAT_TAC);;

let pmatch_list_MAP_Pvar = prove
 (`!vars' vals aux.
      LENGTH vars' = LENGTH vals ==>
      semanticPrimitives_pmatch_list env refs (MAP ast_Pvar vars') vals aux
        =
      Match (APPEND (REVERSE (ZIP vars' vals)) aux)`,
  CHEAT_TAC);;

let write_list_def,write_list_ind = define_guess
  `(ml_translator_write_list [] (env:semanticPrimitives_v sem_env) = env) /\
   (ml_translator_write_list (CONS (n,v) xs) (env:semanticPrimitives_v
    sem_env) = ml_translator_write_list xs (ml_prog_write n v env))`;;

let write_list_thm = prove
 (`!xs env.
      ml_translator_write_list xs (env:semanticPrimitives_v sem_env) =
       (sem_env_v_fupd (K (nsAppend (alist_to_ns (REVERSE xs)) (sem_env_v
         env))) env)`,
  CHEAT_TAC);;

let IMP_Eval_Mat_cases = prove
 (`!a (r1:'a) env exp r2 y.
      ast_Eval env exp (a r1) /\
      (match y with INL (vars',exp) ->
                   (ALL_DISTINCT (ast_pats_bindings (MAP ast_Pvar vars')) /\
                    (!v. a r1 v ==>
                         (?name vals t.
                           v = semanticPrimitives_Conv NONE vals /\
                           LENGTH vals = LENGTH vars' /\
                           ast_Eval (ml_translator_write_list (ZIP vars'
                             vals) env) exp r2)))
       | INR ps -> ALL_DISTINCT (MAP (SND o SND o SND) ps) /\
                   good_cons_env ps env /\
                   (!v. a r1 v ==>
                        (?name vals t vars' exp.
                          v = semanticPrimitives_Conv (SOME t) vals /\
                          MEM (name,vars',exp,t) ps /\
                          LENGTH vals = LENGTH vars' /\
                          ast_Eval (ml_translator_write_list (ZIP vars'
                            vals) env) exp r2))) ==>
      ast_Eval env (ast_Mat exp (Mat_cases y)) r2`,
  CHEAT_TAC);;

(* [local] *)
let Eval_Con_lemma = prove
 (`!ps refs.
     (!p_1 p_2. MEM (p_1,p_2) ps ==> ast_Eval env p_2 p_1) ==>
     (?ck1 ck2 refs' vals.
       evaluate (semanticPrimitives_state_refs_fupd (K refs)
         (semanticPrimitives_state_clock_fupd (K ck1)
         ml_translator_empty_state)) env
                (MAP SND ps) =
       (semanticPrimitives_state_refs_fupd (K (APPEND refs refs'))
         (semanticPrimitives_state_clock_fupd (K ck2)
         ml_translator_empty_state),Rval vals) /\
       ALL2 (\(p,x) v. p v) ps vals)`,
  CHEAT_TAC);;

let Eval_Con = prove
 (`!ps stamp.
      lookup_cons name env = SOME (LENGTH ps,stamp) /\
      ALL (\(p,x). ast_Eval env x p) ps /\
      (!vals.
         ALL2 (\(p,x) v. p v) ps vals ==>
         q (semanticPrimitives_Conv (SOME stamp) vals)) ==>
      ast_Eval env (ast_Con (SOME name) (MAP SND ps)) q`,
  CHEAT_TAC);;

let Eval_Con_NONE = prove
 (`!ps.
      ALL (\(p,x). ast_Eval env x p) ps /\
      (!vals.
         ALL2 (\(p,x) v. p v) ps vals ==>
         q (semanticPrimitives_Conv NONE vals)) ==>
      ast_Eval env (ast_Con NONE (MAP SND ps)) q`,
  CHEAT_TAC);;

(* translation of a new ref *)

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let new_ref_thm = prove
 (cake_as_vars (fun () ->
    `ast_Eval env e (a (x:'a)) ==>
     no_change_refs e ==>
     (!refs.
       ?init_v loc_v.
         eval_rel (semanticPrimitives_state_refs_fupd (K refs)
           ml_translator_empty_state) env (ast_App ast_Opref [e])
                  (semanticPrimitives_state_refs_fupd (K (APPEND refs
                    [semanticPrimitives_Refv init_v]))
                    ml_translator_empty_state) loc_v /\
         a x init_v /\ loc_v = semanticPrimitives_Loc T (LENGTH refs))`),
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["ABS";
   "Num";
   "id"];;

(* and the interface *)
let _ = unhide_overloads ();;
