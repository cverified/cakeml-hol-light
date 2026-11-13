(* ======================================================== *)
(*  flat_to_closProof: ported from HOL4's
    compiler/backend/proofs/flat_to_closProofScript.sml
    A proof theory about flat_to_clos.ml, with 7 definitions and 102
    theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for flat_to_clos
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_interp.ml";;
needs "compiler/backend/flatLang.ml";;
needs "compiler/backend/flat_to_clos.ml";;
needs "compiler/backend/proofs/clos_interpProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "compiler/backend/semantics/flatProps.ml";;
needs "compiler/backend/semantics/flatSem.ml";;
needs "lib/comparison.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "flat_to_closProof"
  ["ast"; "backendProps"; "backend_common"; "closLang"; "closProps";
   "closSem"; "clos_interpProof"; "ffi"; "flatLang"; "flatProps";
   "flatSem"; "flat_to_clos"; "misc"; "semanticPrimitives";
   "semanticPrimitivesProps"];;

let LIST_REL_EL = prove
 (`// TODO: move
   !xs ys r.
     LIST_REL r xs ys <=>
     (LENGTH xs = LENGTH ys) /\
     (!n. n < LENGTH ys ==> r (EL n xs) (EL n ys))`,
  CHEAT_TAC);;

let flat_to_closProof_v_rel = cake_inductive
  `(!n b. flat_to_closProof_v_rel (Loc b n) (closSem_RefPtr b n)) /\
   (!i. flat_to_closProof_v_rel (Litv (ast_IntLit i)) (closSem_Number
     i)) /\
   (!c. flat_to_closProof_v_rel (Litv (ast_Char c)) (closSem_Number
     (&(ORD c)))) /\
   (!s. flat_to_closProof_v_rel (Litv (ast_StrLit s))
     (closSem_ByteVector (MAP (n2w o ORD) (explode s)))) /\
   (!b. flat_to_closProof_v_rel (Litv (ast_Word8 b)) (closSem_Number
     (&(w2n b)))) /\
   (!w. flat_to_closProof_v_rel (Litv (ast_Word64 w)) (Word64 w)) /\
   (!f. flat_to_closProof_v_rel (Litv (ast_Float64 f)) (Word64 f)) /\
   (!vs ws. LIST_REL flat_to_closProof_v_rel vs ws ==>
     flat_to_closProof_v_rel (Conv NONE vs) (closSem_Block 0 ws)) /\
   (!vs ws t r. LIST_REL flat_to_closProof_v_rel vs ws ==>
     flat_to_closProof_v_rel (Conv (SOME (t,r)) vs) (closSem_Block t
     ws)) /\
   (!vs ws. LIST_REL flat_to_closProof_v_rel vs ws ==>
     flat_to_closProof_v_rel (Vectorv vs) (closSem_Block 0 ws)) /\
   (!env m db.
     (!n x. ALOOKUP (flatSem_environment_v env) n = SOME x ==>
            indexedLists_findi (SOME n) m < LENGTH db /\
            flat_to_closProof_v_rel x (EL (indexedLists_findi (SOME
              n) m) db)) ==>
      flat_to_closProof_env_rel env (m:(mlstring option) list)
        (db:closSem_v list)) /\
   (!env m db n e.
      flat_to_closProof_env_rel env m db /\ no_Mat e ==>
      flat_to_closProof_v_rel (Closure env n e)
            (Closure NONE [] db 1 (HD (flat_to_clos_compile (SOME n
              :: m) [e])))) /\
   (!funs n env m db.
     n < LENGTH funs /\ flat_to_closProof_env_rel env m db /\
       ALL_DISTINCT (MAP FST funs) /\
     EVERY no_Mat (MAP (SND o SND) funs) ==>
      flat_to_closProof_v_rel (Recclosure env funs (FST (EL n funs)))
       (Recclosure NONE [] db (MAP
             (\(f,v,x). (1,HD (flat_to_clos_compile
                        (SOME v :: (MAP (\n. SOME (FST n)) funs ++
                          m))
                        [x]))) funs) n))`;;
hol4_overload "env_rel" "flat_to_closProof_env_rel";;
hol4_overload "v_rel" "flat_to_closProof_v_rel";;

(* HOL4 flat_to_closProofScript.sml:55-68: a theorem that HOL4 states
   as the value of an ML expression: v_rel_def *)

(* HOL4 flat_to_closProofScript.sml:70: a theorem that HOL4 states as
   the value of an ML expression: env_rel_def *)

let store_rel_def = new_definition
  `store_rel refs t_refs =
     (!i. if LENGTH refs <= i then FLOOKUP t_refs i = NONE else
           match EL i refs with semanticPrimitives_Refv v -> (?x.
             FLOOKUP t_refs i = SOME (closSem_ValueArray [x]) /\
             flat_to_closProof_v_rel v x) | Thunk m v -> (?x. FLOOKUP
             t_refs i = SOME (Thunk m x) /\ flat_to_closProof_v_rel v x)
             | semanticPrimitives_Varray vs -> (?xs. FLOOKUP t_refs i =
             SOME (closSem_ValueArray xs) /\
                              LIST_REL flat_to_closProof_v_rel vs
                                xs) | semanticPrimitives_W8array bs
                                -> FLOOKUP t_refs i = SOME
                                (closSem_ByteArray bs))`;;

let inc_compile_decs'_def = new_definition
  `inc_compile_decs' decs = (flat_to_clos_compile_decs decs ++
     flat_to_clos_compile_decs [Con backend_common_None NONE
       []],[])`;;

let install_config_rel'_def = new_definition
  `install_config_rel' ic co cc = (
     (!i. no_Mat_decs (SND (compile_oracle ic i))) /\
     co = pure_co inc_compile_decs' o compile_oracle ic /\ compile
     ic = pure_cc inc_compile_decs' cc)`;;

let flat_to_closProof_state_rel_def = new_definition
  `flat_to_closProof_state_rel (s:('c,'ffi)flatSem_state)
  (t:('c,'ffi)closSem_state) <=>
     1 <= closSem_state_max_app t /\ flatSem_state_ffi
     s = closSem_state_ffi t /\ flatSem_state_clock
     s = closSem_state_clock t /\
     store_rel (flatSem_state_refs s) (closSem_state_refs t) /\
       ~(LENGTH (closSem_state_globals t) = 0) /\
     // HD t.globals = SOME (Closure NONE [] [] 1 clos_interpreter) ∧
     LIST_REL (OPTREL flat_to_closProof_v_rel) (flatSem_state_globals
       s) (TL (closSem_state_globals t)) /\
     install_config_rel' (flatSem_state_eval_config s)
       (closSem_state_compile_oracle t) (closSem_state_compile t)`;;
hol4_overload "state_rel" "flat_to_closProof_state_rel";;

let v_rel_to_list = prove
 (`!x y xs. flat_to_closProof_v_rel x y /\ flatSem_v_to_list x = SOME xs
  ==>
            (?ys. closSem_v_to_list y = SOME ys /\ LIST_REL
              flat_to_closProof_v_rel xs ys)`,
  CHEAT_TAC);;

let IMP_v_rel_to_list = prove
 (`!xs ys.
     LIST_REL flat_to_closProof_v_rel xs ys ==>
     flat_to_closProof_v_rel (list_to_v xs) (list_to_v ys)`,
  CHEAT_TAC);;

let lookup_refv = prove
 (`state_rel s1 t1 /\ store_lookup i (state_refs s1) = SOME
  (semanticPrimitives_Refv v) ==>
   (?w. FLOOKUP (state_refs t1) i = SOME (closSem_ValueArray [w])
     /\ flat_to_closProof_v_rel v w)`,
  CHEAT_TAC);;

let lookup_byte_array = prove
 (`state_rel s1 t1 /\ store_lookup i (state_refs s1) = SOME
  (semanticPrimitives_W8array bytes) ==>
   FLOOKUP (state_refs t1) i = SOME (closSem_ByteArray bytes)`,
  CHEAT_TAC);;

let lookup_array = prove
 (`state_rel s1 t1 /\ store_lookup i (state_refs s1) = SOME
  (semanticPrimitives_Varray vs) ==>
   (?ws. FLOOKUP (state_refs t1) i = SOME (closSem_ValueArray ws)
     /\ LIST_REL flat_to_closProof_v_rel vs ws)`,
  CHEAT_TAC);;

let lookup_thunk = prove
 (`state_rel s1 t1 /\ store_lookup i (state_refs s1) = SOME (Thunk m v)
  ==>
   (?w. FLOOKUP (state_refs t1) i = SOME (Thunk m w) /\
     flat_to_closProof_v_rel v w)`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_CONS_upd = prove
 (`flat_to_closProof_env_rel (flatSem_environment_v_fupd f env) m db /\
  flat_to_closProof_v_rel v1 v2 ==>
   flat_to_closProof_env_rel (flatSem_environment_v_fupd (\xs.
     (n,v1) :: f xs) env) (SOME n :: m) (v2 :: db)`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_CONS = prove
 (`flat_to_closProof_env_rel (flatSem_environment_v_fupd (K xs) env) m
  db /\ flat_to_closProof_v_rel v1 v2 ==>
   flat_to_closProof_env_rel (flatSem_environment_v_fupd (K ((n,v1)
     :: xs)) env) (SOME n :: m) (v2 :: db)`,
  CHEAT_TAC);;

(* env_rel_APPEND[local] *)
let flat_to_closProof_env_rel_APPEND = prove
 (`!name_prefix prefix db_prefix env m db.
     flat_to_closProof_env_rel env m db /\
     LIST_REL flat_to_closProof_v_rel (MAP SND prefix) db_prefix /\
     name_prefix = MAP (SOME o FST) prefix ==>
     flat_to_closProof_env_rel (flatSem_environment_v_fupd (K (prefix
       ++ flatSem_environment_v env)) env1) (name_prefix ++ m)
       (db_prefix ++ db)`,
  CHEAT_TAC);;

let initial_state'_def = new_definition
  `initial_state' b ffi ma code co cc k =
     mk_closSem_state [SOME (if b then
                            Closure NONE [] [] 1 clos_interpreter
                              else closSem_Unit)] FEMPTY ffi k cc co
                              code ma`;;

(* [simp,local] *)
let initate_state'_clock = prove
 (`(state_clock_fupd (K k) (initial_state' b ffi max_app FEMPTY co cc
  k')) =
   initial_state' b ffi max_app FEMPTY co cc k /\ state_clock
   (initial_state' b ffi max_app FEMPTY co cc k) = k`,
  CHEAT_TAC);;

let state_rel_initial_state = prove
 (`0 < max_app /\ install_config_rel' ec co cc ==>
   state_rel (initial_state ffi k ec)
             (initial_state' b ffi max_app FEMPTY co cc k)`,
  CHEAT_TAC);;

(* [local] *)
let state_rel_IMP_clock = prove
 (`state_rel s t ==> state_clock s = state_clock t`,
  CHEAT_TAC);;

(* state_rel_dec_clock[local] *)
let flat_to_closProof_state_rel_dec_clock = prove
 (`state_rel s t ==> state_clock s = state_clock t /\
     state_rel (dec_clock s) (dec_clock 1 t)`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:232-233: the ML values that the
   definitions below antiquote *)

(* HOL4 flat_to_closProofScript.sml:235-242: the ML values that the
   definitions below antiquote *)

(* HOL4 flat_to_closProofScript.sml:244-252: the ML values that the
   definitions below antiquote *)

let evaluate_decs_sing = prove
 (`evaluate_decs s [d] = evaluate_dec s d`,
  CHEAT_TAC);;

(* compile_correct *)
let flat_to_closProof_compile_correct = prove
 (`(!env (s:('c,'ffi)flatSem_state) es m db res1 s1 t.
      evaluate env s es = (s1,res1) /\ state_rel s t /\
        flat_to_closProof_env_rel env m db /\
      EVERY no_Mat es /\ ~(res1 = Rerr (Rabort Rtype_error)) ==>
      (?res2 t1.
        evaluate (flat_to_clos_compile m es,db,t) = (res2,t1) /\
          state_rel s1 t1 /\
        semanticPrimitivesProps_result_rel (LIST_REL
          flat_to_closProof_v_rel) flat_to_closProof_v_rel res1 res2))
          /\
   (!(s:('c,'ffi)flatSem_state) ds res1 s1 t.
     evaluate_decs s ds = (s1,res1) /\ state_rel s t /\ no_Mat_decs
       ds /\ ~(res1 = SOME (Rabort Rtype_error)) ==>
     (?res2 t1.
       evaluate (flat_to_clos_compile_decs ds,[],t) = (res2,t1) /\
         state_rel s1 t1 /\
       (?v. (let
              res1' = (match res1 with NONE -> Rval v | SOME e ->
                Rerr e) in
              semanticPrimitivesProps_result_rel (LIST_REL (\x y.
                T)) flat_to_closProof_v_rel res1' res2))))`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:300-302: a proof *)

(* HOL4 flat_to_closProofScript.sml:304-323: a proof *)

(* HOL4 flat_to_closProofScript.sml:325-330: a proof *)

(* HOL4 flat_to_closProofScript.sml:332-338: a proof *)

let dest_pat_from_case = prove
 (`(match pes with [(Pvar _1,_2)] -> T | _3 -> F) ==>
   (?nm rhs. dest_pat pes = SOME (nm,rhs))`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:347-371: a proof *)

(* HOL4 flat_to_closProofScript.sml:373-392: a proof *)

(* [local] *)
let LIST_REL_MAP_GENLIST = prove
 (`!funs f1 f2 R.
     (!n. n < LENGTH funs ==> R (f1 (EL n funs)) (f2 n)) ==>
     LIST_REL R (MAP f1 funs) (GENLIST f2 (LENGTH funs))`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:408-428: a proof *)

(* HOL4 flat_to_closProofScript.sml:430-435: a proof *)

let dest_Constant_IMP = prove
 (`flat_to_clos_dest_Constant x = SOME c <=>
     (?t. x = closLang_Op t (closLang_BlockOp (closLang_Constant c))
       []) \/
     (?t i. x = closLang_Op t (closLang_IntOp (closLang_Const i)) []
       /\ c = ConstInt i) \/
     (?t n. x = closLang_Op t (closLang_BlockOp (closLang_Cons n))
       [] /\ c = ConstCons n [])`,
  CHEAT_TAC);;

let dest_Constants_IMP = prove
 (`!xs ys.
     dest_Constants xs = SOME ys ==>
     LIST_REL (\x y. flat_to_clos_dest_Constant x = SOME y) xs ys`,
  CHEAT_TAC);;

let dest_Constant_evaluate = prove
 (`flat_to_clos_dest_Constant x = SOME c ==>
   evaluate ([x],db,s) = (Rval [make_const c],s)`,
  CHEAT_TAC);;

let dest_Constants_evaluate = prove
 (`!xs x.
     dest_Constants xs = SOME x ==>
     evaluate (xs,db,s) = (Rval (MAP make_const x),s)`,
  CHEAT_TAC);;

let evaluate_SmartCons = prove
 (`evaluate ([SmartCons t tag xs],db,s) = evaluate ([closLang_Op t
  (closLang_BlockOp (closLang_Cons tag)) xs],db,s)`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:487-498: a proof *)

(* HOL4 flat_to_closProofScript.sml:500-512: a proof *)

(* HOL4 flat_to_closProofScript.sml:514-517: a proof *)

(* [local] *)
let find_recfun_EL = prove
 (`!l0 n.
     n < LENGTH l0 /\ ALL_DISTINCT (MAP FST l0) ==>
     find_recfun (FST (EL n l0)) l0 = SOME (SND (EL n l0))`,
  CHEAT_TAC);;

(* [local] *)
let IMP_PAIR = prove
 (`z = (x,y) ==> x = FST z /\ y = SND z`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:536-554: a proof *)

(* HOL4 flat_to_closProofScript.sml:556-558: a proof *)

let state_rel_LEAST = prove
 (`state_rel s1 t1 ==>
   (LEAST (\ptr. ~(ptr IN FDOM (state_refs t1)))) = LENGTH
     (state_refs s1)`,
  CHEAT_TAC);;

let evaluate_Let_error = prove
 (`evaluate (es,env,s) = (Rerr err,s') ==>
   evaluate ([Let t es e],env,s) = (Rerr err,s')`,
  CHEAT_TAC);;

let evaluate_Op_error = prove
 (`evaluate (es,env,s) = (Rerr err,s') ==>
   evaluate ([closLang_Op t op es],env,s) = (Rerr err,s')`,
  CHEAT_TAC);;

let compile_op_evaluates_args = prove
 (`evaluate (xs,db,t) = (Rerr err,t1) /\ ~(op = flatLang_Src ast_Opapp)
  /\ ~(op = flatLang_Src ast_Eval) /\ ~(op = flatLang_Src (ast_ThunkOp
  ForceThunk)) ==>
   evaluate ([flat_to_clos_compile_op tra op xs],db,t) = (Rerr
     err,t1)`,
  CHEAT_TAC);;

(* v_rel_Boolv[simp] *)
let flat_to_closProof_v_rel_Boolv = prove
 (`flat_to_closProof_v_rel (Boolv b) v = (v = Boolv b)`,
  CHEAT_TAC);;

(* [simp] *)
let v_rel_Unitv = prove
 (`flat_to_closProof_v_rel Unitv v = (v = closSem_Block 0 [])`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:634-643: the ML values that the
   definitions below antiquote *)

let op_refs = prove
 (`(op = flatLang_Src ast_Opref) \/
   (?n. op = El n) \/
   (op = flatLang_Src ast_Opassign) ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_shifts = prove
 (`(?w s n. op = flatLang_Src (ast_Shift w s n)) ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_byte_arrays = prove
 (`op = flatLang_Src ast_Aw8length \/
   op = flatLang_Src ast_Aw8alloc \/
   op = flatLang_Src ast_Aw8sub_unsafe \/
   op = flatLang_Src ast_Aw8sub \/
   op = flatLang_Src ast_Aw8update_unsafe \/
   op = flatLang_Src ast_Aw8update ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\ LIST_REL
       flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_byte_copy = prove
 (`op = flatLang_Src ast_CopyStrAw8 \/
   op = flatLang_Src ast_CopyAw8Str \/
   op = flatLang_Src ast_CopyAw8Aw8 \/
   op = flatLang_Src ast_CopyStrStr \/
   op = flatLang_Src ast_XorAw8Str_unsafe ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

(* [local] *)
let MAP_n2w_o_ORD_11 = prove
 (`!l1 l2. MAP ((n2w:num->word8) o ORD) l1 = MAP (n2w o ORD) l2 <=> l1
  = l2`,
  CHEAT_TAC);;

let op_eq_gc = prove
 (`op = flatLang_Src ast_ConfigGC \/
   op = flatLang_Src ast_Equality ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let v_rel_v_to_char_list = prove
 (`!x ls y.
     v_to_char_list x = SOME ls /\ flat_to_closProof_v_rel x y ==>
     v_to_list y = SOME (MAP (closSem_Number o (&)) (MAP ORD ls))`,
  CHEAT_TAC);;

let op_str = prove
 (`op = flatLang_Src ast_Explode \/
   op = flatLang_Src ast_Implode \/
   op = flatLang_Src ast_Strlen \/
   op = flatLang_Src ast_Strsub \/
   op = flatLang_Src ast_Strcat ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\ evaluate (xs,db,t) =
       (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_globals = prove
 (`(?n. op = flatLang_GlobalVarLookup n) \/
   (?n. op = flatLang_GlobalVarInit n) \/
   (?n. op = flatLang_GlobalVarAlloc n) ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_vectors = prove
 (`op = flatLang_Src ast_Vlength \/
   op = flatLang_Src ast_Vsub \/
   op = flatLang_Src ast_Vsub_unsafe \/
   op = flatLang_Src ast_VfromList ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\ evaluate (xs,db,t) =
       (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_arrays = prove
 (`op = flatLang_Src ast_Aalloc \/
   op = flatLang_Src ast_AallocFixed \/
   op = flatLang_Src ast_Asub_unsafe \/
   op = flatLang_Src ast_Asub \/
   op = flatLang_Src ast_Alength \/
   op = flatLang_Src ast_Aupdate_unsafe \/
   op = flatLang_Src ast_Aupdate ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_blocks = prove
 (`(?n0 n1. op = TagLenEq n0 n1) \/
   (?l. op = LenEq l) \/
   op = flatLang_Src ast_ListAppend ==>
   (do_app s1 op vs = SOME (s2,res2) /\ state_rel s1
     (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

(* [local] *)
let MAP_n2w_ORD_eq = prove
 (`!s s'. (MAP (n2w o ORD) s = (MAP (n2w o ORD) s':word8 list)) <=> s
  = s'`,
  CHEAT_TAC);;

let imp_cmp_eq_num_cmp = prove
 (`!cmp. semanticPrimitives_int_cmp cmp (&m) (&n) <=> num_cmp cmp m n`,
  CHEAT_TAC);;

(* [local] *)
let check_type_IntT_flat_to_v = prove
 (`check_type ast_IntT (flat_to_v (v:flatSem_v)) ==> (?i. v = Litv
  (ast_IntLit i))`,
  CHEAT_TAC);;

(* [local] *)
let check_type_Float64T_flat_to_v = prove
 (`check_type ast_Float64T (flat_to_v (v:flatSem_v)) ==> (?w. v = Litv
  (ast_Float64 w))`,
  CHEAT_TAC);;

(* [local] *)
let check_type_WordT_W8_flat_to_v = prove
 (`check_type (ast_WordT ast_W8) (flat_to_v (v:flatSem_v)) ==> (?w. v
  = Litv (ast_Word8 w))`,
  CHEAT_TAC);;

(* [local] *)
let check_type_WordT_W64_flat_to_v = prove
 (`check_type (ast_WordT ast_W64) (flat_to_v (v:flatSem_v)) ==> (?w. v
  = Litv (ast_Word64 w))`,
  CHEAT_TAC);;

(* [local] *)
let check_type_CharT_flat_to_v = prove
 (`check_type ast_CharT (flat_to_v (v:flatSem_v)) ==> (?c. v = Litv
  (ast_Char c))`,
  CHEAT_TAC);;

(* [local] *)
let check_type_BoolT_flat_to_v = prove
 (`check_type ast_BoolT (flat_to_v (v:flatSem_v)) ==> v = Boolv F \/ v
  = Boolv T`,
  CHEAT_TAC);;

let op_arith = prove
 (`(?a ty. op = flatLang_Src (ast_Arith a ty)) ==>
   (do_app s1 op vs = SOME (s2,res2) /\ state_rel s1
     (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_from_to = prove
 (`(?ty1 ty2. op = flatLang_Src (ast_FromTo ty1 ty2)) ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_test = prove
 (`(?test ty. op = flatLang_Src (ast_Test test ty)) ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_ffi = prove
 (`(?n. op = flatLang_Src (ast_FFI n)) ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_id = prove
 (`op = flatLang_Id ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_eval = prove
 (`op = flatLang_Src ast_Eval ==>
   (do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let op_thunk = prove
 (`!th_op. op = flatLang_Src (ast_ThunkOp th_op) ==> (do_app s1 op vs =
  SOME (s2,res2) /\ state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let compile_op_correct = prove
 (`(do_app s1 op vs = SOME (s2,res2) /\
     state_rel s1 (t1:('c,'ffi)closSem_state) /\
     evaluate (xs,db,t) = (Rval ws,t1) /\
     LIST_REL flat_to_closProof_v_rel vs (REVERSE ws) /\
     LENGTH xs = LENGTH vs /\ ~(op = flatLang_Src ast_Opapp) /\ ~(op
       = flatLang_Src (ast_ThunkOp ForceThunk)) ==>
     (?res2' t1.
       evaluate ([flat_to_clos_compile_op tt op xs],db,t) =
         (res2',t1) /\
       state_rel s2 t1 /\
       semanticPrimitivesProps_result_rel (LIST_REL
         flat_to_closProof_v_rel) flat_to_closProof_v_rel (list_result
         res2) res2'))`,
  CHEAT_TAC);;

let v_rel_to_words = prove
 (`!x y xs. flat_to_closProof_v_rel x y /\ flatSem_v_to_words x = SOME
  xs ==>
            (?ys. closSem_v_to_words y = SOME xs)`,
  CHEAT_TAC);;

let v_rel_to_bytes = prove
 (`!x y xs. flat_to_closProof_v_rel x y /\ flatSem_v_to_bytes x = SOME
  xs ==>
            (?ys. closSem_v_to_bytes y = SOME xs)`,
  CHEAT_TAC);;

let do_eval_install = prove
 (`do_eval xs (flatSem_state_eval_config s) = SOME res /\
   state_rel s t /\
   LIST_REL flat_to_closProof_v_rel xs ys ==>
   (?decs exps eval_config t'. state_rel
     (flatSem_state_eval_config_fupd (K eval_config) s) t' /\
   res = (decs,eval_config,Unitv) /\
   closSem_do_install ys t = (if state_clock t' = 0 then (Rerr
     (Rabort Rtimeout_error),t') else (Rval (exps ++
     flat_to_clos_compile [] [Con backend_common_None NONE
     []]),dec_clock 1 t')) /\
   no_Mat_decs decs /\
   (?envv dsv. xs = [envv; dsv]) /\
   (~(state_clock t' = 0) ==> exps = flat_to_clos_compile_decs
     decs))`,
  CHEAT_TAC);;

let compile_single_DEEP_INTRO = prove
 (`!P. (!exp'. flat_to_clos_compile m [exp] = [exp'] ==> P [exp']) ==>
   P (flat_to_clos_compile m [exp])`,
  CHEAT_TAC);;

(* rel_update_thunk[local] *)
let flat_to_closProof_rel_update_thunk = prove
 (`state_rel s1 s2 /\
   LIST_REL flat_to_closProof_v_rel vs ys ==>
     (update_thunk [Loc v ptr] (state_refs s1) vs = SOME refs1 ==>
        (?refs2. update_thunk [closSem_RefPtr v ptr] (state_refs s2)
          ys = SOME refs2 /\
                state_rel (state_refs_fupd (K refs1) s1)
                  (state_refs_fupd (K refs2) s2)))`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:1778-1949: a proof *)

(* HOL4 flat_to_closProofScript.sml:1951-1962: a proof *)

(* HOL4 flat_to_closProofScript.sml:1964-1968: a proof *)

(* HOL4 flat_to_closProofScript.sml:1970-1993: a proof *)

(* HOL4 flat_to_closProofScript.sml:1995: a proof *)

(* HOL4 flat_to_closProofScript.sml:1997: a theorem that HOL4 states
   as the value of an ML expression: compile_decs_correct *)

let compile_decs_correct2 = prove
 (`evaluate_decs s1 decs = res_tup /\
   evaluate (flat_to_clos_compile_decs decs,[],s2) = (res2,t2) /\
   state_rel s1 s2 /\ no_Mat_decs decs /\ ~(SND res_tup = SOME
     (Rabort Rtype_error)) ==>
   state_rel (FST res_tup) t2 /\
   semanticPrimitivesProps_result_rel (\x y. T)
     flat_to_closProof_v_rel
     (match SND res_tup with NONE -> Rval [] | SOME e -> Rerr e)
       res2`,
  CHEAT_TAC);;

let FST_SND_EQ_CASE = prove
 (`FST = (\(a,b). a) /\ SND = (\(a,b). b)`,
  CHEAT_TAC);;

let evaluate_compile_prog_initial_state = prove
 (`0 < max_app ==>
   (evaluate (flat_to_clos_compile_prog ds,[],initial_state ffi
     max_app FEMPTY co cc k) =
    (match evaluate (flat_to_clos_compile_decs ds,[],
           initial_state' (has_install_list
             (flat_to_clos_compile_decs ds)) ffi max_app FEMPTY co cc
             k) with (Rval vs1,s1) -> (Rval (closSem_Unit :: vs1),s1)
             | res -> res))`,
  CHEAT_TAC);;

let evaluate_compile_prog_initial_state_FST_Err = prove
 (`0 < max_app ==>
   (FST (evaluate (flat_to_clos_compile_prog ds,[],initial_state ffi
     max_app FEMPTY co cc k)) = Rerr e <=>
    FST (evaluate (flat_to_clos_compile_decs ds,[],initial_state'
      (has_install_list (flat_to_clos_compile_decs ds))
                              ffi max_app FEMPTY co cc k)) = Rerr
                                e)`,
  CHEAT_TAC);;

let compile_semantics' = prove
 (`0 < max_app /\ no_Mat_decs ds /\ install_config_rel' ec co cc ==>
  ~(flatSem_semantics ec (ffi:'ffi ffi_state) ds = ffi_Fail) ==>
   closSem_semantics ffi max_app FEMPTY co cc
     (flat_to_clos_compile_prog ds) =
   flatSem_semantics ec ffi ds`,
  CHEAT_TAC);;

(* [local] *)
let inc_compile_decs_intro = prove
 (`pure_co (insert_interp ## I) o pure_co inc_compile_decs' o f =
   pure_co inc_compile_decs o f /\
   pure_cc inc_compile_decs' (pure_cc (insert_interp ## I) cc) =
   pure_cc inc_compile_decs cc`,
  CHEAT_TAC);;

let install_config_rel_def = new_definition
  `install_config_rel ic co cc <=>
     (!i. no_Mat_decs (SND (compile_oracle ic i))) /\
     co = pure_co inc_compile_decs o compile_oracle ic /\ compile
     ic = pure_cc inc_compile_decs cc`;;

(* compile_semantics *)
(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let flat_to_closProof_compile_semantics = prove
 (cake_as_vars (fun () ->
    `0 < max_app /\ no_Mat_decs ds /\ install_config_rel ec co cc ==>
  ~(semantics ec ffi ds = ffi_Fail) ==>
     semantics ffi max_app FEMPTY co cc (flat_to_clos_compile_prog
       ds) =
     semantics ec ffi ds`),
  CHEAT_TAC);;

let contains_App_SOME_APPEND = prove
 (`contains_App_SOME ma (xs ++ ys) <=>
   contains_App_SOME ma xs \/ contains_App_SOME ma ys`,
  CHEAT_TAC);;

(* HOL4 flat_to_closProofScript.sml:2214-2217: ML code, not ported *)

let EVERY_IMP_HD = prove
 (`EVERY P xs /\ ~(NULL xs) ==> P (HD xs)`,
  CHEAT_TAC);;

(* elist_globals_empty *)
let flat_to_closProof_elist_globals_empty = prove
 (`!es. closProps_elist_globals es = EMPTY_BAG <=>
        (!e. MEM e es ==> set_globals e = EMPTY_BAG)`,
  CHEAT_TAC);;

let set_globals_SmartCons = prove
 (`set_globals (SmartCons t tag xs) = elist_globals xs`,
  CHEAT_TAC);;

let esgc_free_SmartCons = prove
 (`esgc_free (SmartCons t tag xs) = EVERY esgc_free xs`,
  CHEAT_TAC);;

(* [simp] *)
let flat_FINITE_BAG_set_globals = prove
 (`(!e. FINITE_BAG (flatProps_set_globals e)) /\
   (!e. FINITE_BAG (flatProps_elist_globals e))`,
  CHEAT_TAC);;

(* [simp] *)
let clos_FINITE_BAG_set_globals = prove
 (`(!e. FINITE_BAG (closProps_set_globals e)) /\
   (!e. FINITE_BAG (closProps_elist_globals e))`,
  CHEAT_TAC);;

(* [local] *)
let BAG_IMAGE_FOLDR_lemma = prove
 (`!xs.
     BAG_IMAGE SUC (ITLIST (BAG_UNION) (MAP flatProps_set_globals xs)
       EMPTY_BAG) =
     ITLIST (BAG_UNION) (MAP (BAG_IMAGE SUC o set_globals) xs)
       EMPTY_BAG /\
     FINITE_BAG (ITLIST (BAG_UNION) (MAP flatProps_set_globals xs)
       EMPTY_BAG)`,
  CHEAT_TAC);;

let compile_set_globals = prove
 (`!m e. EVERY no_Mat e ==>
   closProps_elist_globals (flat_to_clos_compile m e) = BAG_IMAGE
     SUC (flatProps_elist_globals e)`,
  CHEAT_TAC);;

let compile_eq_set_globals = prove
 (`flat_to_clos_compile m exps = exps' /\
   EVERY no_Mat exps ==>
   closProps_elist_globals exps' = BAG_IMAGE SUC
     (flatProps_elist_globals exps)`,
  CHEAT_TAC);;

let compile_decs_set_globals = prove
 (`!decs. no_Mat_decs decs ==>
   closProps_elist_globals (flat_to_clos_compile_decs decs) =
   BAG_IMAGE SUC (flatProps_elist_globals decs)`,
  CHEAT_TAC);;

let compile_prog_set_globals = prove
 (`!decs. no_Mat_decs decs ==>
   closProps_elist_globals (flat_to_clos_compile_prog decs) =
     (BAG_UNION) (BAG_INSERT 0 (EMPTY_BAG)) (BAG_IMAGE SUC
     (flatProps_elist_globals decs))`,
  CHEAT_TAC);;

let compile_esgc_free = prove
 (`!m e. EVERY flatProps_esgc_free e /\ EVERY no_Mat e ==>
     EVERY closProps_esgc_free (flat_to_clos_compile m e)`,
  CHEAT_TAC);;

let compile_decs_esgc_free = prove
 (`!decs. EVERY (flatProps_esgc_free) decs /\
   no_Mat_decs decs ==>
   EVERY closProps_esgc_free (flat_to_clos_compile_decs decs)`,
  CHEAT_TAC);;

let compile_prog_esgc_free = prove
 (`!decs. EVERY (flatProps_esgc_free) decs /\
   no_Mat_decs decs ==>
   EVERY closProps_esgc_free (flat_to_clos_compile_prog decs)`,
  CHEAT_TAC);;

let contains_App_SOME_SmartCons = prove
 (`contains_App_SOME max_app [SmartCons t tag xs] =
   contains_App_SOME max_app xs`,
  CHEAT_TAC);;

let every_Fn_vs_NONE_SmartCons = prove
 (`every_Fn_vs_NONE [SmartCons t tag xs] =
   every_Fn_vs_NONE xs`,
  CHEAT_TAC);;

let no_mti_SmartCons = prove
 (`no_mti (SmartCons t tag xs) = EVERY no_mti xs`,
  CHEAT_TAC);;

let compile_syntactic_props = prove
 (`0 < max_app ==> (!m e.
     ~(contains_App_SOME max_app (flat_to_clos_compile m e)) /\
     EVERY no_mti (flat_to_clos_compile m e) /\
     every_Fn_vs_NONE (flat_to_clos_compile m e))`,
  CHEAT_TAC);;

let compile_decs_syntactic_props = prove
 (`!decs. EVERY no_mti (flat_to_clos_compile_decs decs) /\
     every_Fn_vs_NONE (flat_to_clos_compile_decs decs) /\
     (0 < max_app ==> ~(contains_App_SOME max_app
       (flat_to_clos_compile_decs decs)))`,
  CHEAT_TAC);;

(* [local] *)
let contains_App_SOME_compile_init = prove
 (`0 < max_app ==> ~(contains_App_SOME max_app [compile_init b])`,
  CHEAT_TAC);;

(* [local] *)
let no_mti_compile_init = prove
 (`no_mti (compile_init b)`,
  CHEAT_TAC);;

(* [local] *)
let every_Fn_vs_NONE_compile_init = prove
 (`every_Fn_vs_NONE [compile_init b]`,
  CHEAT_TAC);;

(* contains_App_SOME_compile_init[local] *)
let flat_to_closProof_contains_App_SOME_compile_init = prove
 (`1 <= max_app ==>
   contains_App_SOME max_app [compile_init b] = F`,
  CHEAT_TAC);;

let compile_prog_syntactic_props = prove
 (`!decs. EVERY no_mti (flat_to_clos_compile_prog decs) /\
     every_Fn_vs_NONE (flat_to_clos_compile_prog decs) /\
     (0 < max_app ==> ~(contains_App_SOME max_app
       (flat_to_clos_compile_prog decs)))`,
  CHEAT_TAC);;

let FST_inc_compile_syntactic_props = prove
 (`EVERY no_mti (FST (inc_compile_decs decs)) /\
   every_Fn_vs_NONE (FST (inc_compile_decs decs)) /\
   (0 < max_app ==> ~(contains_App_SOME max_app (FST
     (inc_compile_decs decs))))`,
  CHEAT_TAC);;

let FST_inc_compile_set_globals = prove
 (`!decs. no_Mat_decs decs ==>
   closProps_elist_globals (FST (inc_compile_decs decs)) =
   BAG_IMAGE SUC (flatProps_elist_globals decs)`,
  CHEAT_TAC);;

let FST_inc_compile_esgc_free = prove
 (`EVERY (flatProps_esgc_free) decs /\
   no_Mat_decs decs ==>
   EVERY closProps_esgc_free (FST (inc_compile_decs decs))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
