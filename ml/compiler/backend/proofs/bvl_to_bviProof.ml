(* ======================================================== *)
(*  bvl_to_bviProof: ported from HOL4's
    compiler/backend/proofs/bvl_to_bviProofScript.sml
    A proof theory about bvl_to_bvi.ml, with 9 definitions and 123
    theorems.  Needed by backendProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_to_bvi
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/bvl_to_bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/proofs/bvi_inlineProof.ml";;
needs "compiler/backend/proofs/bvi_letProof.ml";;
needs "compiler/backend/proofs/bvi_tailrecProof.ml";;
needs "compiler/backend/proofs/bvi_tmcProof.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;
needs "compiler/backend/proofs/bvl_handleProof.ml";;
needs "compiler/backend/proofs/bvl_inlineProof.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "lib/sorting.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["id"; "parts"];;

cake_hide_more ["str"];;

(* HOL4 bvl_to_bviProofScript.sml:22: ML code, not ported *)

(* value relation *)
(* HOL4 bvl_to_bviProofScript.sml:25: the overload num_stubs, which
   the port expands *)
(* HOL4 bvl_to_bviProofScript.sml:26: the overload nss, which the
   port expands *)

let _ = size_thms "bvlSem_v";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvl_to_bviProofScript.sml:34-38: the tactic that proves the
   termination *)
let adjust_bv_def = cake_define_list_try (fun () ->
  `MEASURE (bvlSem_v_size o SND)`)
  [`adjust_bv b (Number i:bvlSem_v) = bvlSem_Number i`;
   `adjust_bv b (Word64 w:bvlSem_v) = bvlSem_Word64 w`;
   `adjust_bv b (RefPtr l r:bvlSem_v) = bvlSem_RefPtr l (b r)`;
   `adjust_bv b (bvlSem_CodePtr c:bvlSem_v) = bvlSem_CodePtr
  (bvl_num_stubs + bvl_to_bvi_namespaces * c)`;
   `adjust_bv b (Block tag vs:bvlSem_v) = bvlSem_Block tag (MAP
  (adjust_bv b) vs)`];;

(* HOL4 bvl_to_bviProofScript.sml:40: ML code, not ported *)

let adjust_bv_Unit = cake_theorem "adjust_bv_Unit[simp]"
  (fun () ->
    `adjust_bv x Unit = Unit`)
  CHEAT_TAC;;

let adjust_bv_Boolv = cake_theorem "adjust_bv_Boolv[simp]"
  (fun () ->
    `adjust_bv x (Boolv b) = Boolv b`)
  CHEAT_TAC;;

let aux_code_installed_def = cake_define_list
  [`aux_code_installed [] t <=> T`;
   `aux_code_installed ((name,arg_count,body) :: rest) t <=>
         (sptree_lookup name t = SOME (arg_count,body)) /\
         aux_code_installed rest t`];;

let aux_code_installed_APPEND =
  cake_theorem "aux_code_installed_APPEND[local]"
  (fun () ->
    `!xs ys.
         aux_code_installed (xs ++ ys) code ==>
         aux_code_installed xs code /\
         aux_code_installed ys code`)
  CHEAT_TAC;;

let aux_code_installed_subspt = cake_theorem "aux_code_installed_subspt"
  (fun () ->
    `!x c1 c2. aux_code_installed x c1 /\ subspt c1 c2 ==>
                aux_code_installed x c2`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:78: the overload in_ns_0, which the
   port expands *)
(* HOL4 bvl_to_bviProofScript.sml:79: the overload in_ns_1, which the
   port expands *)

let names_ok_def = cake_define
  `bvl_to_bviProof_names_ok s_code t_code s_oracle <=>
     (!n k prog. s_oracle n = (k,prog) ==>
                 EVERY (\(name,arity,exp). handle_ok [exp]) prog) /\
     (let next' = FST (FST (s_oracle 0)) in
       (!n. n IN domain t_code /\ bvl_num_stubs <= n ==>
            (if (\n. n MOD bvl_to_bvi_namespaces = 1) n then n <
              bvl_num_stubs + bvl_to_bvi_namespaces * next' else (\n. n
              MOD bvl_to_bvi_namespaces = 0) n /\
                 (n - bvl_num_stubs) DIV bvl_to_bvi_namespaces IN
                   domain s_code)))`;;
hol4_overload "names_ok" "bvl_to_bviProof_names_ok";;

let state_rel_def = cake_define
  `bvl_to_bviProof_state_rel (b:num->num) s (t:('c,'ffi)bviSem_state)
  <=>
     INJ b (FDOM (state_refs s)) (FDOM (bviSem_state_refs t)) /\
     (!k. match FLOOKUP (state_refs s) k with NONE -> T | SOME
       (ValueArray vs) ->
              (FLOOKUP (bviSem_state_refs t) (b k) = SOME (ValueArray
                (MAP (adjust_bv b) vs))) | SOME (Thunk m v) ->
              (FLOOKUP (bviSem_state_refs t) (b k) = SOME (Thunk m
                (adjust_bv b v))) | SOME res -> (FLOOKUP
                (bviSem_state_refs t) (b k) = SOME res)) /\
     (state_ffi s = bviSem_state_ffi t) /\
     (!p. bviSem_state_global t = SOME p ==> ~(p IN IMAGE b (FDOM
       (state_refs s))) /\
            (?z. FLOOKUP (bviSem_state_refs t) p =
                  SOME (ValueArray
                    ((Number (&(SUC (LENGTH (state_globals s))))) ::
                     (MAP (the (Number (&0)) o OPTION_MAP (adjust_bv
                       b)) (state_globals s) ++
                     REPLICATE (z - (SUC (LENGTH (state_globals s))))
                       (Number (&0))))) /\
                SUC (LENGTH (state_globals s)) <= z)) /\
     (state_clock s = bviSem_state_clock t) /\
       bviSem_state_compile_oracle
     t = state_co compile_inc (compile_oracle s) /\ compile
     s = state_cc compile_inc (bviSem_state_compile t) /\
     (sptree_lookup AllocGlobal_location (bviSem_state_code t) = SOME
       AllocGlobal_code) /\
     (sptree_lookup CopyGlobals_location (bviSem_state_code t) = SOME
       CopyGlobals_code) /\
     (sptree_lookup ListLength_location (bviSem_state_code t) = SOME
       ListLength_code) /\
     (sptree_lookup FromListByte_location (bviSem_state_code t) =
       SOME FromListByte_code) /\
     (sptree_lookup ToListByte_location (bviSem_state_code t) = SOME
       ToListByte_code) /\
     (sptree_lookup SumListLength_location (bviSem_state_code t) =
       SOME SumListLength_code) /\
     (sptree_lookup ConcatByte_location (bviSem_state_code t) = SOME
       ConcatByte_code) /\
     // (lookup InitGlobals_location t.code = SOME InitGlobals_code start) ∧
     bvl_to_bviProof_names_ok (state_code s) (bviSem_state_code t)
       (compile_oracle s) /\
     (!name arity exp.
        (sptree_lookup name (state_code s) = SOME (arity,exp)) ==>
        (?n. let (c1,aux1,n1) = compile_exps n [exp] in
              (sptree_lookup (bvl_num_stubs + bvl_to_bvi_namespaces *
                name) (bviSem_state_code t) =
                 SOME (arity,bvi_let_compile_exp (HD c1))) /\
              aux_code_installed (append aux1) (bviSem_state_code t)
                /\
              handle_ok [exp]))`;;
hol4_overload "state_rel" "bvl_to_bviProof_state_rel";;

let state_rel_FLOOKUP_byteArray =
  cake_theorem "state_rel_FLOOKUP_byteArray"
  (fun () ->
    `!b s t m l n.
     state_rel b s t /\ FLOOKUP (state_refs s) n = SOME
       (ByteArray m l) ==> FLOOKUP (state_refs t) (b n) = SOME
       (ByteArray m l)`)
  CHEAT_TAC;;

let state_rel_FLOOKUP_valueArray =
  cake_theorem "state_rel_FLOOKUP_valueArray"
  (fun () ->
    `state_rel b s t /\
     FLOOKUP (state_refs s) ptr = SOME (ValueArray vs) ==>
       FLOOKUP (state_refs t) (b ptr) = SOME (ValueArray (MAP
         (adjust_bv b) vs))`)
  CHEAT_TAC;;

let state_rel_FLOOKUP_MutBlock =
  cake_theorem "state_rel_FLOOKUP_MutBlock"
  (fun () ->
    `state_rel b s t /\
     FLOOKUP (state_refs s) ptr = SOME (bvlSem_MutBlock tg fin l c
       r) ==>
       FLOOKUP (state_refs t) (b ptr) = SOME (bvlSem_MutBlock tg
         fin l c r)`)
  CHEAT_TAC;;

let state_rel_FLOOKUP_Thunk = cake_theorem "state_rel_FLOOKUP_Thunk"
  (fun () ->
    `state_rel b s t /\
     FLOOKUP (state_refs s) ptr = SOME (Thunk m v) ==>
       FLOOKUP (state_refs t) (b ptr) = SOME (Thunk m (adjust_bv
         b v))`)
  CHEAT_TAC;;

let _ = size_thms "bvlSem_v";;
(* HOL4 bvl_to_bviProofScript.sml:172-176: the tactic that proves the
   termination *)
let bv_ok_def = cake_define_wf
  `MEASURE (bvlSem_v_size o SND)`
  `bv_ok refs x2 =
        match (refs,x2) with
          ((refs:(num,bvlSem_v bvlSem_ref)fmap),(RefPtr l
            r:bvlSem_v)) -> r IN FDOM refs
        | (refs,(Block tag vs)) -> EVERY (bv_ok refs) vs
        | (refs,_1) -> T`;;

(* HOL4 bvl_to_bviProofScript.sml:178: ML code, not ported *)

let bv_ok_SUBSET_IMP = cake_theorem "bv_ok_SUBSET_IMP[local]"
  (fun () ->
    `!refs x refs2.
         bv_ok refs x /\ FDOM refs SUBSET FDOM refs2 ==> bv_ok
           refs2 x`)
  CHEAT_TAC;;

let bv_ok_Unit = cake_theorem "bv_ok_Unit[simp]"
  (fun () ->
    `bv_ok refs Unit`)
  CHEAT_TAC;;

let bv_ok_Boolv = cake_theorem "bv_ok_Boolv[simp]"
  (fun () ->
    `bv_ok refs (Boolv b)`)
  CHEAT_TAC;;

let bv_ok_IMP_adjust_bv_eq =
  cake_theorem "bv_ok_IMP_adjust_bv_eq[local]"
  (fun () ->
    `!b2 a1 b3.
         bv_ok refs a1 /\
         (!a. a IN FDOM refs ==> b2 a = b3 a) ==>
         (adjust_bv b2 a1 = adjust_bv b3 a1)`)
  CHEAT_TAC;;

let state_ok_def = cake_define
  `bvl_to_bviProof_state_ok (s:('c,'ffi)bvlSem_state) <=>
     EVERY (\x. match x with NONE -> T | SOME v -> bv_ok
       (bvlSem_state_refs s) v) (bvlSem_state_globals s) /\
     (!k. match FLOOKUP (bvlSem_state_refs s) k with SOME
       (ValueArray vs) -> EVERY (bv_ok (bvlSem_state_refs s)) vs |
       SOME (Thunk _2 v) -> bv_ok (bvlSem_state_refs s) v | _3 -> T)`;;
hol4_overload "state_ok" "bvl_to_bviProof_state_ok";;

(* evaluate preserves state_ok *)

let evaluate_ok_lemma = cake_theorem "evaluate_ok_lemma[local]"
  (fun () ->
    `(bvl_to_bviProof_state_ok (dec_clock n s) =
  bvl_to_bviProof_state_ok s) /\
       (state_refs (dec_clock n s) = state_refs s)`)
  CHEAT_TAC;;

let evaluate_IMP_bv_ok = cake_theorem "evaluate_IMP_bv_ok[local]"
  (fun () ->
    `(bvlSem_evaluate (xs,env,s) = (res,t)) ==>
       (bv_ok (state_refs s) a1 ==> bv_ok (state_refs t) a1) /\
       (EVERY (bv_ok (state_refs s)) as ==> EVERY (bv_ok
         (state_refs t)) as)`)
  CHEAT_TAC;;

let v_to_list_ok = cake_theorem "v_to_list_ok[local]"
  (fun () ->
    `!v x. v_to_list v = SOME x /\
            bv_ok refs v ==>
            EVERY (bv_ok refs) x`)
  CHEAT_TAC;;

let list_to_v_ok = cake_theorem "list_to_v_ok"
  (fun () ->
    `!xs. EVERY (bv_ok refs) xs ==> bv_ok refs (list_to_v xs)`)
  CHEAT_TAC;;

let list_to_v_ok_APPEND = cake_theorem "list_to_v_ok_APPEND"
  (fun () ->
    `!xs ys.
       bv_ok refs (list_to_v xs) /\
       bv_ok refs (list_to_v ys) ==>
         bv_ok refs (list_to_v (xs ++ ys))`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:264-276: code that the source has
   in a comment *)

let do_build_ok = cake_theorem "do_build_ok"
  (fun () ->
    `!parts' m n r q rs.
       bvlSem_do_build m n parts' (state_refs r) = (q,rs) /\
       bvl_to_bviProof_state_ok r /\ (!k. bv_ok (state_refs r) (m
         k)) ==>
       bvl_to_bviProof_state_ok (state_refs_fupd (K rs) r) /\
         bv_ok rs q`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:318-319: ML code, not ported *)

let do_app_ok_lemma = cake_theorem "do_app_ok_lemma[local]"
  (fun () ->
    `bvl_to_bviProof_state_ok r /\ EVERY (bv_ok (state_refs r)) a /\
     (do_app op a r = Rval (q,t)) ==>
     bvl_to_bviProof_state_ok t /\ bv_ok (state_refs t) q`)
  CHEAT_TAC;;

let do_app_ok = cake_theorem "do_app_ok"
  (fun () ->
    `bvl_to_bviProof_state_ok r /\ EVERY (bv_ok (state_refs r)) a /\
      (do_app op a r = Rval (q,t)) ==>
      bvl_to_bviProof_state_ok t /\ bv_ok (state_refs t) q /\
      (EVERY (bv_ok (state_refs r)) env ==> EVERY (bv_ok
        (state_refs t)) env)`)
  CHEAT_TAC;;
(* HOL4 bvl_to_bviProofScript.sml:596: ML code, not ported *)

let bvl_to_bviProof_dec_clock_inc_clock =
  cake_theorem "dec_clock_inc_clock[local]"
  (fun () ->
    `~(c = 0) ==> dec_clock 1 (inc_clock c t) =
                    inc_clock (c - 1) (t:('c,'ffi)bviSem_state)`)
  CHEAT_TAC;;

let find_code_bv_ok = cake_theorem "find_code_bv_ok"
  (fun () ->
    `bvlSem_find_code dest vs s = SOME (args,e2) /\
      EVERY (bv_ok (refs:(num,bvlSem_v bvlSem_ref)fmap)) vs ==>
        EVERY (bv_ok refs) args`)
  CHEAT_TAC;;

let evaluate_ok = cake_theorem "evaluate_ok"
  (fun () ->
    `!xs env s res t.
        (evaluate (xs,env,s) = (res,t)) /\
        bvl_to_bviProof_state_ok s /\ EVERY (bv_ok (state_refs s))
          env ==>
        bvl_to_bviProof_state_ok t /\
        (match res with Rval vs -> EVERY (bv_ok (state_refs t)) vs
          | Rerr (Rraise v) -> bv_ok (state_refs t) v | _4 -> T) /\
        EVERY (bv_ok (state_refs t)) env`)
  CHEAT_TAC;;

(* semantics lemmas *)

(* HOL4 bvl_to_bviProofScript.sml:680-694: a theorem that HOL4 states
   as the value of an ML expression: evaluate_MAP_Var *)

(* HOL4 bvl_to_bviProofScript.sml:696-707: a theorem that HOL4 states
   as the value of an ML expression: evaluate_MAP_Var2 *)

let bEval_bVarBound = cake_theorem "bEval_bVarBound[local]"
  (fun () ->
    `!xs vs s env.
         bVarBound (LENGTH vs) xs ==>
         (bvlSem_evaluate (xs,vs ++ env,s) = evaluate (xs,vs,s))`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:727: ML code, not ported *)

(* correctness of stubs *)

(* HOL4 bvl_to_bviProofScript.sml:731-732: ML code, not ported *)

let evaluate_CopyGlobals_code =
  cake_theorem "evaluate_CopyGlobals_code[local]"
  (fun () ->
    `!n l1 s.
      sptree_lookup CopyGlobals_location (state_code s) = SOME
        (3,SND CopyGlobals_code) /\
      FLOOKUP (state_refs s) p = SOME (ValueArray ls) /\
      FLOOKUP (state_refs s) p1 = SOME (ValueArray l1) /\ ~(p = p1)
        /\
      n < LENGTH ls /\ n < LENGTH l1 ==>
      (?c.
        evaluate ([SND CopyGlobals_code],
                  [RefPtr b1 p1; RefPtr b p; Number (&n)],
                  inc_clock c s) =
        (Rval [Unit],state_refs_fupd (K (state_refs s |+
          (p1,ValueArray (TAKE (SUC n) ls ++ DROP (SUC n) l1)))) s))`)
  CHEAT_TAC;;
(* HOL4 bvl_to_bviProofScript.sml:782-783: ML code, not ported *)

let evaluate_AllocGlobal_code =
  cake_theorem "evaluate_AllocGlobal_code[local]"
  (fun () ->
    `FLOOKUP (state_refs s) p = SOME (ValueArray (Number (&(SUC n)) ::
  ls)) /\ n <= LENGTH ls /\ bviSem_state_global
     s = SOME p /\
     sptree_lookup CopyGlobals_location (state_code s) = SOME
       (3,SND CopyGlobals_code) ==>
     (?p1 c extra.
       (~(p1 = p) ==> ~(p1 IN FDOM (state_refs s))) /\
       n + k + 1 <= LENGTH ls + extra /\
       evaluate ([SND AllocGlobal_code],[Number (&k)],inc_clock c
         s) =
         (Rval [Unit],state_refs_fupd (K
            (
            state_refs s |+ (p,ValueArray ((Number (&(SUC (n +
              k)))) :: ls)) |+ (p1,ValueArray (((Number (&(SUC (n +
              k)))) ::
                              ls) ++ (REPLICATE extra (Number
                                (&0))))))) (bviSem_state_global_fupd (K
                                (SOME p1))
          s)))`)
  CHEAT_TAC;;

let evaluate_ListLength_code = cake_theorem "evaluate_ListLength_code"
  (fun () ->
    `!lv vs n.
        sptree_lookup ListLength_location (state_code s) = SOME
          (2,SND ListLength_code) /\
        v_to_list lv = SOME vs ==>
        (?p1 c.
          evaluate ([SND ListLength_code],[lv; Number
            (&n)],inc_clock c s) =
            (Rval [Number (&(n + LENGTH vs))],s))`)
  CHEAT_TAC;;

let evaluate_FromListByte_code =
  cake_theorem "evaluate_FromListByte_code"
  (fun () ->
    `!lv vs n bs (s:('c,'ffi)bviSem_state).
      v_to_list lv = SOME (MAP (Number o (&)) vs) /\ LENGTH vs <=
        LENGTH bs /\
      sptree_lookup FromListByte_location (bviSem_state_code s) =
        SOME (3,SND FromListByte_code) /\
      EVERY (\n. n < 256) vs /\
      FLOOKUP (bviSem_state_refs s) p = SOME (ByteArray fl bs) /\ n
        = LENGTH bs - LENGTH vs ==>
      (?c.
        evaluate ([SND FromListByte_code],[lv; Number (&n); RefPtr
          b p],inc_clock c s) =
          (Rval [RefPtr b p],bviSem_state_refs_fupd (K
            (bviSem_state_refs s |+ (p,ByteArray fl (TAKE n bs ++ (MAP
            n2w vs))))) s))`)
  CHEAT_TAC;;

let evaluate_ToListByte_code = cake_theorem "evaluate_ToListByte_code"
  (fun () ->
    `!bs rest p (s:('c,'ffi)bviSem_state).
       sptree_lookup ToListByte_location (bviSem_state_code s) =
         SOME (3,SND ToListByte_code) /\
       FLOOKUP (bviSem_state_refs s) p = SOME (ByteArray fl (bs ++
         rest)) ==>
       (?c.
         evaluate ([SND ToListByte_code],
           [list_to_v (MAP (\b. Number (&(w2n b))) rest);
            Number (&(LENGTH bs)); RefPtr b p],inc_clock c s) =
           (Rval [list_to_v (MAP (\b. Number (&(w2n b))) bs ++
                             MAP (\b. Number (&(w2n b)))
                               rest)],bviSem_state_refs_fupd (K
                               (bviSem_state_refs s |+ (p,ByteArray fl
                               (bs ++ rest))))
            s))`)
  CHEAT_TAC;;

let evaluate_SumListLength_code =
  cake_theorem "evaluate_SumListLength_code"
  (fun () ->
    `!lv ps wss n.
     sptree_lookup SumListLength_location (state_code s) = SOME
       (2,SND SumListLength_code) /\
     v_to_list lv = SOME (MAP (RefPtr T) ps) /\
     MAP (FLOOKUP (state_refs s)) ps = MAP (SOME o ByteArray T) wss
       ==>
     (?c.
       evaluate
         ([SND SumListLength_code],[lv; Number (&n)],inc_clock c s)
           =
         (Rval [Number (&(n + LENGTH (FLAT wss)))],s))`)
  CHEAT_TAC;;

let evaluate_ConcatByte_code = cake_theorem "evaluate_ConcatByte_code"
  (fun () ->
    `!lv ps wss (s:('c,'ffi)bviSem_state) ds1 ds2 n.
     sptree_lookup SumListLength_location (bviSem_state_code s) =
       SOME (2,SND SumListLength_code) /\
     sptree_lookup ConcatByte_location (bviSem_state_code s) = SOME
       (3,SND ConcatByte_code) /\
     v_to_list lv = SOME (MAP (RefPtr T) ps) /\ ~(dst IN
       set_of_list ps) /\
     MAP (FLOOKUP (bviSem_state_refs s)) ps = MAP (SOME o ByteArray
       T) wss /\
     FLOOKUP (bviSem_state_refs s) dst = SOME (ByteArray T (ds1 ++
       ds2)) /\
     n = LENGTH ds1 /\ LENGTH (FLAT wss) = LENGTH ds2 ==>
     (?c.
       evaluate
         ([SND ConcatByte_code],[lv; Number (&n); RefPtr b
           dst],inc_clock c s) =
         (Rval [RefPtr b dst],bviSem_state_refs_fupd (K
           (bviSem_state_refs s |+ (dst,ByteArray T (ds1 ++ FLAT
           wss)))) s))`)
  CHEAT_TAC;;

(* compiler correctness *)

(* HOL4 bvl_to_bviProofScript.sml:1086-1087: ML code, not ported *)

let compile_exps_Var_list = cake_theorem "compile_exps_Var_list[local]"
  (fun () ->
    `!l n. EVERY isVar l ==> (?aux. compile_exps n l = (MAP (Var o
  destVar) l,aux,n) /\ append aux = [])`)
  CHEAT_TAC;;

let compile_int_thm = cake_theorem "compile_int_thm[local]"
  (fun () ->
    `!i env s. evaluate ([compile_int i],env,s) = (Rval [Number i],s)`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:1105-1136: a theorem that HOL4
   states as the value of an ML expression: compile_string_thm *)

let HD_APPEND3 = cake_theorem "HD_APPEND3"
  (fun () ->
    `0 < LENGTH (l1 ++ l2) ==> HD (l1 ++ l2 ++ l3) = HD (l1 ++ l2)`)
  CHEAT_TAC;;

let iEval_bVarBound = cake_theorem "iEval_bVarBound[local]"
  (fun () ->
    `!(n:num) xs n vs (s:('c,'ffi)bviSem_state) env.
       bVarBound (LENGTH vs) xs /\ handle_ok xs ==>
       (evaluate (FST (compile_exps n xs),vs ++ env,s) =
        evaluate (FST (compile_exps n xs),vs,s))`)
  CHEAT_TAC;;

let v_to_list_adjust = cake_theorem "v_to_list_adjust[local]"
  (fun () ->
    `!x. v_to_list (adjust_bv f x) = OPTION_MAP (MAP (adjust_bv f))
  (v_to_list x)`)
  CHEAT_TAC;;

let do_eq_adjust_lemma = cake_theorem "do_eq_adjust_lemma[local]"
  (fun () ->
    `(!refs x1 x2 b.
                 refs = state_refs r /\
                 do_eq refs x1 x2 = Eq_val b /\ state_rel b2 r t2
                   /\
                 bv_ok (state_refs r) x1 /\ bv_ok (state_refs r) x2
                   ==>
                 do_eq (state_refs t2) (adjust_bv b2 x1) (adjust_bv
                   b2 x2) = Eq_val b) /\
      (!refs x1 x2 b.
                 refs = state_refs r /\
                 do_eq_list refs x1 x2 = Eq_val b /\ state_rel b2 r
                   t2 /\
                 EVERY (bv_ok (state_refs r)) x1 /\ EVERY (bv_ok
                   (state_refs r)) x2 ==>
                 do_eq_list (state_refs t2) (MAP (adjust_bv b2)
                   x1) (MAP (adjust_bv b2) x2) = Eq_val b)`)
  CHEAT_TAC;;

let do_eq_adjust = cake_theorem "do_eq_adjust[local]"
  (fun () ->
    `do_eq (state_refs r) x1 x2 = Eq_val b /\ state_rel b2 r t2 /\
      bv_ok (state_refs r) x1 /\ bv_ok (state_refs r) x2 ==>
      do_eq (state_refs t2) (adjust_bv b2 x1) (adjust_bv b2 x2) =
        Eq_val b`)
  CHEAT_TAC;;

let list_to_v_adjust = cake_theorem "list_to_v_adjust"
  (fun () ->
    `!xs.
     list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (list_to_v
       xs)`)
  CHEAT_TAC;;

let list_to_v_adjust_APPEND = cake_theorem "list_to_v_adjust_APPEND"
  (fun () ->
    `!xs ys.
       list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (list_to_v
         xs) /\
       list_to_v (MAP (adjust_bv b) xs) = adjust_bv b (list_to_v
         xs) ==>
        list_to_v (MAP (adjust_bv b) (xs ++ ys)) =
        adjust_bv b (list_to_v (xs ++ ys))`)
  CHEAT_TAC;;

let do_app_adjust = cake_theorem "do_app_adjust[local]"
  (fun () ->
    `state_rel b2 s5 t2 /\
     (!i. ~(op = closLang_IntOp (closLang_Const i))) /\ (~(op =
       closLang_MemOp closLang_Ref)) /\
     (!flag. ~(op = closLang_MemOp (closLang_RefByte flag))) /\
       (~(op = closLang_MemOp closLang_RefArray)) /\
     (!n. ~(op = closLang_GlobOp (closLang_Global n))) /\ (!n. ~(op
       = closLang_GlobOp (closLang_SetGlobal n))) /\ (~(op =
       closLang_GlobOp closLang_AllocGlobal)) /\ ~(op =
       closLang_Install) /\
     (!t. ~(op = ThunkOp t)) /\
     (!n. ~(op = closLang_BlockOp (closLang_FromList n))) /\ (~(op
       = closLang_MemOp closLang_FromListByte)) /\
     (~(op = closLang_MemOp closLang_ToListByte)) /\ (!c. ~(op =
       closLang_BlockOp (closLang_Build c))) /\ ~(op = closLang_MemOp
       closLang_XorByte) /\
     (!b. ~(op = closLang_MemOp (closLang_CopyByte b))) /\ (~(op =
       closLang_MemOp closLang_ConcatByteVec)) /\ (!n. ~(op =
       closLang_Label n)) /\
     (do_app op (REVERSE a) s5 = Rval (q,r)) /\ EVERY (bv_ok
       (state_refs s5)) (REVERSE a) ==>
     (?t3. (do_app op (MAP (adjust_bv b2) (REVERSE a)) t2 =
           Rval (adjust_bv b2 q,t3)) /\
         state_rel b2 r t3)`)
  CHEAT_TAC;;

let eval_ind_alt = cake_theorem "eval_ind_alt"
  (fun () ->
    `!P.
       (!env s. P ([],env,s)) /\
       (!x y xs env s.
          (!v3 s1 v1.
             evaluate ([x],env,s) = (v3,s1) /\ v3 = Rval v1 ==>
             P (y :: xs,env,s1)) /\ P ([x],env,s) ==>
          P (x :: y :: xs,env,s)) /\ (!n env s. P ([Var n],env,s))
            /\
       (!x1 x2 x3 env s.
          (!v2 s1 vs.
             evaluate ([x1],env,s) = (v2,s1) /\ v2 = Rval vs /\
               ~(Boolv T = HD vs) /\ Boolv F = HD vs ==>
             P ([x3],env,s1)) /\
          (!v2 s1 vs.
             evaluate ([x1],env,s) = (v2,s1) /\ v2 = Rval vs /\
             Boolv T = HD vs ==>
             P ([x2],env,s1)) /\ P ([x1],env,s) ==>
          P ([If x1 x2 x3],env,s)) /\
       (!xs x2 env s.
          (!ys v2 s1 vs.
             list_size bvl_exp_size ys <= bvl_exp_size x2 /\
               evaluate (xs,env,s) = (v2,s1) ==>
             P (ys,vs,s1)) /\
          (!ys env. list_size bvl_exp_size ys <= bvl_exp_size x2
            ==> P (ys,env,s)) /\
          (!v2 s1 vs.
             evaluate (xs,env,s) = (v2,s1) /\ v2 = Rval vs ==>
             P ([x2],vs ++ env,s1)) /\
          P (xs,env,s) ==>
          P ([Let xs x2],env,s)) /\
       (!x1 env s. P ([x1],env,s) ==> P ([Raise x1],env,s)) /\
       (!op xs env s. P (xs,env,s) ==> P ([Op op xs],env,s)) /\
       (!x1 x2 env s1.
          (!v3 s v8 v.
             evaluate ([x1],env,s1) = (v3,s) /\ v3 = Rerr v8 /\
             v8 = Rraise v ==>
             P ([x2],v :: env,s)) /\
          (!xs env. list_size bvl_exp_size xs <= bvl_exp_size x1
            ==> P (xs,env,s1)) ==>
          P ([Handle x1 x2],env,s1)) /\
       (!force_loc n env s.
          (!thunk_v v1 v v' args exp.
             n < LENGTH env /\ thunk_v = EL n env /\
             dest_thunk thunk_v (state_refs s) = IsThunk v1 v /\ v1
               = NotEvaluated /\ ~(state_clock
             s = 0) /\
             find_code (SOME force_loc) [thunk_v; v] (state_code s)
               = SOME v' /\
             v' = (args,exp) /\ ~(state_clock s = 0) ==>
             P ([exp],args,dec_clock 1 s)) ==>
          P ([Force force_loc n],env,s)) /\
       (!x env s.
          (~(state_clock s = 0) ==> P ([x],env,dec_clock 1 s)) ==>
          P ([Tick x],env,s)) /\
       (!ticks dest xs env s1.
          (!v2 s vs v args exp.
             evaluate (xs,env,s1) = (v2,s) /\ v2 = Rval vs /\
             find_code dest vs (state_code s) = SOME v /\ v =
               (args,exp) /\
             ~(state_clock s < ticks + 1) ==>
             P ([exp],args,dec_clock (ticks + 1) s)) /\ P
               (xs,env,s1) ==>
          P ([Call ticks dest xs],env,s1)) ==>
       (!v v1 v2. P (v,v1,(v2:('c,'ffi)bvlSem_state)))`)
  CHEAT_TAC;;

let EVERY_isVar_evaluate_Rval_MEM =
  cake_theorem "EVERY_isVar_evaluate_Rval_MEM"
  (fun () ->
    `!l env a s r.
        EVERY isVar l /\ bvlSem_evaluate (l,env,s) = (Rval a,r) ==>
        EVERY (\x. MEM x env) a /\ s = r`)
  CHEAT_TAC;;

let do_app_Ref = cake_theorem "do_app_Ref[local]"
  (fun () ->
    `do_app (closLang_MemOp closLang_Ref) vs s =
        Rval
         (RefPtr T (LEAST (\ptr. ~(ptr IN FDOM (state_refs s)))),
          bvl_to_bvi
           (state_refs_fupd (K (state_refs
              s |+ ((LEAST (\ptr. ~(ptr IN FDOM (state_refs
                s)))),ValueArray vs))) (bvi_to_bvl s)) s)`)
  CHEAT_TAC;;

let state_rel_add_bytearray = cake_theorem "state_rel_add_bytearray"
  (fun () ->
    `state_rel b2 s5 (t2:('c,'ffi)bviSem_state) /\
     bvl_to_bviProof_state_ok s5 /\ ~(pp IN FDOM (state_refs s5))
       /\ ~(qq IN FDOM (bviSem_state_refs t2)) ==>
     state_rel ((pp =+ qq) b2)
       (state_refs_fupd (K (state_refs s5 |+ (pp,ByteArray fl ws)))
         s5)
       (bviSem_state_refs_fupd (K (bviSem_state_refs t2 |+
         (qq,ByteArray fl ws))) t2)`)
  CHEAT_TAC;;

let state_rel_add_thunk = cake_theorem "state_rel_add_thunk"
  (fun () ->
    `state_rel b s (t:('c,'ffi)bviSem_state) /\
     bvl_to_bviProof_state_ok s /\ ~(pp IN FDOM (state_refs s)) /\
       ~(qq IN FDOM (bviSem_state_refs t)) ==>
     state_rel ((pp =+ qq) b)
       (state_refs_fupd (K (state_refs s |+ (pp,Thunk m v))) s)
       (bviSem_state_refs_fupd (K (bviSem_state_refs t |+
         (qq,Thunk m (adjust_bv ((pp =+ qq) b) v)))) t)`)
  CHEAT_TAC;;

let state_rel_update_thunk = cake_theorem "state_rel_update_thunk"
  (fun () ->
    `state_rel b s (t:('c,'ffi)bviSem_state) /\
     bvl_to_bviProof_state_ok s /\
     ptr IN FDOM (state_refs s) ==>
     state_rel b
       (state_refs_fupd (K (state_refs s |+ (ptr,Thunk m v))) s)
       (bviSem_state_refs_fupd (K (bviSem_state_refs t |+ (b
         ptr,Thunk m (adjust_bv b v)))) t)`)
  CHEAT_TAC;;

let iEval_bVarBound_extra = cake_theorem "iEval_bVarBound_extra[local]"
  (fun () ->
    `!n xs n vs s env d.
      bVarBound (LENGTH vs) xs /\ handle_ok xs /\ d = FST
        (compile_exps n xs) ==>
      evaluate (d,vs ++ env,s) =
      evaluate (d,vs,s)`)
  CHEAT_TAC;;

let MAP_Num_11 = cake_theorem "MAP_Num_11[local]"
  (fun () ->
    `!(ns:word8 list) ns'.
       MAP (\x. Number (&(w2n x))) ns = MAP (\x. Number (&(w2n
         x))) ns' <=> ns' = ns`)
  CHEAT_TAC;;

let MAP_Word_11 = cake_theorem "MAP_Word_11[local]"
  (fun () ->
    `!ns ns'. MAP Word64 ns = MAP Word64 ns' <=> ns' = ns`)
  CHEAT_TAC;;

let IMP_v_to_bytes = cake_theorem "IMP_v_to_bytes"
  (fun () ->
    `!v1 ns.
        v_to_list v1 = SOME (MAP (Number o (&) o w2n) ns) ==>
        v_to_bytes (adjust_bv b2 v1) = SOME ns`)
  CHEAT_TAC;;

let IMP_v_to_words = cake_theorem "IMP_v_to_words"
  (fun () ->
    `v_to_list v2 = SOME (MAP Word64 ns') ==>
      v_to_words (adjust_bv b2 v2) = SOME ns'`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:1921-1923: ML code, not ported *)

let aux_code_installed_sublist =
  cake_theorem "aux_code_installed_sublist"
  (fun () ->
    `!aux ls.
      IS_SUBLIST ls aux /\
      ALL_DISTINCT (MAP FST ls) ==>
      aux_code_installed aux (fromAList ls)`)
  CHEAT_TAC;;

let compile_exps_aux_sorted = cake_theorem "compile_exps_aux_sorted"
  (fun () ->
    `!n es c aux n1. compile_exps n es = (c,aux,n1) ==>
     SORTED (<) (MAP FST (append aux)) /\
     EVERY (\x. ?n. x = bvl_num_stubs + bvl_to_bvi_namespaces * n +
       1) (MAP FST (append aux)) /\
     EVERY (between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
       (bvl_num_stubs + bvl_to_bvi_namespaces * n1)) (MAP FST (append
       aux)) /\ n <= n1`)
  CHEAT_TAC;;

let in_ns_def = cake_define
  `in_ns k n <=> n MOD bvl_to_bvi_namespaces = k`;;

let nss_in_ns = cake_theorem "nss_in_ns[simp]"
  (fun () ->
    `in_ns k bvl_to_bvi_namespaces <=> k = 0`)
  CHEAT_TAC;;

let mult_nss_in_ns = cake_theorem "mult_nss_in_ns[simp]"
  (fun () ->
    `in_ns k (m * bvl_to_bvi_namespaces) <=> k = 0`)
  CHEAT_TAC;;

let mult_nss_in_ns_1 = cake_theorem "mult_nss_in_ns_1[simp]"
  (fun () ->
    `in_ns k (m * bvl_to_bvi_namespaces + 1) <=> k = 1`)
  CHEAT_TAC;;

let mult_nss_in_ns_2 = cake_theorem "mult_nss_in_ns_2[simp]"
  (fun () ->
    `in_ns k (m * bvl_to_bvi_namespaces + 2) <=> k = 2`)
  CHEAT_TAC;;

let in_ns_1_add_1 = cake_theorem "in_ns_1_add_1"
  (fun () ->
    `in_ns 0 x ==> in_ns 1 (x + 1)`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:2007: the ML values that the
   definitions below antiquote *)

let in_ns_add_num_stubs = cake_theorem "in_ns_add_num_stubs[simp]"
  (fun () ->
    `in_ns k (bvl_num_stubs + x) <=> in_ns k x`)
  CHEAT_TAC;;

let compile_list_imp = cake_theorem "compile_list_imp[local]"
  (fun () ->
    `!n prog code n' name arity exp.
        compile_list n prog = (code,n') /\
        ALOOKUP prog name = SOME (arity,exp) ==>
        (?n0 c aux n1.
        compile_exps n0 [exp] = ([c],aux,n1) /\
        ALOOKUP (append code) (bvl_to_bvi_namespaces * name +
          bvl_num_stubs) = SOME (arity,bvi_let_compile_exp c) /\
        IS_SUBLIST (append code) (append aux))`)
  CHEAT_TAC;;

let nss_lemma = cake_theorem "nss_lemma[local]"
  (fun () ->
    `~(n * bvl_to_bvi_namespaces = k * bvl_to_bvi_namespaces + 1)`)
  CHEAT_TAC;;

let in_ns_0_simp = cake_theorem "in_ns_0_simp[local]"
  (fun () ->
    `in_ns 0 (bvl_to_bvi_namespaces * p_1 + bvl_num_stubs)`)
  CHEAT_TAC;;

let compile_inc_lemma = cake_theorem "compile_inc_lemma"
  (fun () ->
    `compile_inc next1 prog1 = (next2,prog2) ==>
      (ALL_DISTINCT (MAP FST prog1) ==>
      ALL_DISTINCT (MAP FST prog2)) /\ next1 <= next2 /\
      (!p. MEM (bvl_num_stubs + p * bvl_to_bvi_namespaces) (MAP FST
        prog2) ==>
           MEM p (MAP FST prog1)) /\
      (!p. MEM p (MAP FST prog2) ==>
           (if in_ns 0 p then (?q. bvl_num_stubs + q *
             bvl_to_bvi_namespaces = p) else
           in_ns 1 p /\ bvl_num_stubs + bvl_to_bvi_namespaces *
             next1 <= p /\
                        p < bvl_num_stubs + bvl_to_bvi_namespaces
                          * next2))`)
  CHEAT_TAC;;

let compile_inc_next = cake_theorem "compile_inc_next"
  (fun () ->
    `bvl_to_bvi_compile_inc next1 prog1 = (next2,prog2) ==>
      next1 <= next2`)
  CHEAT_TAC;;

let compile_inc_DISTINCT = cake_theorem "compile_inc_DISTINCT"
  (fun () ->
    `compile_inc next1 prog1 = (next2,prog2) /\
      ALL_DISTINCT (MAP FST prog1) ==>
      ALL_DISTINCT (MAP FST prog2)`)
  CHEAT_TAC;;

let compile_inc_next_range = cake_theorem "compile_inc_next_range"
  (fun () ->
    `compile_inc next1 prog1 = (next2,prog2) /\
      MEM x (MAP FST prog2) ==>
      (if (\n. n MOD bvl_to_bvi_namespaces = 1) x then
        bvl_num_stubs + bvl_to_bvi_namespaces * next1 <= x /\ x <
        bvl_num_stubs + bvl_to_bvi_namespaces * next2 else (\n. n MOD
        bvl_to_bvi_namespaces = 0) x /\ bvl_num_stubs <= x /\ MEM ((x
        - bvl_num_stubs) DIV bvl_to_bvi_namespaces) (MAP FST prog1))`)
  CHEAT_TAC;;

let not_in_ns_1 = cake_theorem "not_in_ns_1[local]"
  (fun () ->
    `~((\n. n MOD bvl_to_bvi_namespaces = 1) (bvl_num_stubs + name *
  bvl_to_bvi_namespaces))`)
  CHEAT_TAC;;

let names_nss_DIV_nss = cake_theorem "names_nss_DIV_nss[local]"
  (fun () ->
    `(name * bvl_to_bvi_namespaces) DIV bvl_to_bvi_namespaces = name`)
  CHEAT_TAC;;

(* the compiled bvi Call handler post-processes its result, rejecting an
   escaping Ret; a mapped bvl handler result (raised values lifted through Exn)
   never raises a Ret, so the post-processing is the identity *)
let call_SOME_handler_result =
  cake_theorem "call_SOME_handler_result[local]"
  (fun () ->
    `!f g r t.
       (match map_result f (\v. Exn (g v)) r with
          Rval v6 -> (Rval v6,t) | Rerr (Rraise (Exn v14)) -> (Rerr
            (Rraise (Exn v14)),t) | Rerr (Rraise (Ret v15)) -> (Rerr
            (Rabort Rtype_error),t) | Rerr (Rabort v11) -> (Rerr (Rabort
            v11),t)) =
       (map_result f (\v. Exn (g v)) r,t)`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:2182: ML code, not ported *)

(* HOL4 bvl_to_bviProofScript.sml:2184-2199: the ML values that the
   definitions below antiquote *)

let compile_exps_correct = cake_theorem "compile_exps_correct"
  (fun () ->
    `!xs env s1 n res s2 (t1:('c,'ffi)bviSem_state) n2 ys aux b1.
       (evaluate (xs,env,s1) = (res,s2)) /\ ~(res = Rerr (Rabort
         Rtype_error)) /\
       (compile_exps n xs = (ys,aux,n2)) /\
       state_rel b1 s1 t1 /\
       bvl_to_bviProof_state_ok s1 /\ EVERY (bv_ok (state_refs s1))
         env /\
       aux_code_installed (append aux) (bviSem_state_code t1) /\
       handle_ok xs /\ IS_SOME (bviSem_state_global t1) ==>
       (?t2 b2 c.
          (evaluate (ys,MAP (adjust_bv b2) env,inc_clock c t1) =
             (map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv
               b2 v)) res,t2)) /\
          state_rel b2 s2 t2 /\
          (MAP (adjust_bv b1) env = MAP (adjust_bv b2) env) /\
          (!a. a IN FDOM (state_refs s1) ==> (b1 a = b2 a)))`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviProofScript.sml:2232-3504: a proof *)
    (* the ops reserved for bvi_tmc are the remaining ones compile_op does not
       leave alone; each is ruled out by bvlSem$do_app being Error on it *)
(* HOL4 bvl_to_bviProofScript.sml:3507-3519: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3521-3527: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3529-3585: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3587-3595: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3597-3665: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3667-3785: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3787-3808: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3810-3965: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:3967-4026: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:4028-4054: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:4056-4171: a proof *)

(* HOL4 bvl_to_bviProofScript.sml:4173: a proof *)

(* composed compiler correctness *)

let compile_single_evaluate = cake_theorem "compile_single_evaluate"
  (fun () ->
    `evaluate ([Call 0 (SOME start) []],[],s1) = (res,s2) /\
     state_rel b1 s1 t1 /\ IS_SOME (bviSem_state_global t1) /\
       bvl_to_bviProof_state_ok s1 /\ ~(res = Rerr (Rabort Rtype_error))
       ==>
     (?ck b2 t2.
       evaluate ([Call 0 (SOME (bvl_num_stubs +
         bvl_to_bvi_namespaces * start)) [] NONE],[],inc_clock ck t1) =
         (map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2
           v)) res,t2) /\
       state_rel b2 s2 (t2:('c,'ffi)bviSem_state))`)
  CHEAT_TAC;;

let evaluate_REPLICATE_0 = cake_theorem "evaluate_REPLICATE_0[local]"
  (fun () ->
    `!n. evaluate (REPLICATE n (Op (closLang_IntOp (closLang_Const
  (&0))) []),env,s) =
             (Rval (REPLICATE n (Number (&0))),s)`)
  CHEAT_TAC;;

let bvi_stubs_evaluate = cake_theorem "bvi_stubs_evaluate"
  (fun () ->
    `!kk start' ffi0 code k.
       0 < k /\ bvl_num_stubs <= start' ==>
     (let t0 = (mk_bviSem_state (FEMPTY |+
                  (0,ValueArray ([Number (&1)] ++
                    REPLICATE ((MIN (MAX kk 1) InitGlobals_max) -
                      1) (Number (&0))))) k (SOME 0) cc co (fromAList
                      (bvl_to_bvi_stubs start' kk ++ code))
                      ffi0:('c,'ffi)bviSem_state) in
        evaluate ([Call 0 (SOME InitGlobals_location) [] NONE],[],
          initial_state ffi0 (fromAList (bvl_to_bvi_stubs start' kk
            ++ code)) co cc (k + 1)) =
     (let (r,s) = evaluate ([Call 0 (SOME start') [] NONE],[],t0)
       in
       ((match r with Rerr (Rraise (Exn v)) -> Rval [v] | _5 ->
         r),s)))`)
  CHEAT_TAC;;

let compile_list_distinct_locs =
  cake_theorem "compile_list_distinct_locs"
  (fun () ->
    `!n prog code_app code n'.
       ALL_DISTINCT (MAP FST prog) /\
       compile_list n prog = (code_app,n') /\
       code = append code_app ==>
       ALL_DISTINCT (MAP FST code) /\
       EVERY (between (bvl_num_stubs + bvl_to_bvi_namespaces * n)
         (bvl_num_stubs + bvl_to_bvi_namespaces * n'))
         (FILTER (\n. in_ns 1 (n - bvl_num_stubs)) (MAP FST code))
           /\
       FILTER (\n. in_ns 0 (n - bvl_num_stubs)) (MAP FST code) =
         MAP (\n. bvl_num_stubs + bvl_to_bvi_namespaces * n) (MAP
           FST prog) /\
        // redundant, but useful
        EVERY ((<=) bvl_num_stubs) (MAP FST code) /\
       EVERY (\n. ~(in_ns 2 (n - bvl_num_stubs)) /\ ~(in_ns 3 (n -
         bvl_num_stubs)))
         (MAP FST code) /\
       n <= n'`)
  CHEAT_TAC;;

let bvl_to_bviProof_compile_prog_evaluate =
  cake_theorem "compile_prog_evaluate"
  (fun () ->
    `compile_prog start n prog = (start',prog',n') /\
     evaluate ([Call 0 (SOME start) []],[],
               initial_state ffi0 (fromAList prog) co (state_cc
                 compile_inc cc) k) = (r,s) /\
     0 < k /\
     ALL_DISTINCT (MAP FST prog) /\
     handle_ok (MAP (SND o SND) prog) /\
     (!n. EVERY ((\e. handle_ok [e]) o SND o SND) (SND (co n))) /\
     n' <= (FST (FST (co 0))) /\ ~(r = Rerr (Rabort Rtype_error))
       ==>
     (?ck b2 s2.
     evaluate ([Call 0 (SOME start') [] NONE],[],
               initial_state ffi0 (fromAList prog') (state_co
                 compile_inc co) cc (k + ck)) =
       (map_result (MAP (adjust_bv b2)) (\v. Exn (adjust_bv b2 v))
         (match r with Rerr (Rraise v) -> Rval [v] | _6 -> r),s2)
           /\
     state_rel b2 s (s2:('c,'ffi)bviSem_state))`)
  CHEAT_TAC;;

let bvl_to_bviProof_compile_prog_semantics =
  cake_theorem "compile_prog_semantics"
  (fun () ->
    `compile_prog start n prog = (start',prog',n') /\
     ALL_DISTINCT (MAP FST prog) /\
     handle_ok (MAP (SND o SND) prog) /\
     (!n. EVERY ((\e. handle_ok [e]) o SND o SND) (SND (co n))) /\
     n' <= FST (FST ((co:num->(num#'c)#(num#num#bvl_exp) list) 0))
       /\ ~(semantics (ffi0:'ffi ffi_state) (fromAList prog) co
       (state_cc compile_inc cc) start = ffi_Fail) ==>
     semantics ffi0 (fromAList prog') (state_co compile_inc co) cc
       start' =
     semantics ffi0 (fromAList prog) co (state_cc compile_inc cc)
       start`)
  CHEAT_TAC;;

let compile_prog_distinct_locs =
  cake_theorem "compile_prog_distinct_locs"
  (fun () ->
    `compile_prog start n prog = (k,prog1,n1) /\ ALL_DISTINCT (MAP FST
  prog) ==>
      ALL_DISTINCT (MAP FST prog1) /\
      EVERY (between (bvl_to_bvi_namespaces * n + bvl_num_stubs)
        (bvl_to_bvi_namespaces * n1 + bvl_num_stubs))
        (FILTER (\n. in_ns 1 (n - bvl_num_stubs)) (MAP FST prog1))
          /\
      EVERY (\n. ~(in_ns 2 (n - bvl_num_stubs)) /\ ~(in_ns 3 (n -
        bvl_num_stubs)))
        (MAP FST prog1)`)
  CHEAT_TAC;;

let ODD_lemma = cake_theorem "ODD_lemma[local]"
  (fun () ->
    `ODD (2 * n + k) = ODD k`)
  CHEAT_TAC;;

let full_cc_def = cake_define
  `full_cc c cc =
     (let limit' = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_cc (compile_inc limit' split cut) (state_cc compile_inc
         (state_cc (bvi_tailrec_compile_prog
           (bvl_to_bvi_config_do_tailrec c))
           (state_cc (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
             c))
             (state_cc bvi_inline_compile_inc cc)))))`;;

let full_co_def = cake_define
  `full_co c co =
     (let limit' = bvl_to_bvi_config_inline_size_limit c in
     let split = bvl_to_bvi_config_split_main_at_seq c in
     let cut = bvl_to_bvi_config_exp_cut c in
       state_co bvi_inline_compile_inc
         (state_co (bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
           c))
           (state_co (bvi_tailrec_compile_prog
             (bvl_to_bvi_config_do_tailrec c))
             (state_co compile_inc
               (state_co (compile_inc limit' split cut) co)))))`;;

let compile_prog_avoids_nss_2 = cake_theorem "compile_prog_avoids_nss_2"
  (fun () ->
    `compile_prog start f prog = (loc,code,new_state) /\
      ALL_DISTINCT (MAP FST prog) /\
      k MOD bvl_to_bvi_namespaces = 2 /\ MEM k (MAP FST code) ==>
      k <= bvl_num_stubs`)
  CHEAT_TAC;;

let compile_prog_avoids_nss_3 = cake_theorem "compile_prog_avoids_nss_3"
  (fun () ->
    `compile_prog start f prog = (loc,code,new_state) /\
      ALL_DISTINCT (MAP FST prog) /\
      k MOD bvl_to_bvi_namespaces = 3 /\ MEM k (MAP FST code) ==>
      k <= bvl_num_stubs`)
  CHEAT_TAC;;

(* --- no_mutcons: syntactic absence of MutCons operations ---

   The bvi_tmc pass requires its input to be free of MutCons operations
   (the no_mutcons conjunct of bvi_tmc's input_condition).  This holds
   unconditionally: compile_op compiles out the mem_ops reserved for
   bvi_tmc (bvlSem$do_app is Error on them), so no bvi code produced by
   bvl_to_bvi contains them.  The lemmas below carry the property
   through bvi_let and bvi_tailrec to the two input_condition
   obligations in compile_semantics below. *)

(* no_mutcons preservation: bvi_let *)

let bvi_let_delete_var_no_mutcons =
  cake_theorem "bvi_let_delete_var_no_mutcons[local]"
  (fun () ->
    `no_mutcons x ==> no_mutcons (bvi_let_delete_var x)`)
  CHEAT_TAC;;

let bvi_let_compile_no_mutcons =
  cake_theorem "bvi_let_compile_no_mutcons[local]"
  (fun () ->
    `(!env d e. no_mutcons e ==> no_mutcons (bvi_let_compile_sing env d
  e)) /\
     (!env d es. EVERY no_mutcons es ==> EVERY no_mutcons
       (bvi_let_compile_list env d es))`)
  CHEAT_TAC;;

let bvi_let_compile_exp_no_mutcons =
  cake_theorem "bvi_let_compile_exp_no_mutcons[local]"
  (fun () ->
    `no_mutcons x ==> no_mutcons (bvi_let_compile_exp x)`)
  CHEAT_TAC;;

(* no_mutcons preservation: bvl_to_bvi compile *)

let compile_int_no_mutcons =
  cake_theorem "compile_int_no_mutcons[local,simp]"
  (fun () ->
    `no_mutcons (compile_int i)`)
  CHEAT_TAC;;

let compile_op_no_mutcons = cake_theorem "compile_op_no_mutcons[local]"
  (fun () ->
    `EVERY no_mutcons c1 ==> no_mutcons (compile_op op c1)`)
  CHEAT_TAC;;

let compile_exps_sing_no_mutcons =
  cake_theorem "compile_exps_sing_no_mutcons[local]"
  (fun () ->
    `(!n e c aux n1.
        compile_exps_sing n e = (c,aux,n1) ==>
        no_mutcons c /\ EVERY (no_mutcons o SND o SND) (append
          aux)) /\
     (!n es c aux n1.
        compile_exps_list n es = (c,aux,n1) ==>
        EVERY no_mutcons c /\ EVERY (no_mutcons o SND o SND)
          (append aux))`)
  CHEAT_TAC;;

let compile_exps_no_mutcons =
  cake_theorem "compile_exps_no_mutcons[local]"
  (fun () ->
    `compile_exps n xs = (c,aux,n1) ==>
     EVERY no_mutcons c /\ EVERY (no_mutcons o SND o SND) (append
       aux)`)
  CHEAT_TAC;;

let stubs_no_mutcons = cake_theorem "stubs_no_mutcons[local]"
  (fun () ->
    `EVERY (no_mutcons o SND o SND) (bvl_to_bvi_stubs start n)`)
  CHEAT_TAC;;

let compile_single_no_mutcons =
  cake_theorem "compile_single_no_mutcons[local]"
  (fun () ->
    `bvl_to_bvi_compile_single n p = (q,n1) ==>
     EVERY (no_mutcons o SND o SND) (append q)`)
  CHEAT_TAC;;

let compile_list_no_mutcons =
  cake_theorem "compile_list_no_mutcons[local]"
  (fun () ->
    `!n progs q n1.
       compile_list n progs = (q,n1) ==>
       EVERY (no_mutcons o SND o SND) (append q)`)
  CHEAT_TAC;;

let compile_inc_no_mutcons = cake_theorem "compile_inc_no_mutcons"
  (fun () ->
    `bvl_to_bvi_compile_inc n prog = (n1,prog1) ==>
     EVERY (no_mutcons o SND o SND) prog1`)
  CHEAT_TAC;;

let compile_prog_no_mutcons = cake_theorem "compile_prog_no_mutcons"
  (fun () ->
    `compile_prog start n prog = (loc,code,n1) ==>
     EVERY (no_mutcons o SND o SND) code`)
  CHEAT_TAC;;

(* no_mutcons preservation: bvi_tailrec *)

let to_op_no_mutcons = cake_theorem "to_op_no_mutcons[local,simp]"
  (fun () ->
    `no_mutcons_op (to_op op)`)
  CHEAT_TAC;;

let apply_op_no_mutcons = cake_theorem "apply_op_no_mutcons[local,simp]"
  (fun () ->
    `no_mutcons (apply_op op e1 e2) <=> no_mutcons e1 /\ no_mutcons e2`)
  CHEAT_TAC;;

let id_from_op_no_mutcons =
  cake_theorem "id_from_op_no_mutcons[local,simp]"
  (fun () ->
    `no_mutcons (id_from_op op)`)
  CHEAT_TAC;;

let let_wrap_no_mutcons = cake_theorem "let_wrap_no_mutcons[local,simp]"
  (fun () ->
    `no_mutcons (let_wrap arity id x) <=> no_mutcons id /\ no_mutcons
  x`)
  CHEAT_TAC;;

let get_bin_args_no_mutcons =
  cake_theorem "get_bin_args_no_mutcons[local]"
  (fun () ->
    `get_bin_args exp = SOME (e1,e2) /\ no_mutcons exp ==>
     no_mutcons e1 /\ no_mutcons e2`)
  CHEAT_TAC;;

let opbinargs_no_mutcons = cake_theorem "opbinargs_no_mutcons[local]"
  (fun () ->
    `opbinargs opr exp = SOME (e1,e2) /\ no_mutcons exp ==>
     no_mutcons e1 /\ no_mutcons e2`)
  CHEAT_TAC;;

let try_swap_no_mutcons = cake_theorem "try_swap_no_mutcons[local]"
  (fun () ->
    `no_mutcons exp ==> no_mutcons (try_swap loc opr exp)`)
  CHEAT_TAC;;

let check_op_no_mutcons = cake_theorem "check_op_no_mutcons[local]"
  (fun () ->
    `check_op ts opr loc exp = SOME exp2 /\ no_mutcons exp ==>
  no_mutcons exp2`)
  CHEAT_TAC;;

let args_from_no_mutcons = cake_theorem "args_from_no_mutcons[local]"
  (fun () ->
    `args_from f = SOME (t,d,args,hdl) /\ no_mutcons f ==>
     EVERY no_mutcons args /\ (match hdl with NONE -> T | SOME h
       -> no_mutcons h)`)
  CHEAT_TAC;;

let push_call_no_mutcons = cake_theorem "push_call_no_mutcons[local]"
  (fun () ->
    `no_mutcons x /\ no_mutcons f ==>
     no_mutcons (push_call n op acc x (args_from f))`)
  CHEAT_TAC;;

let rewrite_catchall_no_mutcons =
  cake_theorem "rewrite_catchall_no_mutcons[local]"
  (fun () ->
    `(match check_op ts opr loc exp with
        NONE -> (F,apply_op opr (Var acc) exp) | SOME v1 ->
          (match opbinargs opr v1 with
            NONE -> (F,apply_op opr (Var acc) v1) | SOME (xs,f) ->
              (T,push_call next opr acc xs (args_from f)))) = (r,y) /\
     no_mutcons exp ==>
     no_mutcons y`)
  CHEAT_TAC;;

let rewrite_no_mutcons = cake_theorem "rewrite_no_mutcons[local]"
  (fun () ->
    `!loc next' opr acc ts exp r y.
       rewrite loc next' opr acc ts exp = (r,y) /\ no_mutcons exp
         ==> no_mutcons y`)
  CHEAT_TAC;;

let tailrec_compile_exp_no_mutcons =
  cake_theorem "tailrec_compile_exp_no_mutcons[local]"
  (fun () ->
    `bvi_tailrec_compile_exp loc next arity exp = SOME (aux,opt) /\
     no_mutcons exp ==>
     no_mutcons aux /\ no_mutcons opt`)
  CHEAT_TAC;;

let bvi_tailrec_compile_each_no_mutcons =
  cake_theorem "bvi_tailrec_compile_each_no_mutcons[local]"
  (fun () ->
    `!next' prog next1 prog1.
       bvi_tailrec_compile_each next' prog = (next1,prog1) /\
       EVERY (no_mutcons o SND o SND) prog ==>
       EVERY (no_mutcons o SND o SND) prog1`)
  CHEAT_TAC;;

let bvi_tailrec_compile_prog_no_mutcons =
  cake_theorem "bvi_tailrec_compile_prog_no_mutcons"
  (fun () ->
    `!b next' prog next1 prog1.
       bvi_tailrec_compile_prog b next' prog = (next1,prog1) /\
       EVERY (no_mutcons o SND o SND) prog ==>
       EVERY (no_mutcons o SND o SND) prog1`)
  CHEAT_TAC;;

(* A name outside namespace 2 cannot be one of bvi_tailrec's fresh names,
   which are all congruent to num_stubs + 2 modulo the namespace count. *)
(* NB free_names must be qualified: bvi_tmcProof defines an identically
   printing (and identically stated) constant of the same name. *)
let EVERY_free_names_not_in_ns_2 =
  cake_theorem "EVERY_free_names_not_in_ns_2[local]"
  (fun () ->
    `EVERY (\n. ~(in_ns 2 (n - bvl_num_stubs))) (MAP FST xs) ==>
     EVERY (bvi_tailrecProof_free_names (bvl_num_stubs + 2) o
       FST) xs`)
  CHEAT_TAC;;

let compile_semantics = cake_theorem "compile_semantics"
  (fun () ->
    `compile start c names prog =
  (start',prog',inlines,bvi_inlines,n1,n2,n3,names') /\
     FST (FST (co 0)) = inlines /\
     FST (SND (FST (co 0))) = n1 /\
     FST (SND (SND (FST (co 0)))) = n2 /\
     FST (SND (SND (SND (FST (co 0))))) = n3 /\
     FST (SND (SND (SND (SND (FST (co 0)))))) = bvi_inlines /\
     (!n. ALL_DISTINCT (MAP FST (SND (co n))) /\
          bvl_num_stubs <= FST (SND (SND (FST (co n)))) /\ in_ns 2
            (FST (SND (SND (FST (co n))))) /\
          bvl_num_stubs <= FST (SND (SND (SND (FST (co n))))) /\
          in_ns 3 (FST (SND (SND (SND (FST (co n))))))) /\
     ALL_DISTINCT (MAP FST prog) ==>
     ~(semantics (ffi0:'ffi ffi_state) (fromAList prog) co (full_cc
       c cc) start = ffi_Fail) ==>
     semantics ffi0 (fromAList prog') (full_co c co) cc start' =
     semantics ffi0 (fromAList prog) co (full_cc c cc) start`)
  CHEAT_TAC;;


let compile_distinct_names = cake_theorem "compile_distinct_names"
  (fun () ->
    `bvl_to_bvi_compile n0 c ns p2 = (k,p3,l,bl,n1,n2,ns') /\
     ALL_DISTINCT (MAP FST p2) /\ bvl_to_bvi_config_next_name2
     c = bvl_num_stubs + 2 + n02 * bvl_to_bvi_namespaces ==>
     EVERY (\n. data_num_stubs <= n) (MAP FST p3) /\
     ALL_DISTINCT (MAP FST p3)`)
  CHEAT_TAC;;


let ALL_DISTINCT_MAP_FST_SND_full_co =
  cake_theorem "ALL_DISTINCT_MAP_FST_SND_full_co"
  (fun () ->
    `ALL_DISTINCT (MAP FST (SND (co n))) /\
     (FST (SND (SND (FST (co n)))) MOD bvl_to_bvi_namespaces = 2)
       /\
     (FST (SND (SND (SND (FST (co n))))) MOD bvl_to_bvi_namespaces
       = 3) ==>
     ALL_DISTINCT (MAP FST (SND (full_co c co n)))`)
  CHEAT_TAC;;


let destLet_code_labels = cake_theorem "destLet_code_labels"
  (fun () ->
    `destLet x = (y,z) ==>
      BIGUNION (set_of_list (MAP get_code_labels y)) UNION
        get_code_labels z SUBSET get_code_labels x`)
  CHEAT_TAC;;

let compile_int_code_labels =
  cake_theorem "compile_int_code_labels[simp]"
  (fun () ->
    `!i. get_code_labels (compile_int i) = {}`)
  CHEAT_TAC;;

let compile_op_code_labels = cake_theorem "compile_op_code_labels"
  (fun () ->
    `get_code_labels (compile_op op c) SUBSET
      BIGUNION (set_of_list (MAP get_code_labels c)) UNION
      IMAGE (\n. bvl_num_stubs + n * bvl_to_bvi_namespaces)
        (assign_get_code_label op) UNION
      set_of_list (MAP FST (bvl_to_bvi_stubs x y))`)
  CHEAT_TAC;;

let compile_exps_get_code_labels =
  cake_theorem "compile_exps_get_code_labels"
  (fun () ->
    `!n xs ys aux m.
      bvl_to_bvi_compile_exps n xs = (ys,aux,m) ==>
       BIGUNION (set_of_list (MAP get_code_labels ys)) UNION
       BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         (append aux))) SUBSET
       IMAGE (\k. bvl_num_stubs + (k * bvl_to_bvi_namespaces))
         (BIGUNION (set_of_list (MAP get_code_labels xs))) UNION
       {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n <=
         k /\ k < m} UNION
       set_of_list (MAP FST (bvl_to_bvi_stubs x y))`)
  CHEAT_TAC;;

let compile_exps_aux_contains = cake_theorem "compile_exps_aux_contains"
  (fun () ->
    `!n es c aux n1. compile_exps n es = (c,aux,n1) ==>
      {bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n <=
        k /\ k < n1} SUBSET set_of_list (MAP FST (append aux))`)
  CHEAT_TAC;;

let compile_single_get_code_labels =
  cake_theorem "compile_single_get_code_labels"
  (fun () ->
    `!n p code m. bvl_to_bvi_compile_single n p = (code,m) ==>
        BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
          (append code))) SUBSET
        IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
          (get_code_labels (SND (SND p))) UNION
        set_of_list (MAP FST (append code)) UNION
        set_of_list (MAP FST (bvl_to_bvi_stubs x y))`)
  CHEAT_TAC;;

let compile_list_get_code_labels =
  cake_theorem "compile_list_get_code_labels"
  (fun () ->
    `!n p code m. compile_list n p = (code,m) ==>
     n <= m /\
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
       (append code))) SUBSET
     set_of_list (MAP FST (append code)) UNION
     IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
       (BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         p))) UNION
     set_of_list (MAP FST (bvl_to_bvi_stubs x y))`)
  CHEAT_TAC;;

let bvl_to_bviProof_compile_prog_get_code_labels =
  cake_theorem "compile_prog_get_code_labels"
  (fun () ->
    `!s n p t q m.
     bvl_to_bvi_compile_prog s n p = (t,q,m) ==>
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND) q))
       SUBSET (
       bvl_num_stubs + s * bvl_to_bvi_namespaces) INSERT (
       set_of_list (MAP FST q) UNION
       IMAGE (\k. bvl_num_stubs + (k * bvl_to_bvi_namespaces))
         (BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
         p))))`)
  CHEAT_TAC;;

(* The code-label containment for the whole pass boundary, composing all four
   stages of [compile]: bvl_inline, compile_prog, bvi_tailrec and bvi_inline.
   The last two only ever shrink the label set relative to the names they keep,
   so the shape matches compile_prog_get_code_labels above, widened by the
   fresh names bvi_tailrec allocates. *)
let compile_get_code_labels = cake_theorem "compile_get_code_labels"
  (fun () ->
    `!start' c names prog loc code inlines bvi_inlines n1 n2 n3 names'.
     bvl_to_bvi_compile start' c names prog =
       (loc,code,inlines,bvi_inlines,n1,n2,n3,names') ==>
     BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
       code)) SUBSET (
       bvl_num_stubs + start' * bvl_to_bvi_namespaces) INSERT (
       set_of_list (MAP FST code) UNION
       IMAGE (\k. bvl_num_stubs + (k * bvl_to_bvi_namespaces))
         (BIGUNION (set_of_list (MAP (get_code_labels o SND o SND)
           prog))) UNION
       {bvl_num_stubs + 2 + k * bvl_to_bvi_namespaces | k |
         bvl_num_stubs + 2 + k * bvl_to_bvi_namespaces < n2} UNION
       {bvl_num_stubs + 3 + k * bvl_to_bvi_namespaces | k |
         bvl_num_stubs + 3 + k * bvl_to_bvi_namespaces < n3})`)
  CHEAT_TAC;;

let compile_list_code_labels_domain =
  cake_theorem "compile_list_code_labels_domain"
  (fun () ->
    `!n p code m. compile_list n p = (code,m) ==>
       n <= m /\
       set_of_list (MAP FST (append code)) =
       IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
         (set_of_list (MAP FST p)) UNION
       {bvl_num_stubs + k * bvl_to_bvi_namespaces + 1 | k | n <=
         k /\ k < m}`)
  CHEAT_TAC;;

let compile_prog_code_labels_domain =
  cake_theorem "compile_prog_code_labels_domain"
  (fun () ->
    `!s n p t q m.
     bvl_to_bvi_compile_prog s n p = (t,q,m) ==>
     set_of_list (MAP FST q) =
       IMAGE (\k. bvl_num_stubs + k * bvl_to_bvi_namespaces)
         (set_of_list (MAP FST p)) UNION
       {bvl_num_stubs + k * bvl_to_bvi_namespaces + 1 | k | n <= k
         /\ k < m} UNION
       set_of_list (MAP FST (bvl_to_bvi_stubs x y))`)
  CHEAT_TAC;;

cake_hide [];;
