(* ======================================================== *)
(*  flat_to_closProof: ported from HOL4's
    compiler/backend/proofs/flat_to_closProofScript.sml  *)
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
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;

let v_rel = cake_inductive
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

let store_rel_def = cake_define
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

let inc_compile_decs'_def = cake_define
  `inc_compile_decs' decs = (flat_to_clos_compile_decs decs ++
     flat_to_clos_compile_decs [Con backend_common_None NONE
       []],[])`;;

let install_config_rel'_def = cake_define
  `install_config_rel' ic co cc = (
     (!i. no_Mat_decs (SND (compile_oracle ic i))) /\
     co = pure_co inc_compile_decs' o compile_oracle ic /\ compile
     ic = pure_cc inc_compile_decs' cc)`;;

let state_rel_def = cake_define
  `flat_to_closProof_state_rel (s:('c,'ffi)flatSem_state)
  (t:('c,'ffi)closSem_state) <=>
     1 <= closSem_state_max_app t /\ state_ffi
     s = state_ffi t /\ state_clock
     s = state_clock t /\
     store_rel (state_refs s) (state_refs t) /\ ~(
     LENGTH (state_globals t) = 0) /\
     LIST_REL (OPTREL flat_to_closProof_v_rel) (state_globals s) (TL
       (state_globals t)) /\
     install_config_rel' (flatSem_state_eval_config s)
       (compile_oracle t) (compile t)`;;
hol4_overload "state_rel" "flat_to_closProof_state_rel";;

let initial_state'_def = cake_define
  `initial_state' b ffi ma code co cc k =
     mk_closSem_state [SOME (if b then
                            Closure NONE [] [] 1 clos_interpreter
                              else closSem_Unit)] FEMPTY ffi k cc co
                              code ma`;;

(* HOL4 flat_to_closProofScript.sml:232-233: the ML values that the
   definitions below antiquote *)

(* HOL4 flat_to_closProofScript.sml:235-242: the ML values that the
   definitions below antiquote *)

(* HOL4 flat_to_closProofScript.sml:244-252: the ML values that the
   definitions below antiquote *)

(* HOL4 flat_to_closProofScript.sml:300-302: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:304-323: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:325-330: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:332-338: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:347-371: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:373-392: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:408-428: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:430-435: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:487-498: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:500-512: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:514-517: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:536-554: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:556-558: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:634-643: the ML values that the
   definitions below antiquote *)

(* HOL4 flat_to_closProofScript.sml:1778-1949: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:1951-1962: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:1964-1968: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:1970-1993: ML code, not ported *)

(* HOL4 flat_to_closProofScript.sml:1995: ML code, not ported *)

let install_config_rel_def = cake_define
  `install_config_rel ic co cc <=>
     (!i. no_Mat_decs (SND (compile_oracle ic i))) /\
     co = pure_co inc_compile_decs o compile_oracle ic /\ compile
     ic = pure_cc inc_compile_decs cc`;;

(* HOL4 flat_to_closProofScript.sml:2214-2217: ML code, not ported *)
