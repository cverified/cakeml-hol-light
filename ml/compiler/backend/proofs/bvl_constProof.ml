(* ======================================================== *)
(*  bvl_constProof: ported from HOL4's
    compiler/backend/proofs/bvl_constProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_const
*)

needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

let v_rel_def = cake_define
  `bvl_constProof_v_rel (:'c) (:'ffi) a x y xs ys =
     (match a with Var n -> (\l n. oEL n l) ys n = SOME x | Op _1 _2
       ->
       (x = y) /\
       (!(s:('c,'ffi)bvlSem_state) env. evaluate ([a],env,s) =
         (Rval [x],s)) | _3 -> F)`;;
hol4_overload "v_rel" "bvl_constProof_v_rel";;

let env_rel_def = cake_define
  `bvl_constProof_env_rel x1 x2 x3 e1 e2 =
        match (x1,x2,x3,e1,e2) with
          ((:'c),(:'ffi),[],e1,e2) -> (e1 = e2)
        | ((:'c),(:'ffi),(NONE :: rest),(x :: e1),(y :: e2)) ->
        (x = y) /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
        | ((:'c),(:'ffi),(SOME a :: rest),(x :: e1),(y :: e2)) ->
        bvl_constProof_v_rel (:'c) (:'ffi) a x y (x :: e1) (y :: e2)
          /\ bvl_constProof_env_rel (:'c) (:'ffi) rest e1 e2
        | (_4,_5,_6,_7,_8) -> F`;;
hol4_overload "env_rel" "bvl_constProof_env_rel";;
