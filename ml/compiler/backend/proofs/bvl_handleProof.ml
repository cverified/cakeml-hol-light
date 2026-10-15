(* ======================================================== *)
(*  bvl_handleProof: ported from HOL4's
    compiler/backend/proofs/bvl_handleProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for bvl_handle
*)

needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/db_vars.ml";;
needs "compiler/backend/proofs/bvl_constProof.ml";;
needs "compiler/backend/semantics/bvlProps.ml";;
needs "compiler/backend/semantics/bvlSem.ml";;
needs "semantics/ast.ml";;

let let_ok_def = cake_define
  `let_ok x1 =
        match x1 with
          (Let xs b:bvl_exp) -> EVERY isVar xs /\ bVarBound (LENGTH
            xs) [b]
        | _1 -> F`;;

let handle_ok_def = cake_define_list
  [`handle_ok [] <=> T`;
   `handle_ok ((x:bvl_exp) :: y :: xs) <=>
         handle_ok [x] /\ handle_ok (y :: xs)`;
   `handle_ok [(Var v:bvl_exp)] <=> T`;
   `handle_ok [(If x1 x2 x3:bvl_exp)] <=>
         handle_ok [x1] /\ handle_ok [x2] /\ handle_ok [x3]`;
   `handle_ok [(Let xs x2:bvl_exp)] <=>
         (if LENGTH xs = 0 then
           let_ok x2 /\ (!ys y. x2 = Let ys y ==> handle_ok [y])
             else
           handle_ok xs /\ handle_ok [x2])`;
   `handle_ok [(Raise x1:bvl_exp)] <=> handle_ok [x1]`;
   `handle_ok [(Tick x1:bvl_exp)] <=> handle_ok [x1]`;
   `handle_ok [(Op op xs:bvl_exp)] <=> handle_ok xs`;
   `handle_ok [(Handle x1 x2:bvl_exp)] <=>
         (match x1 with Let xs b ->
             EVERY isVar xs /\ bVarBound (LENGTH xs) [b] /\
             handle_ok [b] /\ handle_ok [x2] | _4 -> F)`;
   `handle_ok [(Force loc n:bvl_exp)] <=> T`;
   `handle_ok [(Call ticks dest xs:bvl_exp)] <=> handle_ok xs`];;

let env_rel_def = cake_define
  `bvl_handleProof_env_rel l env env1 =
     LIST_RELi (\i v1 v2. has_var i l ==> v1 = v2) env env1`;;
hol4_overload "env_rel" "bvl_handleProof_env_rel";;
