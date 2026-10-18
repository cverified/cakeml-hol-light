(* ======================================================== *)
(*  bvi_letProof: ported from HOL4's
    compiler/backend/proofs/bvi_letProofScript.sml
    A proof theory about bvi_let.ml, with 2 definitions and 19
    theorems.  Needed by bvl_to_bviProof.ml and compilerProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_let
*)

needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

let v_rel_def = cake_define
  `bvi_letProof_v_rel a x y xs ys <=> (\l n. oEL n l) ys a = SOME x`;;
hol4_overload "v_rel" "bvi_letProof_v_rel";;

let env_rel_def = cake_define
  `bvi_letProof_env_rel x1 d e1 e2 =
        match (x1,e1,e2) with
          ([],e1,e2) -> (e1 = DROP d e2)
        | ((a :: rest),(x :: e1),(y :: e2)) ->
        bvi_letProof_v_rel a x y (x :: e1) (y :: e2) /\
          bvi_letProof_env_rel rest d e1 e2
        | (_1,_2,_3) -> F`;;
hol4_overload "env_rel" "bvi_letProof_env_rel";;

let env_rel_length = cake_theorem "env_rel_length"
  (fun () ->
    `!ax env env2. bvi_letProof_env_rel ax d env env2 ==> LENGTH env
  <= LENGTH env2`)
  CHEAT_TAC;;

let env_rel_LLOOKUP_NONE = cake_theorem "env_rel_LLOOKUP_NONE[local]"
  (fun () ->
    `!ax env env2 n d.
         bvi_letProof_env_rel ax d env env2 /\
         (\l n. oEL n l) ax n = NONE /\
         n < LENGTH env ==>
         n + d < LENGTH env2 /\
         EL (n + d) env2 = EL n env`)
  CHEAT_TAC;;

let env_rel_LOOKUP_SOME = cake_theorem "env_rel_LOOKUP_SOME[local]"
  (fun () ->
    `!env env2 ax x n d.
         bvi_letProof_env_rel ax d env env2 /\
         (\l n. oEL n l) ax n = SOME x ==>
         bvi_letProof_v_rel x (EL n env) (EL n env2) (DROP n env)
           (DROP n env2)`)
  CHEAT_TAC;;

let evaluate_delete_var_Rerr_SING =
  cake_theorem "evaluate_delete_var_Rerr_SING"
  (fun () ->
    `!x s r e env2.
        evaluate ([x],env2,s) = (Rerr e,r) /\ ~(
        e = Rabort Rtype_error) ==>
        evaluate ([delete_var x],env2,s) = (Rerr e,r)`)
  CHEAT_TAC;;

let evaluate_delete_var_Rerr =
  cake_theorem "evaluate_delete_var_Rerr[local]"
  (fun () ->
    `!xs s r e env2.
         evaluate (xs,env2,s) = (Rerr e,r) /\ ~(
         e = Rabort Rtype_error) ==>
         evaluate (MAP delete_var xs,env2,s) = (Rerr e,r)`)
  CHEAT_TAC;;

let evaluate_delete_var_Rval =
  cake_theorem "evaluate_delete_var_Rval[local]"
  (fun () ->
    `!xs env2 s a r ax env d.
         evaluate (xs,env2,(s:('c,'ffi)bviSem_state)) = (Rval a,r)
           /\
         bvi_letProof_env_rel ax d env env2 ==>
         (?b. evaluate (MAP delete_var xs,env2,s) = (Rval b,r) /\
             bvi_letProof_env_rel (extract_list xs ++ ax) d (a ++
               env) (b ++ env2))`)
  CHEAT_TAC;;

let evaluate_SNOC_Rval = cake_theorem "evaluate_SNOC_Rval"
  (fun () ->
    `evaluate (SNOC x y,env,s) = (Rval a,r) ==>
      (?a1 a2 r1.
        a = SNOC a1 a2 /\ LENGTH y = LENGTH a2 /\
        evaluate (y,env,s) = (Rval a2,r1) /\
        evaluate ([x],env,r1) = (Rval [a1],r))`)
  CHEAT_TAC;;

let compile_CONS = cake_theorem "compile_CONS"
  (fun () ->
    `compile ax d (x :: xs) = compile ax d [x] ++ compile ax d xs`)
  CHEAT_TAC;;

let compile_APPEND = cake_theorem "compile_APPEND"
  (fun () ->
    `!xs ys ax d. compile ax d (xs ++ ys) = compile ax d xs ++ compile
  ax d ys`)
  CHEAT_TAC;;

let IMP_COMM = cake_theorem "IMP_COMM"
  (fun () ->
    `(b1 ==> b2 ==> b3) <=> (b2 ==> b1 ==> b3)`)
  CHEAT_TAC;;

let exp_size_APPEND = cake_theorem "exp_size_APPEND"
  (fun () ->
    `!xs ys. exp2_size (xs ++ ys) = exp2_size xs + exp2_size ys`)
  CHEAT_TAC;;

let env_rel_MAP = cake_theorem "env_rel_MAP"
  (fun () ->
    `!ax env1 env2 d a.
        bvi_letProof_env_rel ax d env1 env2 ==>
        bvi_letProof_env_rel (MAP ((+) (LENGTH a)) ax) (d +
          LENGTH a) env1 (a ++ env2)`)
  CHEAT_TAC;;

let env_rel_REPLICATE_0 = cake_theorem "env_rel_REPLICATE_0[local]"
  (fun () ->
    `!vs ax d env1 env2.
       bvi_letProof_env_rel ax d env1 env2 ==>
       bvi_letProof_env_rel (REPLICATE (LENGTH vs) 0 ++ ax) d (vs
         ++ env1) (vs ++ env2)`)
  CHEAT_TAC;;

let evaluate_env_rel = cake_theorem "evaluate_env_rel"
  (fun () ->
    `!xs env1 (s1:('c,'ffi)bviSem_state) ax env2 res s2 ys d.
        (evaluate (xs,env1,s1) = (res,s2)) /\
        bvi_letProof_env_rel ax d env1 env2 /\ ~(
        res = Rerr (Rabort Rtype_error)) ==>
        (evaluate (compile ax d xs,env2,s1) = (res,s2))`)
  CHEAT_TAC;;

(* HOL4 bvi_letProofScript.sml:220-237: a proof *)

(* HOL4 bvi_letProofScript.sml:239-249: a proof *)

(* HOL4 bvi_letProofScript.sml:251-257: a proof *)

(* HOL4 bvi_letProofScript.sml:259-270: a proof *)

(* HOL4 bvi_letProofScript.sml:272-287: a proof *)
   (* the handler now post-processes its result (rejecting an escaping Ret);
      split that inner case (the Ret branch is impossible as res <> type error),
      then close each surviving handler outcome by the induction hypothesis *)
(* HOL4 bvi_letProofScript.sml:291-297: a proof *)

(* HOL4 bvi_letProofScript.sml:299-307: a proof *)

(* HOL4 bvi_letProofScript.sml:309-320: a proof *)

(* HOL4 bvi_letProofScript.sml:322-330: a proof *)

(* HOL4 bvi_letProofScript.sml:332-346: a proof *)

(* HOL4 bvi_letProofScript.sml:348-387: a proof *)

(* HOL4 bvi_letProofScript.sml:389: a proof *)

(* HOL4 bvi_letProofScript.sml:391-394: a theorem that HOL4 states as
   the value of an ML expression *)

let evaluate_compile_exp = cake_theorem "evaluate_compile_exp"
  (fun () ->
    `evaluate ([d],env,s) = (r,t) /\ ~(
      r = Rerr (Rabort Rtype_error)) ==>
      evaluate ([bvi_let_compile_exp d],env,s) = (r,t)`)
  CHEAT_TAC;;

let dest_var_code_labels = cake_theorem "dest_var_code_labels[simp]"
  (fun () ->
    `!x. get_code_labels (delete_var x) = get_code_labels x`)
  CHEAT_TAC;;

let compile_code_labels = cake_theorem "compile_code_labels"
  (fun () ->
    `!x y z. BIGUNION (set_of_list (MAP get_code_labels'
  (bvi_let_compile x y z))) =
             BIGUNION (set_of_list (MAP get_code_labels' z))`)
  CHEAT_TAC;;

let compile_exp_code_labels =
  cake_theorem "compile_exp_code_labels[simp]"
  (fun () ->
    `!x. get_code_labels (bvi_let_compile_exp x) = get_code_labels x`)
  CHEAT_TAC;;
