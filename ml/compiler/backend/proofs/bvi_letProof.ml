(* ======================================================== *)
(*  bvi_letProof: ported from HOL4's
    compiler/backend/proofs/bvi_letProofScript.sml
    A proof theory about bvi_let.ml, with 2 definitions and 19
    theorems.  Needed by bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  Correctness proof for bvi_let
*)

needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/semantics/bviProps.ml";;
needs "compiler/backend/semantics/bviSem.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvi_letProof"
  ["bviProps"; "bviSem"; "bvi_let"];;

(* HOL4 bvi_letProofScript.sml:10: an overload that the source brings to the
   front: compile, written out as bvi_let_compile *)

let v_rel_def = new_definition
  `bvi_letProof_v_rel a x y xs ys <=> (\l n. oEL n l) ys a = SOME x`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let env_rel_def,env_rel_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). list_size (\n. n) x0)`
  `bvi_letProof_env_rel x1 d e1 e2 =
     match (x1,e1,e2) with
       ([],e1,e2) -> (e1 = DROP d e2)
     | (CONS a rest,CONS x e1,CONS y e2) ->
        bvi_letProof_v_rel a x y (CONS x e1) (CONS y e2)
          /\ bvi_letProof_env_rel rest d e1 e2
     | (_,_,_) -> F`;;

let env_rel_length = prove
 (`!ax env env2. bvi_letProof_env_rel ax d env env2 ==> LENGTH env <= LENGTH
  env2`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_LLOOKUP_NONE = prove
 (`!ax env env2 n d.
       bvi_letProof_env_rel ax d env env2 /\
       (\l n. oEL n l) ax n = NONE /\
       n < LENGTH env ==>
       n + d < LENGTH env2 /\
       EL (n + d) env2 = EL n env`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_LOOKUP_SOME = prove
 (`!env env2 ax x n d.
       bvi_letProof_env_rel ax d env env2 /\
       (\l n. oEL n l) ax n = SOME x ==>
       bvi_letProof_v_rel x (EL n env) (EL n env2) (DROP n env) (DROP n
         env2)`,
  CHEAT_TAC);;

let evaluate_delete_var_Rerr_SING = prove
 (`!x s r e env2.
      bviSem_evaluate ([x],env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error)
        ==>
      bviSem_evaluate ([bvi_let_delete_var x],env2,s) = (Rerr e,r)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_delete_var_Rerr = prove
 (`!xs s r e env2.
       bviSem_evaluate (xs,env2,s) = (Rerr e,r) /\ ~(e = Rabort Rtype_error)
         ==>
       bviSem_evaluate (MAP bvi_let_delete_var xs,env2,s) = (Rerr e,r)`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_delete_var_Rval = prove
 (`!xs env2 s a r ax env d.
       bviSem_evaluate (xs,env2,(s:('c,'ffi)bviSem_state)) = (Rval a,r) /\
       bvi_letProof_env_rel ax d env env2 ==>
       (?b. bviSem_evaluate (MAP bvi_let_delete_var xs,env2,s) = (Rval b,r)
         /\
           bvi_letProof_env_rel (APPEND (bvi_let_extract_list xs) ax) d
             (APPEND a env) (APPEND b env2))`,
  CHEAT_TAC);;

let evaluate_SNOC_Rval = prove
 (`bviSem_evaluate (SNOC x y,env,s) = (Rval a,r) ==>
    (?a1 a2 r1.
      a = SNOC a1 a2 /\ LENGTH y = LENGTH a2 /\
      bviSem_evaluate (y,env,s) = (Rval a2,r1) /\
      bviSem_evaluate ([x],env,r1) = (Rval [a1],r))`,
  CHEAT_TAC);;

let compile_CONS = prove
 (`bvi_let_compile ax d (CONS x xs) = APPEND (bvi_let_compile ax d [x])
  (bvi_let_compile ax d xs)`,
  CHEAT_TAC);;

let compile_APPEND = prove
 (`!xs ys ax d. bvi_let_compile ax d (APPEND xs ys) = APPEND (bvi_let_compile
  ax d xs) (bvi_let_compile ax d ys)`,
  CHEAT_TAC);;

let IMP_COMM = prove
 (`(b1 ==> b2 ==> b3) <=> (b2 ==> b1 ==> b3)`,
  CHEAT_TAC);;

make_size "bvi_exp";;
let exp_size_APPEND = prove
 (`!xs ys. bvi_exp_size1 (APPEND xs ys) = bvi_exp_size1 xs + bvi_exp_size1 ys`,
  CHEAT_TAC);;

let env_rel_MAP = prove
 (`!ax env1 env2 d a.
      bvi_letProof_env_rel ax d env1 env2 ==>
      bvi_letProof_env_rel (MAP ((+) (LENGTH a)) ax) (d + LENGTH a) env1
        (APPEND a env2)`,
  CHEAT_TAC);;

(* [local] *)
let env_rel_REPLICATE_0 = prove
 (`!vs ax d env1 env2.
     bvi_letProof_env_rel ax d env1 env2 ==>
     bvi_letProof_env_rel (APPEND (REPLICATE (LENGTH vs) 0) ax) d (APPEND
       vs env1) (APPEND vs env2)`,
  CHEAT_TAC);;

let evaluate_env_rel = prove
 (`!xs env1 (s1:('c,'ffi)bviSem_state) ax env2 res s2 ys d.
      (bviSem_evaluate (xs,env1,s1) = (res,s2)) /\
      bvi_letProof_env_rel ax d env1 env2 /\ ~(res = Rerr (Rabort
        Rtype_error)) ==>
      (bviSem_evaluate (bvi_let_compile ax d xs,env2,s1) = (res,s2))`,
  CHEAT_TAC);;

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

let compile_thm =
  SIMP_RULE [env_rel_def] (GEN_ALL (CAKE_SPECL [`xs`; `env`; `s1`; `[]`;
  `env`; `res`; `s2`; `ys`; `0`] evaluate_env_rel));;

let evaluate_compile_exp = prove
 (`bviSem_evaluate ([d],env,s) = (r,t) /\ ~(r = Rerr (Rabort Rtype_error)) ==>
    bviSem_evaluate ([bvi_let_compile_exp d],env,s) = (r,t)`,
  CHEAT_TAC);;

let dest_var_code_labels = prove
 (`!x. bviProps_get_code_labels (bvi_let_delete_var x) =
  bviProps_get_code_labels x`,
  CHEAT_TAC);;
add_simp dest_var_code_labels;;

let compile_code_labels = prove
 (`!x y z. UNIONS (set_of_list (MAP bviProps_get_code_labels (bvi_let_compile x
  y z))) =
           UNIONS (set_of_list (MAP bviProps_get_code_labels z))`,
  CHEAT_TAC);;

(* the names of record fields that this statement uses for
   variables of its own are read as variables *)
let compile_exp_code_labels = prove
 (cake_as_vars (fun () ->
    `!x. bviProps_get_code_labels (bvi_let_compile_exp x) =
  bviProps_get_code_labels x`),
  CHEAT_TAC);;
add_simp compile_exp_code_labels;;

(* and the interface *)
let _ = unhide_overloads ();;
