(* ======================================================== *)
(*  clos_mtiProof: ported from HOL4's
    compiler/backend/proofs/clos_mtiProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for the clos_mti compiler pass. The theorem is
  proved using a backwards simulation, i.e. against the direction of
  compilation.
*)

needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* HOL4 ML code, not ported:
val _ = bring_fwd_ctors "closLang" ``:closLang$exp``
*)

(* code relation *)

let code_rel_def = cake_define
  `clos_mtiProof_code_rel max_app e1 e2 <=>
     EVERY no_mti e1 /\ (e2 = intro_multi max_app e1)`;;
hol4_overload "code_rel" "clos_mtiProof_code_rel";;

(* value relation *)

let mk_Fns_def = cake_define_list
  [`mk_Fns [] e = e`;
   `mk_Fns (t :: ts) e = closLang_Fn t NONE NONE 1 (mk_Fns ts e)`];;

let f_rel_def = cake_define
  `clos_mtiProof_f_rel max_app (a1,e1) (a2,e2) <=>
     (?b1 ts.
       clos_mtiProof_code_rel max_app [b1] [e2] /\ a2 <= max_app /\
         no_mti b1 /\
       a1 = 1 /\ e1 = mk_Fns ts b1 /\ a2 = LENGTH ts + 1)`;;
hol4_overload "f_rel" "clos_mtiProof_f_rel";;

let v_rel = cake_inductive
  `(!i. clos_mtiProof_v_rel (max_app:num) (closSem_Number i)
  (closSem_Number i)) /\
   (!w. clos_mtiProof_v_rel max_app (Word64 w) (Word64 w)) /\
   (!w. clos_mtiProof_v_rel max_app (closSem_ByteVector w)
     (closSem_ByteVector w)) /\
   (!n b. clos_mtiProof_v_rel max_app (closSem_RefPtr b n)
     (closSem_RefPtr b n)) /\
   (!tag xs ys.
      LIST_REL (clos_mtiProof_v_rel max_app) xs ys ==>
      clos_mtiProof_v_rel max_app (closSem_Block tag xs)
        (closSem_Block tag ys)) /\
   (!args1 args2 env1 env2 arg_count e1 ts e2.
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      LIST_REL (clos_mtiProof_v_rel max_app) env1 env2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) args1 args2 ==>
      clos_mtiProof_v_rel max_app
        (Closure NONE [] (args1 ++ env1) 1 (mk_Fns ts e1))
        (Closure NONE args2 env2 arg_count e2)) /\
   (!env1 funs1 env2 funs2 n.
      LIST_REL (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) env1 env2 /\
      n < LENGTH funs2 ==>
      clos_mtiProof_v_rel max_app
        (Recclosure NONE [] env1 funs1 n)
        (Recclosure NONE [] env2 funs2 n)) /\
   (!args1 env1 funs1 args2 env2 funs2 n recc ts e1 e2 arg_count.
      LIST_REL (clos_mtiProof_f_rel max_app) funs1 funs2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) env1 env2 /\
      LIST_REL (clos_mtiProof_v_rel max_app) args1 args2 /\ ~(args2 =
        []) /\
      n < LENGTH funs2 /\ EL n funs2 = (arg_count,e2) /\
      1 + LENGTH ts + LENGTH args1 = arg_count /\
      clos_mtiProof_code_rel max_app [e1] [e2] /\
      LIST_REL (clos_mtiProof_v_rel max_app) recc
           (GENLIST (Recclosure NONE [] env2 funs2) (LENGTH funs2))
             ==>
      clos_mtiProof_v_rel max_app
        (Closure NONE [] (args1 ++ recc ++ env1) 1 (mk_Fns ts e1))
        (Recclosure NONE args2 env2 funs2 n))`;;
hol4_overload "v_rel" "clos_mtiProof_v_rel";;

let v_rel_opt_def = cake_define
  `v_rel_opt max_app x2 x3 =
        match (x2,x3) with
          (NONE,NONE) -> T
        | ((SOME x),(SOME y)) -> clos_mtiProof_v_rel max_app x y
        | (_1,_2) -> F`;;

let ref_rel = cake_inductive
  `(!bs. clos_mtiProof_ref_rel max_app (closSem_ByteArray bs)
  (closSem_ByteArray bs)) /\
   (!xs ys.
     LIST_REL (clos_mtiProof_v_rel max_app) xs ys ==>
     clos_mtiProof_ref_rel max_app (closSem_ValueArray xs)
       (closSem_ValueArray ys)) /\
   (!m v w.
     clos_mtiProof_v_rel max_app v w ==>
     clos_mtiProof_ref_rel max_app (Thunk m v) (Thunk m w))`;;
hol4_overload "ref_rel" "clos_mtiProof_ref_rel";;

let FMAP_REL_def = cake_define
  `clos_mtiProof_FMAP_REL r f1 f2 <=>
     FDOM f1 = FDOM f2 /\
     (!k v. FLOOKUP f1 k = SOME v ==>
           (?v2. FLOOKUP f2 k = SOME v2 /\ r v v2))`;;
hol4_overload "FMAP_REL" "clos_mtiProof_FMAP_REL";;

(* state relation *)

let state_rel_def = cake_define
  `clos_mtiProof_state_rel (s:('c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (!n. SND (SND (closSem_state_compile_oracle s n)) = [] /\
          EVERY no_mti (FST (SND (closSem_state_compile_oracle s
            n)))) /\ closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY /\
       closSem_state_max_app
     t = closSem_state_max_app s /\ 1 <= closSem_state_max_app s /\
       state_clock
     t = state_clock s /\ state_ffi
     t = state_ffi s /\
     LIST_REL (v_rel_opt (closSem_state_max_app s))
       (closSem_state_globals s) (closSem_state_globals t) /\
     clos_mtiProof_FMAP_REL (ref_rel (closSem_state_max_app s))
       (state_refs s) (state_refs t) /\ closSem_state_compile
     s = pure_cc (clos_mti_compile_inc (closSem_state_max_app s))
       (closSem_state_compile t) /\ closSem_state_compile_oracle
     t = pure_co (clos_mti_compile_inc (closSem_state_max_app s))
       o closSem_state_compile_oracle s`;;
hol4_overload "state_rel" "clos_mtiProof_state_rel";;

(* evaluation theorem *)

let mk_Apps_def = cake_define_list
  [`mk_Apps e [] = e`;
   `mk_Apps e ((t,other) :: ts) = App t NONE (mk_Apps e ts) [other]`];;

let evaluate_apps_def = cake_define_list
  [`evaluate_apps f [] s = (Rval [f],s)`;
   `evaluate_apps f (x :: xs) s =
      (match evaluate_apps f xs s with (Rval [v],s1) ->
        evaluate_app NONE v [x] s1 | res -> res)`];;

(* HOL4 ML code, not ported:
val do_app_inst =
  simple_val_rel_do_app_rev
  |> Q.INST [`vr`|->`v_rel s.max_app`]
  |> INST_TYPE [``:'a``|->``:'c``]
  |> Q.INST [`sr`|->`\r t. (r.max_app = s.max_app) /\ state_rel r t`]
  |> SIMP_RULE std_ss [simple_val_rel, simple_state_rel]
*)

(* HOL4 ML code, not ported:
val do_install_inst =
  simple_val_rel_do_install
  |> Q.INST [`vr`|->`v_rel s.max_app`]
  |> Q.INST [`sr`|->`\r t. (r.max_app = s.max_app) /\ state_rel r t`,
        `cr`|->`code_rel s.max_app`]
  |> SIMP_RULE bool_ss [simple_val_rel, simple_state_rel]
  |> Q.SPEC `clos_mti$compile_inc s.max_app`
*)

(* syntax well-formedness *)

(* HOL4 ML code, not ported:
val intro1_pat = ``intro_multi max_app [e]``
fun intro_sing th =
  case gen_find_term
         (fn (bvs,t) => if can (match_term intro1_pat) t andalso
                           null (op_intersect aconv bvs (free_vars t))
                        then SOME t
                        else NONE)
                     (concl th)
   of
      SOME t => strip_assume_tac
                  (PART_MATCH (lhs o #2 o dest_exists)
                              clos_mtiTheory.intro_multi_sing t)
    | NONE => NO_TAC
*)

(* preservation of observable semantics *)
