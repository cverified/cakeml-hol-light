(* ======================================================== *)
(*  candle_prover_inv: ported from HOL4's
    candle/prover/candle_prover_invScript.sml
    A definition theory, with 8 definitions and 69 theorems.  Needed
    by 7 files of the port.  *)
(* ======================================================== *)

(*
  Definitions of invariants that are to be maintained during
  evaluate of Candle prover
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/candle_kernel_vals.ml";;
needs "candle/prover/perms.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_prover_inv"
  ["ast_extras"; "candle_kernelProg"; "candle_kernel_vals"; "evaluate";
   "evaluateProps"; "holKernelProof"; "misc"; "ml_hol_kernel_funsProg";
   "ml_prog"; "namespaceProps"; "perms"; "semanticPrimitives";
   "semanticPrimitivesProps"];;

let _ = do_list hide_constant ["id"];;


(* -------------------------------------------------------------------------
 * Expressions are safe if they do not construct anything with a name from the
 * kernel type constructors (i.e. one of TYPE, TERM, THM), and if they do not
 * write to the kernel ffi channel.
 *
 * We can't keep track on whether or not the constructors have been brought
 * into scope (i.e., by 'open Kernel;'), so we just forbid their short names
 * everywhere.
 * ------------------------------------------------------------------------- *)

let safe_exp_def = new_definition
  `safe_exp = ast_extras_every_exp (\x.
                match x with
                   ast_Con opt xs -> (!id. opt = SOME id ==> ~(id_to_n id IN
                     kernel_ctors))
                 | ast_App op xs -> ~(op = ast_FFI kernel_ffi)
                 | _ -> T)`;;

(* HOL4 candle_prover_invScript.sml:33-50: a theorem that HOL4 states as the
   value of an ML expression: safe_exp_simps *)

let safe_dec_def = new_definition
  `safe_dec = every_dec (\d.
                match d with
                  Dlet locs pat x -> safe_exp x
                | Dletrec locs funs -> ALL safe_exp (MAP (SND o SND) funs)
                | _ -> T)`;;

(* HOL4 candle_prover_invScript.sml:60-71: a theorem that HOL4 states as the
   value of an ML expression: safe_dec_simps *)

let v_ok = cake_inductive
  `((!ctxt v.
        inferred ctxt v ==>
          kernel_vals ctxt v)) /\
   ((!ctxt f v g.
        kernel_vals ctxt f /\
        candle_prover_inv_v_ok ctxt v /\
        do_partial_app f v = SOME g ==>
          kernel_vals ctxt g)) /\
   ((!ctxt v.
        kernel_vals ctxt v ==>
          candle_prover_inv_v_ok ctxt v)) /\
   ((!ctxt opt vs.
        ALL (candle_prover_inv_v_ok ctxt) vs /\
        (!tag x. opt = SOME (TypeStamp tag x) ==> ~(x IN kernel_types)) ==>
          candle_prover_inv_v_ok ctxt (semanticPrimitives_Conv opt vs))) /\
   ((!ctxt env n x.
        candle_prover_inv_env_ok ctxt env /\
        safe_exp x ==>
          candle_prover_inv_v_ok ctxt (semanticPrimitives_Closure env n x)))
            /\
   ((!ctxt env f n.
        candle_prover_inv_env_ok ctxt env /\
        ALL safe_exp (MAP (SND o SND) f) ==>
          candle_prover_inv_v_ok ctxt (semanticPrimitives_Recclosure env f
            n))) /\
   ((!ctxt vs.
        ALL (candle_prover_inv_v_ok ctxt) vs ==>
          candle_prover_inv_v_ok ctxt (semanticPrimitives_Vectorv vs))) /\
   ((!ctxt lit.
        candle_prover_inv_v_ok ctxt (semanticPrimitives_Litv lit))) /\
   ((!ctxt loc b. ~(loc IN kernel_locs) ==>
          candle_prover_inv_v_ok ctxt (semanticPrimitives_Loc b loc))) /\
   ((!ctxt env ns.
        candle_prover_inv_env_ok ctxt env ==>
          candle_prover_inv_v_ok ctxt (semanticPrimitives_Env env ns))) /\
   ((!ctxt env.
        (!id len tag tn.
           nsLookup (sem_env_c env) id = SOME (len,TypeStamp tag tn) /\
           tn IN kernel_types ==>
             id_to_n id IN kernel_ctors) /\
        (!n v. nsLookup (sem_env_v env) n = SOME v ==>
          candle_prover_inv_v_ok ctxt v) ==>
          candle_prover_inv_env_ok ctxt env))`;;

let kernel_vals_Vectorv = prove
 (`~(kernel_vals ctxt (semanticPrimitives_Vectorv vs))`,
  CHEAT_TAC);;
add_simp kernel_vals_Vectorv;;

let kernel_vals_Env = prove
 (`~(kernel_vals ctxt1 (semanticPrimitives_Env env id))`,
  CHEAT_TAC);;
add_simp kernel_vals_Env;;

let kernel_vals_Conv = prove
 (`kernel_vals ctxt (semanticPrimitives_Conv (SOME stamp) vs) ==>
     (?tag m. stamp = TypeStamp tag m /\ m IN kernel_types)`,
  CHEAT_TAC);;

let kernel_vals_Conv_NONE = prove
 (`~(kernel_vals ctxt (semanticPrimitives_Conv NONE vs))`,
  CHEAT_TAC);;
add_simp kernel_vals_Conv_NONE;;

let kernel_vals_Loc = prove
 (`~(kernel_vals ctxt (semanticPrimitives_Loc b loc))`,
  CHEAT_TAC);;
add_simp kernel_vals_Loc;;

(* HOL4 candle_prover_invScript.sml:162-171: a theorem that HOL4 states as
   the value of an ML expression: v_ok_def *)

let v_ok_div_exn_v = prove
 (`candle_prover_inv_v_ok ctxt semanticPrimitives_div_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_div_exn_v;;

let v_ok_chr_exn_v = prove
 (`candle_prover_inv_v_ok ctxt semanticPrimitives_chr_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_chr_exn_v;;

let v_ok_bind_exn_v = prove
 (`candle_prover_inv_v_ok ctxt semanticPrimitives_bind_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_bind_exn_v;;

let v_ok_sub_exn_v = prove
 (`candle_prover_inv_v_ok ctxt sub_exn_v`,
  CHEAT_TAC);;
add_simp v_ok_sub_exn_v;;

(* HOL4 candle_prover_invScript.sml:199: a theorem that HOL4 states as the
   value of an ML expression: env_ok_def *)

let kernel_vals_ind =
  GEN_ALL (SIMP_RULE [] (CAKE_SPECL [`P`; `\uu0 uu1. T`; `\uu0 uu1. T`]
  (cake_ind v_ok)));;

(* the clauses in two quotations: vs is ('a list) and (word8 list), which one
   quotation cannot typecheck *)
let ref_ok_def = define_cases_clauses
  [`(candle_prover_inv_ref_ok ctxt (semanticPrimitives_Varray vs) = ALL
    (candle_prover_inv_v_ok ctxt) vs) /\
    (candle_prover_inv_ref_ok ctxt (semanticPrimitives_Refv v) =
    candle_prover_inv_v_ok ctxt v) /\
    (candle_prover_inv_ref_ok ctxt (semanticPrimitives_Thunk m v) =
    candle_prover_inv_v_ok ctxt v)`;
   `candle_prover_inv_ref_ok ctxt (semanticPrimitives_W8array vs) = T`];;

let kernel_loc_ok_def = new_definition
  `kernel_loc_ok s loc refs <=>
     (?v. (\l n. oEL n l) refs loc = SOME (semanticPrimitives_Refv v) /\
         (the_type_constants = semanticPrimitives_Loc T loc ==>
            LIST_TYPE (PAIR_TYPE STRING_TYPE NUM)
              (hol_refs_the_type_constants s) v) /\
         (the_term_constants = semanticPrimitives_Loc T loc ==>
            LIST_TYPE (PAIR_TYPE STRING_TYPE TYPE_TYPE)
              (hol_refs_the_term_constants s) v) /\
         (the_axioms = semanticPrimitives_Loc T loc ==>
            LIST_TYPE THM_TYPE (hol_refs_the_axioms s) v) /\
         (the_context = semanticPrimitives_Loc T loc ==>
            LIST_TYPE UPDATE_TYPE (hol_refs_the_context s) v))`;;

let kernel_loc_ok_LENGTH = prove
 (`kernel_loc_ok st loc refs ==>
     loc < LENGTH refs`,
  CHEAT_TAC);;

let kernel_loc_ok_LUPDATE1 = prove
 (`kernel_loc_ok st loc refs /\ ~(n = loc) ==>
     kernel_loc_ok st loc (LUPDATE v n refs)`,
  CHEAT_TAC);;

let eval_state_ok_def = new_definition
  `eval_state_ok x1 =
   match x1 with
     NONE -> T
   | SOME (EvalDecs s) ->
     (!v ds. eval_decs_state_decode_decs s v = SOME ds ==> ALL safe_dec ds)
   | _ -> F`;;

let state_ok_def = new_definition
  `candle_prover_inv_state_ok ctxt s <=>
     (!n. n IN kernel_types ==> n < semanticPrimitives_state_next_type_stamp
       s) /\
     ALL ok_event (ffi_state_io_events (semanticPrimitives_state_ffi s)) /\
     eval_state_ok (semanticPrimitives_state_eval_state s) /\
     (?state.
       STATE ctxt state /\
       (!loc. loc IN kernel_locs ==> kernel_loc_ok state loc
         (semanticPrimitives_state_refs s)) /\
       (!loc r. ~(loc IN kernel_locs) /\ (\l n. oEL n l)
         (semanticPrimitives_state_refs s) loc = SOME r ==>
         candle_prover_inv_ref_ok ctxt r))`;;

let state_ok_dec_clock = prove
 (`candle_prover_inv_state_ok ctxt (evaluate_dec_clock s) =
  candle_prover_inv_state_ok ctxt s`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * Proving env_ok/v_ok/ref_ok/state_ok for things
 * ------------------------------------------------------------------------- *)

let env_ok_extend_dec_env = prove
 (`candle_prover_inv_env_ok ctxt env1 /\
   candle_prover_inv_env_ok ctxt env2 ==>
     candle_prover_inv_env_ok ctxt (extend_dec_env env1 env2)`,
  CHEAT_TAC);;

let env_ok_write_cons = prove
 (`candle_prover_inv_env_ok ctxt env /\
   (t IN kernel_types ==> nm IN kernel_ctors) ==>
     candle_prover_inv_env_ok ctxt (write_cons nm (n,TypeStamp s t) env)`,
  CHEAT_TAC);;

let env_ok_write_Exn = prove
 (`candle_prover_inv_env_ok ctxt env ==>
   candle_prover_inv_env_ok ctxt (write_cons nm (n,ExnStamp m) env)`,
  CHEAT_TAC);;

let env_ok_write_mod = prove
 (`candle_prover_inv_env_ok ctxt env1 /\
   candle_prover_inv_env_ok ctxt env2 ==>
     candle_prover_inv_env_ok ctxt (write_mod mn env1 env2)`,
  CHEAT_TAC);;

let env_ok_write = prove
 (`candle_prover_inv_env_ok ctxt env /\
   candle_prover_inv_v_ok ctxt v ==>
     candle_prover_inv_env_ok ctxt (ml_prog_write nm v env)`,
  CHEAT_TAC);;

let env_ok_merge_env = prove
 (`candle_prover_inv_env_ok ctxt env1 /\
   candle_prover_inv_env_ok ctxt env2 ==>
     candle_prover_inv_env_ok ctxt (merge_env env1 env2)`,
  CHEAT_TAC);;

let env_ok_with = prove
 (`candle_prover_inv_env_ok ctxt (sem_env_c_fupd (K (sem_env_c env)) env1) ==>
     candle_prover_inv_env_ok ctxt (sem_env_v_fupd (K (sem_env_v env1))
       env)`,
  CHEAT_TAC);;

let env_ok_with_nsBind = prove
 (`candle_prover_inv_v_ok ctxt v /\
   candle_prover_inv_env_ok ctxt (sem_env_c_fupd (K (sem_env_c env)) env2)
     ==>
     candle_prover_inv_env_ok ctxt (sem_env_v_fupd (K (nsBind n v
       (sem_env_v env2))) env)`,
  CHEAT_TAC);;

let env_ok_nsEmpty = prove
 (`candle_prover_inv_env_ok ctxt (mk_sem_env nsEmpty nsEmpty)`,
  CHEAT_TAC);;

let env_ok_empty_env = prove
 (`candle_prover_inv_env_ok ctxt ml_prog_empty_env`,
  CHEAT_TAC);;

let env_ok_init_env = prove
 (`candle_prover_inv_env_ok ctxt init_env`,
  CHEAT_TAC);;

let v_ok_Cons = prove
 (`candle_prover_inv_v_ok ctxt (semanticPrimitives_Conv (SOME (TypeStamp
  (implode "::") 1)) [x; y]) <=> candle_prover_inv_v_ok ctxt x
  /\ candle_prover_inv_v_ok ctxt y`,
  CHEAT_TAC);;

let v_ok_Conv_NONE = prove
 (`candle_prover_inv_v_ok ctxt (semanticPrimitives_Conv NONE ls) =
   ALL (candle_prover_inv_v_ok ctxt) ls`,
  CHEAT_TAC);;

let NUM_v_ok = prove
 (`NUM x v ==> candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let BOOL_v_ok = prove
 (`BOOL x v ==> candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let STRING_TYPE_v_ok = prove
 (`STRING_TYPE x v ==> candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let PAIR_TYPE_v_ok = prove
 (`PAIR_TYPE A B p v /\
   (!v. A (FST p) v ==> candle_prover_inv_v_ok ctxt v) /\
   (!v. B (SND p) v ==> candle_prover_inv_v_ok ctxt v) ==>
   candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let LIST_TYPE_v_ok = prove
 (`!A ls v.
          LIST_TYPE A ls v /\ ALL (\x. !v. A x v ==>
            candle_prover_inv_v_ok ctxt v) ls ==> candle_prover_inv_v_ok ctxt
            v`,
  CHEAT_TAC);;


(* -------------------------------------------------------------------------
 * Lemmas about v_ok and {TYPE,TERM,THM}_TYPE{,_HEAD}
 * ------------------------------------------------------------------------- *)

let TYPE_IMP_v_ok = prove
 (`TYPE ctxt th /\ TYPE_TYPE th v ==> candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let TERM_IMP_v_ok = prove
 (`TERM ctxt th /\ TERM_TYPE th v ==> candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let THM_IMP_v_ok = prove
 (`THM ctxt th /\ THM_TYPE th v ==> candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let v_ok_THM_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   THM_TYPE_HEAD v ==>
     (?th. THM_TYPE th v)`,
  CHEAT_TAC);;

let v_ok_TERM_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   TERM_TYPE_HEAD v ==>
     (?tm. TERM_TYPE tm v)`,
  CHEAT_TAC);;

let v_ok_TYPE_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   TYPE_TYPE_HEAD v ==>
     (?ty. TYPE_TYPE ty v)`,
  CHEAT_TAC);;

let v_ok_LIST_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   (!v. candle_prover_inv_v_ok ctxt v /\ A_HEAD v ==> (?a. A a v)) /\
   LIST_TYPE_HEAD A_HEAD v ==>
     (?tms. LIST_TYPE A tms v)`,
  CHEAT_TAC);;

let v_ok_LIST_TERM_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   LIST_TYPE_HEAD TERM_TYPE_HEAD v ==>
     (?tms. LIST_TYPE TERM_TYPE tms v)`,
  CHEAT_TAC);;

let v_ok_LIST_THM_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   LIST_TYPE_HEAD THM_TYPE_HEAD v ==>
     (?ths. LIST_TYPE THM_TYPE ths v)`,
  CHEAT_TAC);;

let v_ok_PAIR_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   (!v. candle_prover_inv_v_ok ctxt v /\ A_HEAD v ==> (?a. A a v)) /\
   (!v. candle_prover_inv_v_ok ctxt v /\ B_HEAD v ==> (?b. B b v)) /\
   PAIR_TYPE_HEAD A_HEAD B_HEAD v ==>
     (?p. PAIR_TYPE A B p v)`,
  CHEAT_TAC);;

let v_ok_LIST_PAIR_TYPE_HEAD = prove
 (`candle_prover_inv_v_ok ctxt v /\
   (!v. candle_prover_inv_v_ok ctxt v /\ A_HEAD v ==> (?a. A a v)) /\
   (!v. candle_prover_inv_v_ok ctxt v /\ B_HEAD v ==> (?b. B b v)) /\
   LIST_TYPE_HEAD (PAIR_TYPE_HEAD A_HEAD B_HEAD) v ==>
   (?ls. LIST_TYPE (PAIR_TYPE A B) ls v)`,
  CHEAT_TAC);;

let v_ok_TYPE = prove
 (`candle_prover_inv_v_ok ctxt v /\
   TYPE_TYPE ty v ==>
     TYPE ctxt ty`,
  CHEAT_TAC);;

let v_ok_TERM = prove
 (`candle_prover_inv_v_ok ctxt v /\
   TERM_TYPE tm v ==>
     TERM ctxt tm`,
  CHEAT_TAC);;

let v_ok_THM = prove
 (`candle_prover_inv_v_ok ctxt v /\
   THM_TYPE th v ==>
     THM ctxt th`,
  CHEAT_TAC);;

let v_ok_LIST = prove
 (`(!x v. A_TYPE x v /\ candle_prover_inv_v_ok ctxt v ==> A ctxt x) ==>
   (!ls v.
     LIST_TYPE A_TYPE ls v /\ candle_prover_inv_v_ok ctxt v ==> ALL (A
       ctxt) ls)`,
  CHEAT_TAC);;

let v_ok_LIST_TERM = prove
 (`!tms v ctxt. LIST_TYPE TERM_TYPE tms v /\ candle_prover_inv_v_ok ctxt v
  ==> ALL (TERM ctxt) tms`,
  CHEAT_TAC);;

let v_ok_LIST_THM = prove
 (`!ths v ctxt. LIST_TYPE THM_TYPE ths v /\ candle_prover_inv_v_ok ctxt v ==>
  ALL (THM ctxt) ths`,
  CHEAT_TAC);;

let v_ok_LIST_TYPE = prove
 (`!tms v ctxt. LIST_TYPE TYPE_TYPE tms v /\ candle_prover_inv_v_ok ctxt v
  ==> ALL (TYPE ctxt) tms`,
  CHEAT_TAC);;

let v_ok_PAIR = prove
 (`(!x v. A_TYPE x v /\ candle_prover_inv_v_ok ctxt v ==> A ctxt x) /\
   (!x v. B_TYPE x v /\ candle_prover_inv_v_ok ctxt v ==> B ctxt x) /\
   PAIR_TYPE A_TYPE B_TYPE x v /\ candle_prover_inv_v_ok ctxt v ==>
     (\ctxt p. A ctxt (FST p) /\ B ctxt (SND p)) ctxt x`,
  CHEAT_TAC);;

let LIST_TYPE_perms_ok = prove
 (`!xs xsv.
     (!x v. A x v /\ MEM x xs ==> perms_ok ps v) /\
     LIST_TYPE A xs xsv ==>
       perms_ok ps xsv`,
  CHEAT_TAC);;

let PAIR_TYPE_perms_ok = prove
 (`(!x v. A x v ==> perms_ok ps v) /\
   (!x v. B x v ==> perms_ok ps v) /\
   PAIR_TYPE A B x v ==>
     perms_ok ps v`,
  CHEAT_TAC);;

let UNIT_TYPE_perms_ok = prove
 (`!u v. UNIT_TYPE u v ==> perms_ok ps v`,
  CHEAT_TAC);;

let INT_perms_ok = prove
 (`!s v. INT s v ==> perms_ok ps v`,
  CHEAT_TAC);;

let NUM_perms_ok = prove
 (`!s v. NUM s v ==> perms_ok ps v`,
  CHEAT_TAC);;

let STRING_TYPE_perms_ok = prove
 (`!s v. STRING_TYPE s v ==> perms_ok ps v`,
  CHEAT_TAC);;

let TYPE_TYPE_perms_ok = prove
 (`!ty v. TYPE_TYPE ty v ==> perms_ok ps v`,
  CHEAT_TAC);;

let TERM_TYPE_perms_ok = prove
 (`!tm v. TERM_TYPE tm v ==> perms_ok ps v`,
  CHEAT_TAC);;

let THM_TYPE_perms_ok = prove
 (`!th v. THM_TYPE th v ==> perms_ok ps v`,
  CHEAT_TAC);;

let LIST_TERM_TYPE_perms_ok = prove
 (`!tm v. LIST_TYPE TERM_TYPE tm v ==> perms_ok ps v`,
  CHEAT_TAC);;

let LIST_TYPE_TYPE_perms_ok = prove
 (`!tm v. LIST_TYPE TYPE_TYPE tm v ==> perms_ok ps v`,
  CHEAT_TAC);;

let LIST_TYPE_THM_perms_ok = prove
 (`!tm v. LIST_TYPE THM_TYPE th v ==> perms_ok ps v`,
  CHEAT_TAC);;

let UPDATE_TYPE_perms_ok = prove
 (`!u v. UPDATE_TYPE u v ==> perms_ok ps v`,
  CHEAT_TAC);;

let sub_conv = cake_inductive
  `(MEM v vs ==> sub_conv v (semanticPrimitives_Conv cn vs))`;;

let sub_conv_ok = prove
 (`!v w. sub_conv v w ==> candle_prover_inv_v_ok ctxt w ==>
  candle_prover_inv_v_ok ctxt v`,
  CHEAT_TAC);;

let v_ok_Conv_alt = prove
 (`candle_prover_inv_v_ok ctxt (semanticPrimitives_Conv (SOME stamp) vs) ==>
     ALL (candle_prover_inv_v_ok ctxt) vs`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id"];;

(* and the interface *)
let _ = unhide_overloads ();;
