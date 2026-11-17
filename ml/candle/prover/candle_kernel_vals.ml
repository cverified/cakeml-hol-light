(* ======================================================== *)
(*  candle_kernel_vals: ported from HOL4's
    candle/prover/candle_kernel_valsScript.sml
    A definition theory, with 17 definitions and 103 theorems.
    Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  Theorems about values from the Candle kernel program
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/ast_extras.ml";;
needs "candle/prover/candle_kernelProg.ml";;
needs "candle/prover/perms.ml";;
needs "candle/standard/ml_kernel/ml_hol_kernel_funsProg.ml";;
needs "candle/standard/ml_kernel/runtime_check.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "candle/standard/monadic/holKernelProof.ml";;
needs "candle/standard/syntax/holSyntax.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "candle_kernel_vals"
  ["ast_extras"; "candle_kernelProg"; "evaluate"; "evaluateProps";
   "holKernelProof"; "ml_hol_kernel_funsProg"; "ml_translator";
   "namespaceProps"; "perms"; "semanticPrimitives";
   "semanticPrimitivesProps"];;

let _ = do_list hide_constant ["id"];;


(* HOL4 candle_kernel_valsScript.sml:13: ML code, not ported *)

(* -------------------------------------------------------------------------
 * 'inferred' relation
 * ------------------------------------------------------------------------- *)

let kernel_funs_def = new_definition
  `kernel_funs = {
     // this list attempts to match the functions given in:
     // https://github.com/jrh13/hol-light/blob/master/fusion.ml
     types_v,
     get_type_arity_v,
     call_new_type_v,
     mk_type_v,
     mk_vartype_v,
     dest_type_v,
     dest_vartype_v,
     is_type_v,
     is_vartype_v,
     call_tyvars_v,
     call_type_subst_v,
     constants_v,
     get_const_type_v,
     new_constant_v,
     call_type_of_v,
     is_var_v,
     is_const_v,
     is_abs_v,
     is_comb_v,
     mk_var_v,
     mk_const_v,
     mk_abs_v,
     mk_comb_v,
     dest_var_v,
     dest_const_v,
     dest_comb_v,
     dest_abs_v,
     call_frees_v,
     freesl_v,
     call_freesin_v,
     call_vfree_in_v,
     call_type_vars_in_term_v,
     call_variant_v,
     vsubst_v,
     inst_v,
     rand_v,
     rator_v,
     dest_eq_v,
     dest_thm_v,
     hyp_v,
     concl_v,
     refl_v,
     trans_v,
     mk_comb_1_v,
     abs_1_v,
     beta_v,
     assume_v,
     eq_mp_v,
     deduct_antisym_rule_v,
     inst_type_v,
     inst_1_v,
     axioms_v,
     new_axiom_v,
     new_basic_definition_v,
     new_basic_type_definition_v,
     new_specification_v,
     Kernel_print_thm_v,
     // Compute additions
     compute_add_v,
     compute_v}`;;

(* HOL4 candle_kernel_valsScript.sml:92-101: a theorem that HOL4 states as
   the value of an ML expression: kernel_funs_v_def *)

(* HOL4 candle_kernel_valsScript.sml:103: a theorem that HOL4 states as the
   value of an ML expression: abs_v_def *)

let kernel_locs_def = new_definition
  `kernel_locs =
     {l | semanticPrimitives_Loc T l IN
       {the_type_constants,the_term_constants,the_axioms,the_context}}`;;

let IN_kernel_locs = prove
 (`n IN kernel_locs <=>
   semanticPrimitives_Loc T n = the_type_constants \/
   semanticPrimitives_Loc T n = the_term_constants \/
   semanticPrimitives_Loc T n = the_axioms \/
   semanticPrimitives_Loc T n = the_context`,
  CHEAT_TAC);;

(* HOL4 candle_kernel_valsScript.sml:123-125: ML code, not ported *)

(* HOL4 candle_kernel_valsScript.sml:127: a theorem that HOL4 states as the
   value of an ML expression: refs_defs *)

(* HOL4 candle_kernel_valsScript.sml:129-134: a theorem that HOL4 states as
   the value of an ML expression: kernel_locs *)

let kernel_perms_def = new_definition
  `kernel_perms = IMAGE RefMention kernel_locs UNION {RefUpdate}`;;

(* HOL4 candle_kernel_valsScript.sml:140-143: ML code, not ported *)

(* HOL4 candle_kernel_valsScript.sml:145: the overload type_ctors_set, which
   the port expands *)
(* HOL4 candle_kernel_valsScript.sml:146: the overload term_ctors_set, which
   the port expands *)
(* HOL4 candle_kernel_valsScript.sml:147: the overload thm_ctors_set, which
   the port expands *)

let kernel_ctors_def = new_definition
  `kernel_ctors = type_ctors_set UNION
                  term_ctors_set UNION
                  thm_ctors_set`;;

(* HOL4 candle_kernel_valsScript.sml:155-156: ML code, not ported *)

(* HOL4 candle_kernel_valsScript.sml:158: the overload type_stamp_n, which
   the port expands *)
(* HOL4 candle_kernel_valsScript.sml:159: the overload term_stamp_n, which
   the port expands *)
(* HOL4 candle_kernel_valsScript.sml:160: the overload thm_stamp_n, which
   the port expands *)

let kernel_types_def = new_definition
  `kernel_types = ({type_stamp_n,term_stamp_n,thm_stamp_n}:num->bool)`;;

let inferred = cake_inductive
  `((!ctxt f.
        f IN kernel_funs ==>
          inferred ctxt f)) /\
   ((!ctxt ty v.
        TYPE ctxt ty /\
        TYPE_TYPE ty v ==>
          inferred ctxt v)) /\
   ((!ctxt tm v.
        TERM ctxt tm /\
        TERM_TYPE tm v ==>
          inferred ctxt v)) /\
   ((!ctxt th v.
        THM ctxt th /\
        THM_TYPE th v ==>
          inferred ctxt v))`;;

let kernel_ffi_def,kernel_ffi_ind = define_guess
  `kernel_ffi = (implode "kernel_ffi")`;;

let thm2bytes_def = new_definition
  `thm2bytes ctxt th =
     MAP (n2w:num->word8) (MAP ORD (explode (thm_to_string ctxt th)))`;;

(* the bytes written on the kernel channel can be read back: the context the
   theorem was proved in is recoverable from the event alone *)

let bytes2str_def = new_definition
  `bytes2str (out:word8 list) = implode (MAP (CHR o w2n) out)`;;

let bytes2str_thm2bytes = prove
 (`bytes2str (thm2bytes ctxt th) = thm_to_string ctxt th`,
  CHEAT_TAC);;

let ok_event_def = new_definition
  `ok_event (IO_event n out y) <=>
     n = ffi_ExtCall kernel_ffi ==>
       (?ctxt th. THM ctxt th /\
                 thm2bytes ctxt th = out /\ extends ctxt init_ctxt)`;;

(* -------------------------------------------------------------------------
 * Versions of TERM, THM that only match the outermost structure
 * ------------------------------------------------------------------------- *)

let TYPE_TYPE_HEAD_def = new_definition
  `TYPE_TYPE_HEAD v <=>
     (?s vs. v = semanticPrimitives_Conv (SOME (TypeStamp s type_stamp_n))
       vs /\
            s IN type_ctors_set)`;;

let TERM_TYPE_HEAD_def = new_definition
  `TERM_TYPE_HEAD v <=>
     (?s vs. v = semanticPrimitives_Conv (SOME (TypeStamp s term_stamp_n))
       vs /\
            s IN term_ctors_set)`;;

let THM_TYPE_HEAD_def = new_definition
  `THM_TYPE_HEAD v <=>
     (?s vs. v = semanticPrimitives_Conv (SOME (TypeStamp s thm_stamp_n)) vs
       /\
            s IN thm_ctors_set)`;;

(* [allow_rebind] *)
let candle_kernel_vals_THM_TYPE_HEAD_def = SIMP_RULE [] THM_TYPE_HEAD_def;;

let LIST_TYPE_HEAD_def = new_definition
  `LIST_TYPE_HEAD h v = (?(l:1 list). LIST_TYPE (K h) l v)`;;

let PAIR_TYPE_HEAD_def = new_definition
  `PAIR_TYPE_HEAD h1 h2 v = PAIR_TYPE (K h1) (K h2) (one,one) v`;;

(* HOL4 candle_kernel_valsScript.sml:250-252: the definition *)

(* HOL4 candle_kernel_valsScript.sml:254-256: the definition *)

(* -------------------------------------------------------------------------
 * THM, TERM, TYPE lemmas
 * ------------------------------------------------------------------------- *)

let kernel_funs_inferred = prove
 (`(!ty. v IN kernel_funs ==> ~(TYPE_TYPE ty v)) /\
   (!tm. v IN kernel_funs ==> ~(TERM_TYPE tm v)) /\
   (!th. v IN kernel_funs ==> ~(THM_TYPE th v))`,
  CHEAT_TAC);;
add_simp kernel_funs_inferred;;

let TYPE_from_TYPE_TYPE = prove
 (`inferred ctxt v /\
   TYPE_TYPE ty v ==>
     TYPE ctxt ty`,
  CHEAT_TAC);;

let TERM_from_TERM_TYPE = prove
 (`inferred ctxt v /\
   TERM_TYPE tm v ==>
     TERM ctxt tm`,
  CHEAT_TAC);;

let THM_from_THM_TYPE = prove
 (`inferred ctxt v /\
   THM_TYPE th v ==>
     THM ctxt th`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * Theorems applying kernel functions to *any* arguments (incl. wrong type)
 * ------------------------------------------------------------------------- *)

(* HOL4 candle_kernel_valsScript.sml:331: the ML values that the definitions
   below antiquote *)

(* HOL4 candle_kernel_valsScript.sml:333-339: the ML values that the
   definitions below antiquote *)

let do_opapp_clos = prove
 (`semanticPrimitives_do_opapp [semanticPrimitives_Closure env v e; argv] =
  SOME (env1,e1) <=> sem_env_v_fupd (K (nsBind v argv (sem_env_v env)))
   env = env1 /\ e = e1`,
  CHEAT_TAC);;

let do_partial_app_clos = prove
 (`do_partial_app (semanticPrimitives_Closure env v (ast_Fun n e)) argv = SOME
  g <=>
   semanticPrimitives_Closure (sem_env_v_fupd (K (nsBind v argv (sem_env_v
     env))) env) n e = g`,
  CHEAT_TAC);;

(* [local] *)
let same_clock_exists = prove
 (`(?k. s = semanticPrimitives_state_clock_fupd (K k) s) = T /\
   (?k. semanticPrimitives_state_clock_fupd (K k') s =
     semanticPrimitives_state_clock_fupd (K k) s) = T`,
  CHEAT_TAC);;

let evaluate_unit_check = prove
 (`evaluate (s:'a semanticPrimitives_state) (sem_env_v_fupd (K (nsBind v w
  env1)) env)
     [ast_Mat (ast_Var (Short v)) [(ast_Pcon NONE [],ee)]] = (s',res) ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             UNIT_TYPE one w`,
  CHEAT_TAC);;

let evaluate_str_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE (ast_App ast_Strlen [ast_Var (Short v)]) ee] = (s',res)
       /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             STRING_TYPE_HEAD w /\ evaluate (s:'a semanticPrimitives_state)
             env [ee] = (s',res)`,
  CHEAT_TAC);;

let evaluate_ty_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE
        (ast_Mat (ast_Var (Short v))
           [(ast_Pcon (SOME (Short (implode "Tyvar"))) [ast_Pvar a1],ast_Con
             NONE []);
            (ast_Pcon (SOME (Short (implode "Tyapp"))) [ast_Pvar a3;
              ast_Pvar a4],ast_Con NONE [])]) ee] = (s',res) /\
   nsLookup (sem_env_c env) (Short (implode "Tyvar")) = SOME (1,TypeStamp
     (implode "Tyvar") type_stamp_n) /\
   nsLookup (sem_env_c env) (Short (implode "Tyapp")) = SOME (2,TypeStamp
     (implode "Tyapp") type_stamp_n) /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             TYPE_TYPE_HEAD w /\ evaluate (s:'a semanticPrimitives_state) env
             [ee] = (s',res)`,
  CHEAT_TAC);;

let evaluate_tm_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE
        (ast_Mat (ast_Var (Short v))
           [(ast_Pcon (SOME (Short (implode "Var"))) [ast_Pvar a1; ast_Pvar
             a2],ast_Con NONE []);
            (ast_Pcon (SOME (Short (implode "Const"))) [ast_Pvar a3;
              ast_Pvar a4],ast_Con NONE []);
            (ast_Pcon (SOME (Short (implode "Comb"))) [ast_Pvar a5; ast_Pvar
              a6],ast_Con NONE []);
            (ast_Pcon (SOME (Short (implode "Abs"))) [ast_Pvar a7; ast_Pvar
              a8],ast_Con NONE [])]) ee] = (s',res) /\
   nsLookup (sem_env_c env) (Short (implode "Var")) = SOME (2,TypeStamp
     (implode "Var") term_stamp_n) /\
   nsLookup (sem_env_c env) (Short (implode "Const")) = SOME (2,TypeStamp
     (implode "Const") term_stamp_n) /\
   nsLookup (sem_env_c env) (Short (implode "Comb")) = SOME (2,TypeStamp
     (implode "Comb") term_stamp_n) /\
   nsLookup (sem_env_c env) (Short (implode "Abs")) = SOME (2,TypeStamp
     (implode "Abs") term_stamp_n) /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             TERM_TYPE_HEAD w /\ evaluate (s:'a semanticPrimitives_state) env
             [ee] = (s',res)`,
  CHEAT_TAC);;

let evaluate_thm_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE
       (ast_Mat (ast_Var (Short v))
         [(ast_Pcon (SOME (Short (implode "Sequent"))) [ast_Pvar a1;
           ast_Pvar a2],ast_Con NONE [])]) ee] =
     (s',res) /\
   nsLookup (sem_env_c env) (Short (implode "Sequent")) = SOME (2,TypeStamp
     (implode "Sequent") thm_stamp_n) /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             THM_TYPE_HEAD w /\ evaluate (s:'a semanticPrimitives_state) env
             [ee] = (s',res)`,
  CHEAT_TAC);;

let evaluate_mat_pair = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Mat (ast_Var (Short v)) [(ast_Pcon NONE [ast_Pvar a1; ast_Pvar
       a2],ee)]] = (s',res) /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
   (?v1 v2. w = semanticPrimitives_Conv NONE [v1; v2] /\
     evaluate s (sem_env_v_fupd (K (nsBind a2 v2 (nsBind a1 v1 (sem_env_v
       env)))) env) [ee] = (s',res))`,
  CHEAT_TAC);;

let evaluate_mat_thm = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Mat (ast_Var (Short v))
        [(ast_Pcon (SOME (Short (implode "Sequent"))) [ast_Pvar a1; ast_Pvar
          a2],ee)]] = (s',res) /\
   nsLookup (sem_env_c env) (Short (implode "Sequent")) = SOME (2,TypeStamp
     (implode "Sequent") thm_stamp_n) /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/ res = Rerr (Rraise
            semanticPrimitives_bind_exn_v) \/ res = (Rerr (Rabort
            Rtimeout_error):(semanticPrimitives_v
            list,semanticPrimitives_v)semanticPrimitives_result))) \/
   (?v1 v2.
     THM_TYPE_HEAD w /\
     evaluate (s:'a semanticPrimitives_state) (sem_env_v_fupd (K (nsBind
       a2 v2 (nsBind a1 v1 (sem_env_v env)))) env) [ee] = (s',res))`,
  CHEAT_TAC);;

let check_tm_head = prove
 (`!v s.
     ?env e s' res.
       semanticPrimitives_do_opapp [check_tm_v; v] = SOME (env,e) /\
       evaluate (evaluate_dec_clock (s:'a semanticPrimitives_state)) env [e]
         = (s',res) /\
       ((?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
         semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/ res = Rerr (Rraise
            semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
        (?k z. s' = semanticPrimitives_state_clock_fupd (K k) s /\ res =
          Rval [z] /\
        LIST_TYPE_HEAD TERM_TYPE_HEAD v))`,
  CHEAT_TAC);;

let check_ty_head = prove
 (`!v s.
     ?env e s' res.
       semanticPrimitives_do_opapp [check_ty_v; v] = SOME (env,e) /\
       evaluate (evaluate_dec_clock (s:'a semanticPrimitives_state)) env [e]
         = (s',res) /\
       ((?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
         semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/ res = Rerr (Rraise
            semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
        (?k z. s' = semanticPrimitives_state_clock_fupd (K k) s /\ res =
          Rval [z] /\
        LIST_TYPE_HEAD TYPE_TYPE_HEAD v))`,
  CHEAT_TAC);;

let check_thm_head = prove
 (`!v s.
     ?env e s' res.
       semanticPrimitives_do_opapp [check_thm_v; v] = SOME (env,e) /\
       evaluate (evaluate_dec_clock (s:'a semanticPrimitives_state)) env [e]
         = (s',res) /\
       ((?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
         semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/ (?k z.
             s' = semanticPrimitives_state_clock_fupd (K k) s /\ res = Rval [z]
             /\
        LIST_TYPE_HEAD THM_TYPE_HEAD v))`,
  CHEAT_TAC);;

let check_tm_tm_head = prove
 (`!v s.
     ?env e s' res.
       semanticPrimitives_do_opapp [check_tm_tm_v; v] = SOME (env,e) /\
       evaluate (evaluate_dec_clock (s:'a semanticPrimitives_state)) env [e]
         = (s',res) /\
       ((?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
         semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/ res
         = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/ (?k z.
             s' = semanticPrimitives_state_clock_fupd (K k) s /\ res = Rval [z]
             /\
        LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v))`,
  CHEAT_TAC);;

let check_ty_ty_head = prove
 (`!v s.
     ?env e s' res.
       semanticPrimitives_do_opapp [check_ty_ty_v; v] = SOME (env,e) /\
       evaluate (evaluate_dec_clock (s:'a semanticPrimitives_state)) env [e]
         = (s',res) /\
       ((?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
         semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/ res
         = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/ (?k z.
             s' = semanticPrimitives_state_clock_fupd (K k) s /\ res = Rval [z]
             /\
        LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v))`,
  CHEAT_TAC);;

let evaluate_ty_list_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE (ast_App ast_Opapp [ast_Var (Short (implode "check_ty"));
       ast_Var (Short v)]) ee] = (s',res) /\
   nsLookup (sem_env_v env) (Short (implode "check_ty")) = SOME check_ty_v
     /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
   LIST_TYPE_HEAD TYPE_TYPE_HEAD w /\
   (?k. evaluate (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) env [ee] = (s',res))`,
  CHEAT_TAC);;

let evaluate_thm_list_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE (ast_App ast_Opapp [ast_Var (Short (implode
       "check_thm")); ast_Var (Short v)]) ee] = (s',res) /\
   nsLookup (sem_env_v env) (Short (implode "check_thm")) = SOME check_thm_v
     /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/ res = Rerr (Rraise
            semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
   LIST_TYPE_HEAD THM_TYPE_HEAD w /\
   (?k. evaluate (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) env [ee] = (s',res))`,
  CHEAT_TAC);;

let evaluate_ty_ty_list_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE (ast_App ast_Opapp [ast_Var (Short (implode
       "check_ty_ty")); ast_Var (Short v)]) ee] = (s',res) /\
   nsLookup (sem_env_v env) (Short (implode "check_ty_ty")) = SOME
     check_ty_ty_v /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
   LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) w /\
   (?k. evaluate (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) env [ee] = (s',res))`,
  CHEAT_TAC);;

let evaluate_tm_list_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE (ast_App ast_Opapp [ast_Var (Short (implode "check_tm"));
       ast_Var (Short v)]) ee] = (s',res) /\
   nsLookup (sem_env_v env) (Short (implode "check_tm")) = SOME check_tm_v
     /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
   LIST_TYPE_HEAD TERM_TYPE_HEAD w /\
   (?k. evaluate (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) env [ee] = (s',res))`,
  CHEAT_TAC);;

let evaluate_tm_tm_list_check = prove
 (`evaluate (s:'a semanticPrimitives_state) env
     [ast_Let NONE (ast_App ast_Opapp [ast_Var (Short (implode
       "check_tm_tm")); ast_Var (Short v)]) ee] = (s',res) /\
   nsLookup (sem_env_v env) (Short (implode "check_tm_tm")) = SOME
     check_tm_tm_v /\
   nsLookup (sem_env_v env) (Short v) = SOME w ==>
   (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
   LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) w /\
   (?k. evaluate (semanticPrimitives_state_clock_fupd (K k) (s:'a
     semanticPrimitives_state)) env [ee] = (s',res))`,
  CHEAT_TAC);;

let types_v_head = prove
 (`semanticPrimitives_do_opapp [types_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     UNIT_TYPE one v`,
  CHEAT_TAC);;

let constants_v_head = prove
 (`semanticPrimitives_do_opapp [constants_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             UNIT_TYPE one v`,
  CHEAT_TAC);;

let axioms_v_head = prove
 (`semanticPrimitives_do_opapp [axioms_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     UNIT_TYPE one v`,
  CHEAT_TAC);;

let mk_vartype_v_head = prove
 (`semanticPrimitives_do_opapp [mk_vartype_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     (?x. STRING_TYPE x v)`,
  CHEAT_TAC);;

let call_new_type_v_head = prove
 (`semanticPrimitives_do_opapp [call_new_type_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             PAIR_TYPE_HEAD STRING_TYPE_HEAD INT_HEAD v`,
  CHEAT_TAC);;

(* HOL4 candle_kernel_valsScript.sml:1069-1091: a proof *)

let is_type_v_head = prove
 (`semanticPrimitives_do_opapp [is_type_v; w] = SOME (env,exp) /\
   evaluate s env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TYPE_TYPE_HEAD w`,
  CHEAT_TAC);;

let concl_v_head = prove
 (`semanticPrimitives_do_opapp [concl_v; v] = SOME (env,exp) /\
   evaluate s env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v`,
  CHEAT_TAC);;

let trans_v_head = prove
 (`do_partial_app trans_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate s env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v /\ THM_TYPE_HEAD w`,
  CHEAT_TAC);;

let beta_v_head = prove
 (`semanticPrimitives_do_opapp [beta_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let call_variant_v_head = prove
 (`do_partial_app call_variant_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     LIST_TYPE_HEAD TERM_TYPE_HEAD v /\
     TERM_TYPE_HEAD w`,
  CHEAT_TAC);;

let vsubst_v_head = prove
 (`do_partial_app vsubst_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/ res =
       Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v /\
     TERM_TYPE_HEAD w`,
  CHEAT_TAC);;

let dest_type_v_head = prove
 (`semanticPrimitives_do_opapp [dest_type_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             TYPE_TYPE_HEAD v`,
  CHEAT_TAC);;

let is_vartype_v_head = prove
 (`semanticPrimitives_do_opapp [is_vartype_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TYPE_TYPE_HEAD v`,
  CHEAT_TAC);;

let is_var_v_head = prove
 (`semanticPrimitives_do_opapp [is_var_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let is_const_v_head = prove
 (`semanticPrimitives_do_opapp [is_const_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let is_abs_v_head = prove
 (`semanticPrimitives_do_opapp [is_abs_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let is_comb_v_head = prove
 (`semanticPrimitives_do_opapp [is_comb_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let rand_v_head = prove
 (`semanticPrimitives_do_opapp [rand_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let rator_v_head = prove
 (`semanticPrimitives_do_opapp [rator_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let dest_var_v_head = prove
 (`semanticPrimitives_do_opapp [dest_var_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let dest_const_v_head = prove
 (`semanticPrimitives_do_opapp [dest_const_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let dest_comb_v_head = prove
 (`semanticPrimitives_do_opapp [dest_comb_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let dest_abs_v_head = prove
 (`semanticPrimitives_do_opapp [dest_abs_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let dest_vartype_v_head = prove
 (`semanticPrimitives_do_opapp [dest_vartype_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TYPE_TYPE_HEAD v`,
  CHEAT_TAC);;

let dest_eq_v_head = prove
 (`semanticPrimitives_do_opapp [dest_eq_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let call_tyvars_v_head = prove
 (`semanticPrimitives_do_opapp [call_tyvars_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TYPE_TYPE_HEAD v`,
  CHEAT_TAC);;

let call_type_vars_in_term_v_head = prove
 (`semanticPrimitives_do_opapp [call_type_vars_in_term_v; v] = SOME (env,exp)
  /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let new_basic_definition_v_head = prove
 (`semanticPrimitives_do_opapp [new_basic_definition_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let new_specification_v_head = prove
 (`semanticPrimitives_do_opapp [new_specification_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v`,
  CHEAT_TAC);;

let get_const_type_v_head = prove
 (`semanticPrimitives_do_opapp [get_const_type_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     STRING_TYPE_HEAD v`,
  CHEAT_TAC);;

let new_constant_v_head = prove
 (`semanticPrimitives_do_opapp [new_constant_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     PAIR_TYPE_HEAD STRING_TYPE_HEAD TYPE_TYPE_HEAD v`,
  CHEAT_TAC);;

let mk_var_v_head = prove
 (`semanticPrimitives_do_opapp [mk_var_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     PAIR_TYPE_HEAD STRING_TYPE_HEAD TYPE_TYPE_HEAD v`,
  CHEAT_TAC);;

let mk_comb_v_head = prove
 (`semanticPrimitives_do_opapp [mk_comb_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let get_type_arity_v_head = prove
 (`semanticPrimitives_do_opapp [get_type_arity_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     STRING_TYPE_HEAD v`,
  CHEAT_TAC);;

let mk_type_v_head = prove
 (`semanticPrimitives_do_opapp [mk_type_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     PAIR_TYPE_HEAD STRING_TYPE_HEAD (LIST_TYPE_HEAD TYPE_TYPE_HEAD) v`,
  CHEAT_TAC);;

let refl_v_head = prove
 (`semanticPrimitives_do_opapp [refl_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let mk_const_v_head = prove
 (`semanticPrimitives_do_opapp [mk_const_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     PAIR_TYPE_HEAD STRING_TYPE_HEAD
       (LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD)) v`,
  CHEAT_TAC);;

let freesl_v_head = prove
 (`semanticPrimitives_do_opapp [freesl_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     LIST_TYPE_HEAD TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let assume_v_head = prove
 (`semanticPrimitives_do_opapp [assume_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let hyp_v_head = prove
 (`semanticPrimitives_do_opapp [hyp_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v`,
  CHEAT_TAC);;

let dest_thm_v_head = prove
 (`semanticPrimitives_do_opapp [dest_thm_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v`,
  CHEAT_TAC);;

let mk_comb_1_v_head = prove
 (`semanticPrimitives_do_opapp [mk_comb_1_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             PAIR_TYPE_HEAD THM_TYPE_HEAD THM_TYPE_HEAD v`,
  CHEAT_TAC);;

let new_basic_type_definition_v_head = prove
 (`semanticPrimitives_do_opapp [new_basic_type_definition_v; v] = SOME
  (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     (PAIR_TYPE_HEAD STRING_TYPE_HEAD (
        PAIR_TYPE_HEAD STRING_TYPE_HEAD
           (PAIR_TYPE_HEAD STRING_TYPE_HEAD THM_TYPE_HEAD))) v`,
  CHEAT_TAC);;

let call_type_subst_v_head = prove
 (`do_partial_app call_type_subst_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/ res =
       Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v /\
     TYPE_TYPE_HEAD w`,
  CHEAT_TAC);;

let inst_v_head = prove
 (`do_partial_app inst_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD TYPE_TYPE_HEAD) v /\
     TERM_TYPE_HEAD w`,
  CHEAT_TAC);;

let abs_v_head = prove
 (`do_partial_app abs_1_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD w /\
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let eq_mp_v_head = prove
 (`do_partial_app eq_mp_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v /\
     THM_TYPE_HEAD w`,
  CHEAT_TAC);;

let deduct_antisym_rule_v_head = prove
 (`do_partial_app deduct_antisym_rule_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v /\
     THM_TYPE_HEAD w`,
  CHEAT_TAC);;

let inst_type_v_head = prove
 (`do_partial_app inst_type_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD w /\ LIST_TYPE_HEAD (PAIR_TYPE_HEAD TYPE_TYPE_HEAD
       TYPE_TYPE_HEAD) v`,
  CHEAT_TAC);;

let inst_1_v_head = prove
 (`do_partial_app inst_1_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/ res =
       Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD w /\
     LIST_TYPE_HEAD (PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD) v`,
  CHEAT_TAC);;

let new_axiom_v_head = prove
 (`semanticPrimitives_do_opapp [new_axiom_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
             TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let call_type_of_v_head = prove
 (`semanticPrimitives_do_opapp [call_type_of_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let call_vfree_in_v_head = prove
 (`do_partial_app call_vfree_in_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/ res = Rerr (Rraise
            semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v /\
     TERM_TYPE_HEAD w`,
  CHEAT_TAC);;

let call_freesin_v_head = prove
 (`do_partial_app call_freesin_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     LIST_TYPE_HEAD TERM_TYPE_HEAD v /\
     TERM_TYPE_HEAD w`,
  CHEAT_TAC);;

let mk_abs_v_head = prove
 (`semanticPrimitives_do_opapp [mk_abs_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     PAIR_TYPE_HEAD TERM_TYPE_HEAD TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

let call_frees_v_head = prove
 (`semanticPrimitives_do_opapp [call_frees_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\ (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     TERM_TYPE_HEAD v`,
  CHEAT_TAC);;

(* Kernel_print_thm_v_head *)
let kernel_print_thm_v_head = prove
 (`semanticPrimitives_do_opapp [Kernel_print_thm_v; v] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     THM_TYPE_HEAD v`,
  CHEAT_TAC);;

let compute_add_v_head = prove
 (`do_partial_app compute_add_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     LIST_TYPE_HEAD THM_TYPE_HEAD v /\
     TERM_TYPE_HEAD w`,
  CHEAT_TAC);;

let compute_v_head = prove
 (`do_partial_app compute_v v = SOME g /\
   semanticPrimitives_do_opapp [g; w] = SOME (env,exp) /\
   evaluate (s:'a semanticPrimitives_state) env [exp] = (s',res) ==>
     (?k. s' = (semanticPrimitives_state_clock_fupd (K k) (s:'a
       semanticPrimitives_state)) /\
          (res = Rerr (Rabort Rtype_error) \/
           res = Rerr (Rraise semanticPrimitives_bind_exn_v) \/
           res = (Rerr (Rabort Rtimeout_error):(semanticPrimitives_v
             list,semanticPrimitives_v)semanticPrimitives_result))) \/
     PAIR_TYPE_HEAD (LIST_TYPE_HEAD THM_TYPE_HEAD)
                    (LIST_TYPE_HEAD THM_TYPE_HEAD) v /\
     TERM_TYPE_HEAD w`,
  CHEAT_TAC);;

(* -------------------------------------------------------------------------
 * Misc. simps
 * ------------------------------------------------------------------------- *)

let Conv_NOT_IN_kernel_funs = prove
 (`~(semanticPrimitives_Conv opt vs IN kernel_funs)`,
  CHEAT_TAC);;
add_simp Conv_NOT_IN_kernel_funs;;

let list_not_TERM_TYPE = prove
 (`~(TERM_TYPE tm (semanticPrimitives_Conv (SOME (TypeStamp nm
  list_type_num)) vs))`,
  CHEAT_TAC);;
add_simp list_not_TERM_TYPE;;

let list_not_THM_TYPE = prove
 (`~(THM_TYPE th (semanticPrimitives_Conv (SOME (TypeStamp nm list_type_num))
  vs))`,
  CHEAT_TAC);;
add_simp list_not_THM_TYPE;;

let list_type_NOTIN_kernel_types = prove
 (`~(list_type_num IN kernel_types)`,
  CHEAT_TAC);;
add_simp list_type_NOTIN_kernel_types;;

let bool_type_NOTIN_kernel_types = prove
 (`~(bool_type_num IN kernel_types)`,
  CHEAT_TAC);;
add_simp bool_type_NOTIN_kernel_types;;

let TYPE_TYPE_Vectorv = prove
 (`~(TYPE_TYPE ty (semanticPrimitives_Vectorv vs))`,
  CHEAT_TAC);;
add_simp TYPE_TYPE_Vectorv;;

let TERM_TYPE_Vectorv = prove
 (`~(TERM_TYPE tm (semanticPrimitives_Vectorv vs))`,
  CHEAT_TAC);;
add_simp TERM_TYPE_Vectorv;;

let THM_TYPE_Vectorv = prove
 (`~(THM_TYPE th (semanticPrimitives_Vectorv vs))`,
  CHEAT_TAC);;
add_simp THM_TYPE_Vectorv;;

let inferred_Vectorv = prove
 (`~(inferred ctxt (semanticPrimitives_Vectorv vs))`,
  CHEAT_TAC);;
add_simp inferred_Vectorv;;

let inferred_Conv = prove
 (`inferred ctxt (semanticPrimitives_Conv (SOME stamp) vs) ==>
     (?tag m. stamp = TypeStamp tag m /\ m IN kernel_types)`,
  CHEAT_TAC);;

let inferred_Conv_NONE = prove
 (`~(inferred ctxt (semanticPrimitives_Conv NONE vs))`,
  CHEAT_TAC);;
add_simp inferred_Conv_NONE;;

let inferred_Loc = prove
 (`~(inferred ctxt (semanticPrimitives_Loc b loc))`,
  CHEAT_TAC);;
add_simp inferred_Loc;;

let inferred_Env = prove
 (`~(inferred ctxt1 (semanticPrimitives_Env env id))`,
  CHEAT_TAC);;
add_simp inferred_Env;;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id"];;

(* and the interface *)
let _ = unhide_overloads ();;
