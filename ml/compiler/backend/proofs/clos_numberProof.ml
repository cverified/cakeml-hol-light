(* ======================================================== *)
(*  clos_numberProof: ported from HOL4's
    compiler/backend/proofs/clos_numberProofScript.sml  *)
(* ======================================================== *)

(*
  Correctness proof for clos_number
*)

needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_number.ml";;
needs "compiler/backend/semantics/backendProps.ml";;
needs "compiler/backend/semantics/closProps.ml";;
needs "compiler/backend/semantics/closSem.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* properties of renumber_code_locs *)

(* HOL4 ML code, not ported:
fun tac (g as (asl,w)) =
  let
    fun finder tm =
      let
        val (f,args) = strip_comb tm
      in
        (same_const``renumber_code_locs`` f orelse
         same_const``renumber_code_locs_list`` f)
        andalso
         all is_var args
        andalso
         length args = 2
      end
    val tms = find_terms finder w
  in
    map_every (fn tm => Cases_on [ANTIQUOTE tm]) tms g
  end
*)

(* value relation *)

let v_rel = cake_inductive
  `(clos_numberProof_v_rel max_app (closSem_Number j) (closSem_Number
  j)) /\
   (clos_numberProof_v_rel max_app (Word64 w) (Word64 w)) /\
   (EVERY2 (clos_numberProof_v_rel max_app) (xs:closSem_v list)
     (ys:closSem_v list) ==>
    clos_numberProof_v_rel max_app (closSem_Block t xs)
      (closSem_Block t ys)) /\
   (clos_numberProof_v_rel max_app (closSem_ByteVector ws)
     (closSem_ByteVector ws)) /\
   (clos_numberProof_v_rel max_app (closSem_RefPtr b r1)
     (closSem_RefPtr b r1)) /\
   (LIST_REL (clos_numberProof_v_rel max_app) env env' /\
    LIST_REL (clos_numberProof_v_rel max_app) argenv argenv' /\
    ~contains_App_SOME max_app [c] /\
    c' = SND (renumber_code_locs n c) ==>
    clos_numberProof_v_rel max_app (Closure p argenv env num_args c)
      (Closure p' argenv' env' num_args c')) /\
   (
    LIST_REL (clos_numberProof_v_rel max_app) env env' /\
    LIST_REL (clos_numberProof_v_rel max_app) argenv argenv' /\
    ~contains_App_SOME max_app (MAP SND es) /\
    es' = ZIP (MAP FST es) (SND (renumber_code_locs_list n (MAP SND
      es))) ==>
    clos_numberProof_v_rel max_app (Recclosure p argenv env es k)
      (Recclosure p' argenv' env' es' k))`;;
hol4_overload "v_rel" "clos_numberProof_v_rel";;

let state_rel_def = cake_define
  `clos_numberProof_state_rel (s:(num#'c,'ffi)closSem_state)
  (t:('c,'ffi)closSem_state) <=>
     (state_clock s = state_clock t) /\ (state_ffi s = state_ffi t)
       /\ (closSem_state_max_app t = closSem_state_max_app s) /\
       closSem_state_compile
     s = state_cc (ignore_table clos_number_compile_inc)
       (closSem_state_compile t) /\ closSem_state_compile_oracle
     t = state_co (ignore_table clos_number_compile_inc)
       (closSem_state_compile_oracle s) /\
     fmap_rel (closProps_ref_rel (clos_numberProof_v_rel
       (closSem_state_max_app s))) (state_refs s) (state_refs t) /\
     EVERY2 (OPTREL (clos_numberProof_v_rel (closSem_state_max_app
       s))) (closSem_state_globals s) (closSem_state_globals t) /\
     (!n. SND (SND (closSem_state_compile_oracle s n)) = [] /\
          ~contains_App_SOME (closSem_state_max_app s) (FST (SND
            (closSem_state_compile_oracle s n)))) /\ closSem_state_code
     s = FEMPTY /\ closSem_state_code t = FEMPTY`;;
hol4_overload "state_rel" "clos_numberProof_state_rel";;

(* semantic functions respect relation *)

(* HOL4 ML code, not ported:
val do_app_inst =
  simple_val_rel_do_app
  |> Q.INST [`vr`|->`v_rel s.max_app`]
  |> INST_TYPE [``:'a``|->``:num # 'a``,``:'c``|->``:'a``]
  |> Q.INST [`sr`|->`\r t. (r.max_app = s.max_app) /\ state_rel r t`]
  |> SIMP_RULE std_ss []
*)

(* HOL4 ML code, not ported:
fun DFOCUS_PAT pat thm = let
    fun UN Ps thm = let
        val (P, Q) = dest_imp (concl thm)
      in if can (match_term pat) P then (UNDISCH thm, P, Ps)
        else UN (P :: Ps) (UNDISCH thm)
      end
    val (thm, P, Ps) = UN [] thm
  in DISCH P (List.foldl (uncurry DISCH) thm Ps) end
*)

(* compiler correctness *)

(*
val do_install_Rabort = prove(
  ``closSem$do_install xs s2 = (Rerr (Rabort a),s3) ==>
    a = Rtype_error \/ a = Rtimeout_error``,
  rw [do_install_def]
  \\ fs[case_eq_thms,pair_case_eq] \\ rveq \\ fs[]
  \\ pairarg_tac \\ fs []
  \\ fs [do_install_def,case_eq_thms,pair_case_eq,bool_case_eq]);
*)

(* preservation of observable semantics *)
