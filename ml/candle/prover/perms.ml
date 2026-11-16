(* ======================================================== *)
(*  perms: ported from HOL4's
    candle/prover/permsScript.sml
    A definition theory, with 6 definitions, 1 datatype and 22
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  Permissions for CakeML values.
 *)

needs "basis/pure/mlstring.ml";;
needs "candle/prover/ast_extras.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/evaluateProps.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_prog.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "perms"
  ["ast_extras"; "evaluate"; "evaluateProps"; "ml_prog"; "namespaceProps";
   "semanticPrimitives"; "semanticPrimitivesProps"];;

let _ = do_list hide_constant ["fv"];;


new_type_abbrev("perms_loc",`:num`);;

(* -------------------------------------------------------------------------
 * We define a set of permissions for our value relation, which restricts
 * what our code can do.
 * ------------------------------------------------------------------------- *)

let permission_INDUCT,permission_RECURSION = define_datatype
  "permission =
     FFIWrite string
     // Write to FFI channel with name
   | RefMention perms_loc
     // Mention reference using pointer
   | RefUpdate
     // Write to references
   | RefAlloc
     // Allocate new references
   | DoFFI
     // Call FFI
   | W8Alloc
     // Allocate byte arrays
  ";;

let perms_ok_exp_def = new_definition
  `perms_ok_exp ps =
     ast_extras_every_exp (\x.
       match x with
         ast_App op xs -> ~(op = ast_Eval) /\
           (op = ast_Opref ==> RefAlloc IN ps) /\
           (op = ast_Aalloc ==> RefAlloc IN ps) /\
           (op = ast_AallocEmpty ==> RefAlloc IN ps) /\
           (op = ast_AallocFixed ==> RefAlloc IN ps) /\
           (op = ast_Aw8alloc ==> W8Alloc IN ps) /\
           (op = ast_Opassign ==> RefUpdate IN ps) /\
           (!chn. op = ast_FFI chn ==> FFIWrite (explode chn) IN ps /\ DoFFI
             IN ps) /\
           (!m. op = ast_ThunkOp (AllocThunk m) ==> RefAlloc IN ps) /\
           (!m. op = ast_ThunkOp (UpdateThunk m) ==> RefUpdate IN ps)
       | _ -> T)`;;

(* HOL4 permsScript.sml:46-63: a theorem that HOL4 states as the value of an
   ML expression: perms_ok_exp_thm *)

let perms_ok_dec_def = new_definition
  `perms_ok_dec ps =
     every_dec (\d.
       match d with
         Dlet locs pat exp ->
                 // pats_ok ps pat ∧
                 perms_ok_exp ps exp
       | Dletrec locs funs -> ALL (perms_ok_exp ps) (MAP (SND o SND) funs)
       | _ -> T)`;;

(* HOL4 permsScript.sml:74-85: a theorem that HOL4 states as the value of an
   ML expression: perms_ok_dec_thm *)

let perms_ok = cake_inductive
  `((!ps opt vs.
        ALL (perms_ok ps) vs ==>
          perms_ok ps (semanticPrimitives_Conv opt vs))) /\
   ((!ps env n x.
        perms_ok_env ps (freevars x DIFF {Short n}) env /\
        perms_ok_exp ps x ==>
          perms_ok ps (semanticPrimitives_Closure env n x))) /\
   ((!ps env f n.
        perms_ok_env ps
                     (UNIONS (set_of_list (MAP (\(fn,vn,x). freevars x DIFF
                              {Short fn,Short vn}) f)))
                     env /\
        ALL (perms_ok_exp ps) (MAP (SND o SND) f) ==>
          perms_ok ps (semanticPrimitives_Recclosure env f n))) /\
   ((!ps vs.
        ALL (perms_ok ps) vs ==>
          perms_ok ps (semanticPrimitives_Vectorv vs))) /\
   ((!ps lit.
        perms_ok ps (semanticPrimitives_Litv lit))) /\
   ((!ps b loc.
        RefMention loc IN ps ==>
          perms_ok ps (semanticPrimitives_Loc b loc))) /\
   ((!ps env ns.
        perms_ok_env ps UNIV env ==>
          perms_ok ps (semanticPrimitives_Env env ns))) /\
   ((!ps fvs env.
        (!n v.
           n IN fvs /\
           nsLookup (sem_env_v env) n = SOME v ==>
             perms_ok ps v) ==>
          perms_ok_env ps fvs env))`;;

(* HOL4 permsScript.sml:129-138: a theorem that HOL4 states as the value of
   an ML expression: perms_ok_def *)

(* HOL4 permsScript.sml:140-141: a theorem that HOL4 states as the value of
   an ML expression: perms_ok_env_def *)

let perms_ok_env_UNION = prove
 (`perms_ok_env ps (x UNION y) env <=>
     perms_ok_env ps x env /\
     perms_ok_env ps y env`,
  CHEAT_TAC);;

let perms_ok_env_BIGUNION = prove
 (`perms_ok_env ps (UNIONS xs) env <=>
     (!x. x IN xs ==> perms_ok_env ps x env)`,
  CHEAT_TAC);;

let perms_ok_bind_exn_v = prove
 (`perms_ok ps semanticPrimitives_bind_exn_v`,
  CHEAT_TAC);;
add_simp perms_ok_bind_exn_v;;

let perms_ok_div_exn_v = prove
 (`perms_ok ps semanticPrimitives_div_exn_v`,
  CHEAT_TAC);;
add_simp perms_ok_div_exn_v;;

let perms_ok_sub_exn_v = prove
 (`perms_ok ps sub_exn_v`,
  CHEAT_TAC);;
add_simp perms_ok_sub_exn_v;;

let perms_ok_chr_exn_v = prove
 (`perms_ok ps semanticPrimitives_chr_exn_v`,
  CHEAT_TAC);;
add_simp perms_ok_chr_exn_v;;

let perms_ok_ref_def = define_cases
  `(perms_ok_ref ps (semanticPrimitives_Refv v) = perms_ok ps v) /\
   (perms_ok_ref ps (semanticPrimitives_Varray vs) = ALL (perms_ok ps) vs) /\
   (perms_ok_ref ps (semanticPrimitives_W8array ws) = T) /\
   (perms_ok_ref ps (semanticPrimitives_Thunk _ v) = perms_ok ps v)`;;

let perms_ok_state_def = new_definition
  `perms_ok_state ps s =
     (!n. n < LENGTH (semanticPrimitives_state_refs s) /\
         RefMention n IN ps ==>
           perms_ok_ref ps (EL n (semanticPrimitives_state_refs s)))`;;

let perms_ok_state_with_clock = prove
 (`perms_ok_state ps (semanticPrimitives_state_clock_fupd (K ck) s) =
  perms_ok_state ps s`,
  CHEAT_TAC);;
add_simp perms_ok_state_with_clock;;

let pmatch_perms_ok = prove
 (`(!envC s p v ws env.
     semanticPrimitives_pmatch envC s p v ws = Match env /\
     perms_ok perms v /\
     (RefAlloc IN perms ==> IMAGE RefMention UNIV SUBSET perms) /\
     (!n. n < LENGTH s /\ RefMention n IN perms ==> perms_ok_ref perms (EL n
       s)) /\
     ALL (perms_ok perms) (MAP SND ws) ==>
       ALL (perms_ok perms) (MAP SND env)) /\
   (!envC s ps vs ws env.
     semanticPrimitives_pmatch_list envC s ps vs ws = Match env /\
     ALL (perms_ok perms) vs /\
     (RefAlloc IN perms ==> IMAGE RefMention UNIV SUBSET perms) /\
     (!n. n < LENGTH s /\ RefMention n IN perms ==> perms_ok_ref perms (EL n
       s)) /\
     ALL (perms_ok perms) (MAP SND ws) ==>
       ALL (perms_ok perms) (MAP SND env))`,
  CHEAT_TAC);;

let perms_ok_env_extend_dec_env = prove
 (`perms_ok_env ps fvs env1 /\
   perms_ok_env ps fvs env ==>
     perms_ok_env ps fvs (extend_dec_env env1 env)`,
  CHEAT_TAC);;

let EVERY_perms_ok_env_BIGUNION = prove
 (`!xs.
     ALL (\x. perms_ok_env ps (P x) env) xs =
     perms_ok_env ps (UNIONS (set_of_list (MAP P xs))) env`,
  CHEAT_TAC);;

let perms_ok_env_EMPTY = prove
 (`perms_ok_env ps EMPTY env`,
  CHEAT_TAC);;

(* the termination relation that HOL4 gives is
     MEASURE dec_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let dfreevars_def,dfreevars_ind = define_guess
  `dfreevars x1 =
   match x1 with
     Dlet locs p x ->
     (freevars x DIFF set_of_list (MAP Short (ast_pat_bindings p)))
   | Dletrec locs f ->
     UNIONS (set_of_list (MAP (\(fn,vn,x). freevars x DIFF {Short fn,Short
       vn}) f))
   | Dmod mn ds ->
     UNIONS (set_of_list (MAP dfreevars ds))
   | Dlocal ds1 ds2 ->
     UNIONS (set_of_list (MAP dfreevars ds1)) UNION
     UNIONS (set_of_list (MAP dfreevars ds2))
   | _ -> EMPTY`;;

let perms_ok_v_to_list = prove
 (`!v vs.
     semanticPrimitives_v_to_list v = SOME vs /\
     perms_ok ps v ==>
       ALL (perms_ok ps) vs`,
  CHEAT_TAC);;

let do_app_perms = prove
 (`semanticPrimitives_do_app (refs,ffi) op vs = SOME ((refs1,ffi1),res) /\ ~(op
  = ast_Opapp) /\ ~(op = ast_Eval) /\
   ALL (perms_ok ps) vs /\
   (RefAlloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
   (W8Alloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
   (!n. n < LENGTH refs /\ RefMention n IN ps ==> perms_ok_ref ps (EL n
     refs)) /\
   (op = ast_Opref ==> RefAlloc IN ps) /\
   (op = ast_Aalloc ==> RefAlloc IN ps) /\
   (op = ast_AallocEmpty ==> RefAlloc IN ps) /\
   (op = ast_AallocFixed ==> RefAlloc IN ps) /\
   (op = ast_Aw8alloc ==> W8Alloc IN ps) /\
   (op = ast_Opassign ==> RefUpdate IN ps) /\
   (!chn. op = ast_FFI chn ==> FFIWrite (explode chn) IN ps /\ DoFFI IN ps)
     /\
   (!m. op = ast_ThunkOp (AllocThunk m) ==> RefAlloc IN ps) /\
   (!m. op = ast_ThunkOp (UpdateThunk m) ==> RefUpdate IN ps) /\ ~(op =
     ast_Opapp) ==>
     (!n. n < LENGTH refs1 /\ RefMention n IN ps ==> perms_ok_ref ps (EL n
       refs1)) /\
     (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==> LENGTH refs1 = LENGTH refs)
       /\
     (~(DoFFI IN ps) ==> ffi1 = ffi) /\
     (!ch out y.
        MEM (IO_event (ffi_ExtCall ch) out y) (ffi_state_io_events ffi1) ==>
        MEM (IO_event (ffi_ExtCall ch) out y) (ffi_state_io_events ffi) \/
          FFIWrite (explode ch) IN ps) /\
     (match list_result res with
       Rval vs -> ALL (perms_ok ps) vs
     | Rerr (Rraise v) -> perms_ok ps v
     | Rerr (Rabort err) -> T)`,
  CHEAT_TAC);;

let perms_ok_do_opapp = prove
 (`perms_ok ps fv /\
   perms_ok ps av /\
   semanticPrimitives_do_opapp [fv; av] = SOME (env,exp) ==>
     perms_ok_exp ps exp /\
     perms_ok_env ps (freevars exp) env`,
  CHEAT_TAC);;

let evaluate_perms_ok = prove
 (`(!(s:'ffi semanticPrimitives_state). !env xs s' res.
      ALL (perms_ok_exp ps) xs /\
      ALL (\x. perms_ok_env ps (freevars x) env) xs /\
      perms_ok_state ps s /\
      (RefAlloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
      (W8Alloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
      evaluate s env xs = (s',res) ==>
        (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==> LENGTH
          (semanticPrimitives_state_refs s') = LENGTH
          (semanticPrimitives_state_refs s))
          /\ semanticPrimitives_state_next_type_stamp
        s' = semanticPrimitives_state_next_type_stamp s
          /\ semanticPrimitives_state_eval_state
        s' = semanticPrimitives_state_eval_state s /\
        (~(DoFFI IN ps) ==> semanticPrimitives_state_ffi s' =
          semanticPrimitives_state_ffi s) /\
        perms_ok_state ps s' /\
        (!ffi out y.
           MEM (IO_event (ffi_ExtCall ffi) out y) (ffi_state_io_events
             (semanticPrimitives_state_ffi s')) ==>
           MEM (IO_event (ffi_ExtCall ffi) out y) (ffi_state_io_events
             (semanticPrimitives_state_ffi s)) \/ FFIWrite (explode ffi) IN ps)
             /\
        (match res with
          Rerr (Rraise v) -> perms_ok ps v
        | Rval vs -> ALL (perms_ok ps) vs
        | _ -> T)) /\
   (!(s:'ffi semanticPrimitives_state). !env v pes errv s' res.
      ALL (perms_ok_exp ps) (MAP SND pes) /\
      ALL (\(p,x). perms_ok_env ps (freevars x DIFF
                              set_of_list (MAP Short (ast_pat_bindings p)))
                                env)
            pes /\
      perms_ok_state ps s /\
      perms_ok ps v /\
      perms_ok ps errv /\
      (RefAlloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
      (W8Alloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
      evaluate_evaluate_match s env v pes errv = (s',res) ==>
        (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==> LENGTH
          (semanticPrimitives_state_refs s') = LENGTH
          (semanticPrimitives_state_refs s))
          /\ semanticPrimitives_state_next_type_stamp
        s' = semanticPrimitives_state_next_type_stamp s
          /\ semanticPrimitives_state_eval_state
        s' = semanticPrimitives_state_eval_state s /\
        (~(DoFFI IN ps) ==> semanticPrimitives_state_ffi s' =
          semanticPrimitives_state_ffi s) /\
        perms_ok_state ps s' /\
        (!ffi out y.
           MEM (IO_event (ffi_ExtCall ffi) out y) (ffi_state_io_events
             (semanticPrimitives_state_ffi s')) ==>
           MEM (IO_event (ffi_ExtCall ffi) out y) (ffi_state_io_events
             (semanticPrimitives_state_ffi s)) \/ FFIWrite (explode ffi) IN ps)
             /\
        (match res with
          Rerr (Rraise v) -> perms_ok ps v
        | Rval vs -> ALL (perms_ok ps) vs
        | _ -> T)) /\
   (!(s:'ffi semanticPrimitives_state). !env ds s' res.
      ALL (perms_ok_dec ps) ds /\
      perms_ok_state ps s /\
      perms_ok_env ps UNIV env /\
      (RefAlloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
      (W8Alloc IN ps ==> IMAGE RefMention UNIV SUBSET ps) /\
      evaluate_evaluate_decs s env ds = (s',res) ==>
        (~(RefAlloc IN ps) /\ ~(W8Alloc IN ps) ==> LENGTH
          (semanticPrimitives_state_refs s') = LENGTH
          (semanticPrimitives_state_refs s)) /\
        (~(DoFFI IN ps) ==> semanticPrimitives_state_ffi s' =
          semanticPrimitives_state_ffi s) /\
        perms_ok_state ps s' /\
        (!ffi out y.
           MEM (IO_event (ffi_ExtCall ffi) out y) (ffi_state_io_events
             (semanticPrimitives_state_ffi s')) ==>
           MEM (IO_event (ffi_ExtCall ffi) out y) (ffi_state_io_events
             (semanticPrimitives_state_ffi s)) \/ FFIWrite (explode ffi) IN ps)
             /\
        (match res with
          Rerr (Rraise v) -> perms_ok ps v
        | Rval env1 -> perms_ok_env ps UNIV env1
        | _ -> T))`,
  CHEAT_TAC);;

let evaluate_perms_ok_exp =
  SIMP_RULE [] (GEN_ALL (CAKE_SPECL [`s`; `env`; `[exp]`] (CONJUNCT1
  evaluate_perms_ok)));;

let evaluate_perms_ok_pat =
  SIMP_RULE [] (GEN_ALL (CAKE_SPECL [`s`; `env`; `v`; `[p,e]`] (CONJUNCT1
  (CONJUNCT2 evaluate_perms_ok))));;

let evaluate_perms_ok_dec =
  SIMP_RULE [] (GEN_ALL (CAKE_SPECL [`s`; `env`; `[dec]`] (CONJUNCT2
  (CONJUNCT2 evaluate_perms_ok))));;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
