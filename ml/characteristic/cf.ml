(* ======================================================== *)
(*  cf: ported from HOL4's
    characteristic/cfScript.sml
    A definition theory, with 87 definitions and 83 theorems.
    Needed by 8 files of the port.  *)
(* ======================================================== *)

(*
  Defines the characteristic formula (CF) function cf_def and proves
  that it is sound w.r.t. the evaluate semantics of CakeML.
*)

needs "basis/pure/mlstring.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeaps.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "characteristic/cfNormalise.ml";;
needs "characteristic/cfStore.ml";;
needs "lib/integer_word.ml";;
needs "lib/lprefix_lub.ml";;
needs "lib/set_sep.ml";;
needs "semantics/ast.ml";;
needs "semantics/evaluate.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "cf"
  ["cfApp"; "cfHeaps"; "cfHeapsBase"; "cfNormalise"; "cfStore"; "evaluate";
   "ffi"; "fpSem"; "ml_translator"; "semanticPrimitives"];;

let _ = do_list hide_constant ["fv"];;

(*------------------------------------------------------------------*)
(* Characteristic formula for not-implemented or impossible cases *)

let cf_bottom_def = new_definition
  `cf_bottom = (\env. local (\H Q. F))`;;

(*------------------------------------------------------------------*)
(* Machinery for dealing with n-ary applications/functions in cf.

   Applications and ((mutually)recursive)functions are unary in
   CakeML's AST.
   Some machinery is therefore needed to walk down the AST and extract
   multiple arguments (for an application), or multiple parameters and
   the final function body (for functions).
*)

(** 1) n-ary applications *)

(* [local] *)
let dest_opapp_not_empty_arglist = prove
 (`!e f args. dest_opapp e = SOME (f,args) ==> ~(args = [])`,
  CHEAT_TAC);;

(** 2) n-ary single non-recursive functions *)

(* An auxiliary definition *)
let is_bound_Fun_def = new_definition
  `is_bound_Fun x1 x2 =
   match (x1,x2) with
     ((SOME _:mlstring option),ast_Fun _ _) -> T
   | (_,_) -> F`;;

(* [Fun_body]: walk down successive lambdas and return the inner
   function body *)
let fun_body_def,fun_body_ind = define_guess
  `Fun_body x1' =
   match x1' with
     ast_Fun _ body ->
     (match Fun_body body with NONE -> SOME body
        | SOME body' -> SOME body')
   | _ -> NONE`;;

make_size "ast_exp";;
(* Fun_body_exp_size[local] *)
let fun_body_exp_size = prove
 (`!e e'. Fun_body e = SOME e' ==> ast_exp_size e' < ast_exp_size e`,
  CHEAT_TAC);;

(* [local] *)
let is_bound_Fun_unfold = prove
 (`!opt e. is_bound_Fun opt e ==> (?n body. e = ast_Fun n body)`,
  CHEAT_TAC);;

(* [Fun_params]: walk down successive lambdas and return the list of
   parameters *)
let fun_params_def,fun_params_ind = define_guess
  `Fun_params x1'' =
   match x1'' with
     ast_Fun n body -> CONS n (Fun_params body)
   | _ ->
     []`;;

(* [local] *)
let Fun_params_Fun_body_NONE = prove
 (`!e. Fun_body e = NONE ==> Fun_params e = []`,
  CHEAT_TAC);;

(* [naryFun]: build the AST for a n-ary function *)
let naryFun_def,naryFun_ind = define_guess
  `(naryFun [] body = body) /\
   (naryFun (CONS n ns) body = ast_Fun n (naryFun ns body))`;;

(* [local] *)
let Fun_params_Fun_body_repack = prove
 (`!e e'.
     Fun_body e = SOME e' ==>
     naryFun (Fun_params e) e' = e`,
  CHEAT_TAC);;

(** 3) n-ary (mutually)recursive functions *)

(** Mutually recursive definitions (and closures) use a list of tuples
    (function name, parameter name, body). [letrec_pull_params] returns the
    "n-ary" version of this list, that is, a list of tuples:
    (function name, parameters names, inner body)
*)
let letrec_pull_params_def,letrec_pull_params_ind = define_guess
  `(letrec_pull_params [] = []) /\
   (letrec_pull_params (CONS (f,n,body) funs) = CONS (match Fun_body body with
    NONE -> (f,[n],body)
         | SOME body' -> (f,CONS n (Fun_params body),body'))
      (letrec_pull_params funs))`;;

let letrec_pull_params_names = prove
 (`!funs P.
     MAP (\(f,_,_). P f) (letrec_pull_params funs) =
     MAP (\(f,_,_). P f) funs`,
  CHEAT_TAC);;

let letrec_pull_params_LENGTH = prove
 (`!funs. LENGTH (letrec_pull_params funs) = LENGTH funs`,
  CHEAT_TAC);;

let letrec_pull_params_append = prove
 (`!l l'.
     letrec_pull_params (APPEND l l') = APPEND (letrec_pull_params l)
       (letrec_pull_params l')`,
  CHEAT_TAC);;

let letrec_pull_params_cancel = prove
 (`!funs.
     MAP (\(f,ns,body). (f,HD ns,naryFun (TL ns) body)) (letrec_pull_params
       funs) =
     funs`,
  CHEAT_TAC);;

let letrec_pull_params_nonnil_params = prove
 (`!funs f ns body.
     MEM (f,ns,body) (letrec_pull_params funs) ==> ~(ns = [])`,
  CHEAT_TAC);;

let find_recfun_letrec_pull_params = prove
 (`!funs f n ns body.
     find_recfun f (letrec_pull_params funs) = SOME (CONS n ns,body) ==>
     find_recfun f funs = SOME (n,naryFun ns body)`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* The semantic counterpart of n-ary functions: n-ary closures

   Also, dealing with environments.
*)

(* [naryClosure] *)
let naryClosure_def = new_definition
  `naryClosure env (CONS n ns) body = semanticPrimitives_Closure env n
  (naryFun ns body)`;;

(* Properties of [naryClosure] *)

(* [local] *)
let with_clock_clock = prove
 (`semanticPrimitives_state_clock
     (semanticPrimitives_state_clock_fupd (K k) s) = k`,
  CHEAT_TAC);;

(* [local] *)
let with_clock_with_clock = prove
 (`(semanticPrimitives_state_clock_fupd (K k2)
  (semanticPrimitives_state_clock_fupd (K k1) s)) =
  semanticPrimitives_state_clock_fupd (K k2) s`,
  CHEAT_TAC);;

(* [local] *)
let with_clock_self = prove
 (`(semanticPrimitives_state_clock_fupd (K (semanticPrimitives_state_clock
  s)) s) = s`,
  CHEAT_TAC);;

(* [local] *)
let with_clock_self_eq = prove
 (`!ck. (semanticPrimitives_state_clock_fupd (K ck) s) = s <=> ck =
  semanticPrimitives_state_clock s`,
  CHEAT_TAC);;

(* [local] *)
let evaluate_to_heap_with_clock = prove
 (`evaluate_to_heap (semanticPrimitives_state_clock_fupd (K ck) st) =
  evaluate_to_heap st`,
  CHEAT_TAC);;

let app_one_naryClosure = prove
 (`!env n ns x xs body H Q. ~(ns = []) ==> ~(xs = []) ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryClosure env (CONS n ns) body) (CONS x xs) H Q ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryClosure (sem_env_v_fupd (K (nsBind n x (sem_env_v env))) env) ns
       body) xs H Q`,
  CHEAT_TAC);;

let curried_naryClosure = prove
 (`!env len ns body. ~(ns = []) ==> len = LENGTH ns ==>
     curried (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) len
       (naryClosure env ns body)`,
  CHEAT_TAC);;

(* [naryRecclosure] *)
let naryRecclosure_def = new_definition
  `naryRecclosure env naryfuns f =
     semanticPrimitives_Recclosure env
     (MAP (\(f,ns,body). (f,HD ns,naryFun (TL ns) body)) naryfuns)
     f`;;

(* Properties of [naryRecclosure] *)

let do_opapp_naryRecclosure = prove
 (`!funs f n ns body x env env' exp.
     find_recfun f (letrec_pull_params funs) = SOME (CONS n ns,body) ==>
     (
     semanticPrimitives_do_opapp [naryRecclosure env (letrec_pull_params
       funs) f; x] =
      SOME (env',exp) <=>
     (ALL_DISTINCT (MAP (\(f,_,_). f) funs) /\
      env' = (sem_env_v_fupd (K (nsBind n x
        (semanticPrimitives_build_rec_env funs env (sem_env_v env)))) env) /\
      exp = naryFun ns body))`,
  CHEAT_TAC);;

let app_one_naryRecclosure = prove
 (`!funs f n ns body x xs env H Q. ~(ns = []) ==> ~(xs = []) ==>
     find_recfun f (letrec_pull_params funs) = SOME (CONS n ns,body) ==>
     (app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryRecclosure env (letrec_pull_params funs) f) (CONS x xs) H Q ==>
      app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
        (naryClosure
          (sem_env_v_fupd (K (nsBind n x (semanticPrimitives_build_rec_env
            funs env (sem_env_v env)))) env)
          ns body) xs H Q)`,
  CHEAT_TAC);;

let curried_naryRecclosure = prove
 (`!env funs f len ns body.
     ALL_DISTINCT (MAP (\(f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (ns,body) ==>
     len = LENGTH ns ==>
     curried (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) len
       (naryRecclosure env (letrec_pull_params funs) f)`,
  CHEAT_TAC);;

let letrec_pull_params_repack = prove
 (`!funs f env.
     naryRecclosure env (letrec_pull_params funs) f =
     semanticPrimitives_Recclosure env funs f`,
  CHEAT_TAC);;

(** Extending environments *)

(* TODO: there's a version of this already defined ...*)
(* [extend_env] *)
let extend_env_v_def,extend_env_v_ind = define_guess
  `(extend_env_v [] [] env_v = env_v) /\
   (extend_env_v (CONS n ns) (CONS xv xvs) env_v =
      extend_env_v ns xvs (nsBind n xv env_v))`;;

let cf_extend_env_def = new_definition
  `cf_extend_env ns xvs (env:'v sem_env) = (sem_env_v_fupd (K (extend_env_v
  ns xvs (sem_env_v env))) env)`;;

let extend_env_v_rcons = prove
 (`!ns xvs n xv env_v.
     LENGTH ns = LENGTH xvs ==>
     extend_env_v (APPEND ns [n]) (APPEND xvs [xv]) env_v =
     nsBind n xv (extend_env_v ns xvs env_v)`,
  CHEAT_TAC);;

let extend_env_v_zip = prove
 (`!ns xvs env_v.
    LENGTH ns = LENGTH xvs ==>
    extend_env_v ns xvs env_v = nsAppend (alist_to_ns (ZIP (REVERSE ns)
      (REVERSE xvs))) env_v`,
  CHEAT_TAC);;

(* [build_rec_env_aux] *)
let build_rec_env_aux_def = new_definition
  `build_rec_env_aux funs (fs:(mlstring#mlstring#ast_exp) list) env add_to_env
  =
     ITLIST
       (\(f,x,e) env'. nsBind f (semanticPrimitives_Recclosure env funs f)
         env')
       fs
       add_to_env`;;

(* [local] *)
let build_rec_env_zip_aux = prove
 (`!(fs:(mlstring#mlstring#ast_exp) list) funs env env_v.
     nsAppend (alist_to_ns
       (ZIP (MAP (\(f,_,_). f) fs)
          (MAP (\(f,_,_). naryRecclosure env (letrec_pull_params funs) f)
            fs)))
       env_v =
     ITLIST (\(f,x,e) env'. nsBind f (semanticPrimitives_Recclosure env
       funs f) env') fs env_v`,
  CHEAT_TAC);;

let build_rec_env_zip = prove
 (`!funs env env_v.
     nsAppend (alist_to_ns
       (ZIP (MAP (\(f,_,_). f) funs)
          (MAP (\(f,_,_). naryRecclosure env (letrec_pull_params funs) f)
            funs)))
       env_v =
     semanticPrimitives_build_rec_env funs env env_v`,
  CHEAT_TAC);;

(* [extend_env_rec] *)
let extend_env_v_rec_def = new_definition
  `extend_env_v_rec rec_ns rec_xvs ns xvs env_v =
     extend_env_v ns xvs (nsAppend (alist_to_ns (ZIP rec_ns rec_xvs))
       env_v)`;;

let extend_env_rec_def = new_definition
  `extend_env_rec rec_ns rec_xvs ns xvs (env:'v sem_env) = sem_env_v_fupd (K
  (extend_env_v_rec rec_ns rec_xvs ns xvs (sem_env_v env)))
     env`;;

let extend_env_rec_build_rec_env = prove
 (`!funs env env_v.
     extend_env_v_rec (MAP (\(f,_,_). f) funs) (MAP (\(f,_,_).
       naryRecclosure env (letrec_pull_params funs) f) funs)
       [] [] env_v =
     semanticPrimitives_build_rec_env funs env env_v`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(** Pattern matching.

    Restrictions:
    - the CakeML pattern-matching must "typecheck" (does not raise
      Match_type_error)
    - patterns that use [Pref] are not currently supported
*)

(* HOL4 cfScript.sml:482: ML code, not ported *)

(* [pat_wildcards]: computes the number of wildcards a pattern contains. *)

(* the termination relation that HOL4 gives is
     MEASURE ast_pat_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
let pat_wildcards_def,pat_wildcards_ind = define_guess
  `(pat_wildcards ast_Pany = 1) /\
   (pat_wildcards (ast_Pvar _) = 0) /\
   (pat_wildcards (ast_Plit _) = 0) /\
   (pat_wildcards (ast_Pref _) = 0) /\
   (pat_wildcards (ast_Pcon _ args) = pats_wildcards args) /\
   (pat_wildcards (ast_Ptannot p _) = pat_wildcards p) /\
   (pat_wildcards (ast_Pas p _) = pat_wildcards p) /\
   (pats_wildcards [] = 0) /\
   (pats_wildcards (CONS p ps) =
      (pat_wildcards p) + (pats_wildcards ps))`;;

(* [v_of_pat]: from a pattern and a list of instantiations for the pattern
   variables, produce a semantic value
*)

let v_of_matching_pat_aux_measure_def = new_definition
  `v_of_matching_pat_aux_measure x =
     sum_CASE x
       (\(_,p,_,_). ast_pat_size p)
       (\(_,ps,_,_). list_size ast_pat_size ps)`;;

(* the clauses in two quotations: args is (pat list) and (_)list; p is pat
   and varN; x is varN and pat, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE v_of_matching_pat_aux_measure
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 cfScript.sml:555-560: the tactic that proves the termination *)
let v_of_pat_def,v_of_pat_ind = define_guess_clauses
  [`(v_of_pat envC (ast_Pvar x) insts wildcards =
      (match insts with CONS xv rest -> SOME (xv,rest,wildcards)
         | _ -> NONE)) /\
    // unsupported
    (v_of_pat envC ast_Pany insts wildcards =
      (match wildcards with CONS xv rest -> SOME (xv,insts,rest)
         | _ -> NONE)) /\
    (v_of_pat envC (ast_Plit l) insts wildcards =
      SOME (semanticPrimitives_Litv l,insts,wildcards)) /\
    (v_of_pat envC (ast_Pcon c args) insts wildcards =
      (match v_of_pat_list envC args insts wildcards with
           SOME (argsv,insts_rest,wildcards_rest) ->
           (match c with
                NONE -> SOME (semanticPrimitives_Conv NONE
                    argsv,insts_rest,wildcards_rest)
              | SOME id ->
                (match nsLookup envC id with
                    NONE -> NONE
                  | SOME (len,t) ->
                    if len = LENGTH argsv then
                      SOME (semanticPrimitives_Conv (SOME t)
                          argsv,insts_rest,wildcards_rest)
                    else NONE))
        | NONE -> NONE)) /\
    (v_of_pat _ (ast_Pref pat) _ _ =
      NONE) /\
    // unsupported
    (v_of_pat envC (ast_Ptannot p _) insts wildcards =
      v_of_pat envC p insts wildcards) /\
    (v_of_pat _ _ _ _ = NONE) /\
    (v_of_pat_list _ [] insts wildcards = SOME ([],insts,wildcards)) /\
    (v_of_pat_list envC (CONS p argspat) insts wildcards =
      (match v_of_pat envC p insts wildcards with
           SOME (v,insts_rest,wildcards_rest) ->
           (match v_of_pat_list envC argspat insts_rest wildcards_rest with
                SOME (vs,insts_rest',wildcards_rest') ->
                  SOME (CONS v vs,insts_rest',wildcards_rest')
              | NONE -> NONE)
         | NONE -> NONE)) /\
    (v_of_pat_list _ _ _ _ = NONE)`;
   `v_of_pat envC (ast_Pas x p) insts wildcards =
      NONE`];;

let v_of_pat_list_length = prove
 (`!envC pats insts wildcards vs rest.
      v_of_pat_list envC pats insts wildcards = SOME (vs,rest,wrest) ==>
      LENGTH pats = LENGTH vs`,
  CHEAT_TAC);;

let v_of_pat_insts_length = prove
 (`(!envC pat insts wildcards v insts_rest wildcards_rest.
       v_of_pat envC pat insts wildcards = SOME
         (v,insts_rest,wildcards_rest) ==>
       (LENGTH insts = LENGTH (ast_pat_bindings pat) + LENGTH insts_rest))
         /\
    (!envC pats insts wildcards vs insts_rest wildcards_rest.
       v_of_pat_list envC pats insts wildcards = SOME
         (vs,insts_rest,wildcards_rest) ==>
       (LENGTH insts = LENGTH (ast_pats_bindings pats) + LENGTH
         insts_rest))`,
  CHEAT_TAC);;

let v_of_pat_wildcards_count = prove
 (`(!envC pat insts wildcards v insts_rest wildcards_rest.
       v_of_pat envC pat insts wildcards = SOME
         (v,insts_rest,wildcards_rest) ==>
       (LENGTH wildcards = pat_wildcards pat + LENGTH wildcards_rest)) /\
    (!envC pats insts wildcards vs insts_rest wildcards_rest.
       v_of_pat_list envC pats insts wildcards = SOME
         (vs,insts_rest,wildcards_rest) ==>
       (LENGTH wildcards = pats_wildcards pats + LENGTH wildcards_rest))`,
  CHEAT_TAC);;

let v_of_pat_extend_insts = prove
 (`(!envC pat insts wildcards v rest wildcards_rest insts'.
       v_of_pat envC pat insts wildcards = SOME (v,rest,wildcards_rest) ==>
       v_of_pat envC pat (APPEND insts insts') wildcards = SOME (v,APPEND
         rest insts',wildcards_rest)) /\
    (!envC pats insts wildcards vs rest wildcards_rest insts'.
       v_of_pat_list envC pats insts wildcards = SOME
         (vs,rest,wildcards_rest) ==>
       v_of_pat_list envC pats (APPEND insts insts') wildcards = SOME
         (vs,APPEND rest insts',wildcards_rest))`,
  CHEAT_TAC);;

let v_of_pat_extend_wildcards = prove
 (`(!envC pat insts wildcards v rest wildcards_rest wildcards'.
       v_of_pat envC pat insts wildcards = SOME (v,rest,wildcards_rest) ==>
       v_of_pat envC pat insts (APPEND wildcards wildcards') = SOME
         (v,rest,APPEND wildcards_rest wildcards')) /\
    (!envC pats insts wildcards vs rest wildcards_rest wildcards'.
       v_of_pat_list envC pats insts wildcards = SOME
         (vs,rest,wildcards_rest) ==>
       v_of_pat_list envC pats insts (APPEND wildcards wildcards') = SOME
         (vs,rest,APPEND wildcards_rest wildcards'))`,
  CHEAT_TAC);;

let v_of_pat_NONE_extend_insts = prove
 (`(!envC pat insts wildcards insts'.
       v_of_pat envC pat insts wildcards = NONE ==>
       LENGTH insts >= LENGTH (ast_pat_bindings pat) ==>
       LENGTH wildcards >= pat_wildcards pat ==>
       v_of_pat envC pat (APPEND insts insts') wildcards = NONE) /\
    (!envC pats insts wildcards insts'.
       v_of_pat_list envC pats insts wildcards = NONE ==>
       LENGTH insts >= LENGTH (ast_pats_bindings pats) ==>
       LENGTH wildcards >= pats_wildcards pats ==>
       v_of_pat_list envC pats (APPEND insts insts') wildcards = NONE)`,
  CHEAT_TAC);;

let v_of_pat_remove_rest_insts = prove
 (`(!pat envC insts wildcards v rest wildcards_rest.
       v_of_pat envC pat insts wildcards = SOME (v,rest,wildcards_rest) ==>
       (?insts'.
         insts = APPEND insts' rest /\
         LENGTH insts' = LENGTH (ast_pat_bindings pat) /\
         v_of_pat envC pat insts' wildcards = SOME (v,[],wildcards_rest)))
           /\
    (!pats envC insts wildcards vs rest wildcards_rest.
       v_of_pat_list envC pats insts wildcards = SOME
         (vs,rest,wildcards_rest) ==>
       (?insts'.
         insts = APPEND insts' rest /\
         LENGTH insts' = LENGTH (ast_pats_bindings pats) /\
         v_of_pat_list envC pats insts' wildcards = SOME
           (vs,[],wildcards_rest)))`,
  CHEAT_TAC);;

let v_of_pat_insts_unique = prove
 (`(!envC pat insts wildcards rest wildcards_rest v.
       v_of_pat envC pat insts wildcards = SOME (v,rest,wildcards_rest) ==>
       (!insts' wildcards'. v_of_pat envC pat insts' wildcards' = SOME
         (v,rest,wildcards_rest) <=> (insts' = insts /\ wildcards' =
         wildcards))) /\
    (!envC pats insts wildcards rest wildcards_rest vs.
       v_of_pat_list envC pats insts wildcards = SOME
         (vs,rest,wildcards_rest) ==>
       (!insts' wildcards'. v_of_pat_list envC pats insts' wildcards' =
         SOME (vs,rest,wildcards_rest) <=> (insts' = insts /\ wildcards' =
         wildcards)))`,
  CHEAT_TAC);;

(* [v_of_pat_norest]: Wrapper that checks that there are no remaining
   instantiations and wildcards instantiations
*)

let v_of_pat_norest_def = new_definition
  `v_of_pat_norest envC pat insts wildcards =
     match v_of_pat envC pat insts wildcards with
         SOME (v,[],[]) -> SOME v
       | _ -> NONE`;;

let v_of_pat_norest_insts_length = prove
 (`!envC pat insts wildcards v.
      v_of_pat_norest envC pat insts wildcards = SOME v ==>
      LENGTH insts = LENGTH (ast_pat_bindings pat)`,
  CHEAT_TAC);;

let v_of_pat_norest_wildcards_count = prove
 (`!envC pat insts wildcards v.
      v_of_pat_norest envC pat insts wildcards = SOME v ==>
      LENGTH wildcards = pat_wildcards pat`,
  CHEAT_TAC);;

let v_of_pat_norest_insts_unique = prove
 (`!envC pat insts wildcards v.
      v_of_pat_norest envC pat insts wildcards = SOME v ==>
      (!insts' wildcards'. v_of_pat_norest envC pat insts' wildcards' =
        SOME v <=> (insts' = insts /\ wildcards' = wildcards))`,
  CHEAT_TAC);;

(* Predicates that discriminate the patterns we want to deal
   with. [validate_pat] packs them all up.
*)

(* might be wrong *)
let pat_typechecks_def = new_definition
  `pat_typechecks envC s pat v =
     (~(semanticPrimitives_pmatch envC s pat v [] = Match_type_error))`;;

(* the termination relation that HOL4 gives is
     MEASURE ast_pat_size
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 cfScript.sml:831-836: the tactic that proves the termination *)
let pat_without_Pref_Pas_def,pat_without_Pref_Pas_ind = define_guess
  `pat_without_Pref_Pas x1 =
   match x1 with
     ast_Pcon _ args -> ALL pat_without_Pref_Pas args
   | ast_Pref _ -> F
   | ast_Ptannot p _ -> pat_without_Pref_Pas p
   | ast_Pas p _ -> F
   | _ -> T`;;

let validate_pat_def = new_definition
  `validate_pat envC s pat v env =
     (pat_typechecks envC s pat v /\
      pat_without_Pref_Pas pat /\
      ALL_DISTINCT (ast_pat_bindings pat))`;;

(* Lemmas that relate [v_of_pat] and [pmatch], the pattern-matching function
   from the semantics.
*)

let same_type_EQ_same_ctor = prove
 (`same_type r r <=> same_ctor r r`,
  CHEAT_TAC);;
add_simp same_type_EQ_same_ctor;;

let same_ctor_REFL = prove
 (`same_ctor r r`,
  CHEAT_TAC);;
add_simp same_ctor_REFL;;

let v_of_pat_pmatch = prove
 (`(!envC s pat v env_v insts wildcards wildcards_rest.
      v_of_pat envC pat insts wildcards = SOME (v,[],wildcards_rest) ==>
      semanticPrimitives_pmatch envC s pat v env_v = Match
        (APPEND (ZIP (ast_pat_bindings pat) (REVERSE insts)) env_v)) /\
    (!envC s pats vs env_v insts wildcards wildcards_rest.
      v_of_pat_list envC pats insts wildcards = SOME (vs,[],wildcards_rest)
        ==>
      semanticPrimitives_pmatch_list envC s pats vs env_v = Match
        (APPEND (ZIP (ast_pats_bindings pats) (REVERSE insts)) env_v))`,
  CHEAT_TAC);;

let v_of_pat_norest_pmatch = prove
 (`!envC s pat v env_v insts wildcards.
     v_of_pat_norest envC pat insts wildcards = SOME v ==>
     semanticPrimitives_pmatch envC s pat v env_v = Match
       (APPEND (ZIP (ast_pat_bindings pat) (REVERSE insts)) env_v)`,
  CHEAT_TAC);;

let pmatch_v_of_pat = prove
 (`(!envC s pat v env_v env_v'.
      semanticPrimitives_pmatch envC s pat v env_v = Match env_v' ==>
      pat_without_Pref_Pas pat ==>
      (?insts wildcards.
        env_v' = APPEND (ZIP (ast_pat_bindings pat) (REVERSE insts)) env_v
          /\
        v_of_pat envC pat insts wildcards = SOME (v,[],[]))) /\
    (!envC s pats vs env_v env_v'.
      semanticPrimitives_pmatch_list envC s pats vs env_v = Match env_v' ==>
      ALL (\pat. pat_without_Pref_Pas pat) pats ==>
      (?insts wildcards.
        env_v' = APPEND (ZIP (ast_pats_bindings pats) (REVERSE insts)) env_v
          /\
        v_of_pat_list envC pats insts wildcards = SOME (vs,[],[])))`,
  CHEAT_TAC);;

let pmatch_v_of_pat_norest = prove
 (`!envC s pat v env_v env_v'.
      semanticPrimitives_pmatch envC s pat v env_v = Match env_v' ==>
      pat_without_Pref_Pas pat ==>
      (?insts wildcards.
        env_v' = APPEND (ZIP (ast_pat_bindings pat) (REVERSE insts)) env_v
          /\
        v_of_pat_norest envC pat insts wildcards = SOME v)`,
  CHEAT_TAC);;

(* The nested ifs corresponding to a list of patterns *)

let cf_cases_def,cf_cases_ind = define_guess
  `(cf_cases v nomatch_exn [] env H Q =
      local (\H Q. SEP_IMP H (Q (cfHeapsBase_Exn nomatch_exn))) H Q) /\
   (cf_cases v nomatch_exn (CONS (pat,row_cf) rows) env H Q =
      local (\H Q.
        ((if (?insts wildcards. v_of_pat_norest (sem_env_c env) pat insts
            wildcards = SOME v) then
            (!insts wildcards. v_of_pat_norest (sem_env_c env) pat insts
                wildcards = SOME v ==>
               can_pmatch_all (sem_env_c env) [] (MAP FST rows) v /\
               row_cf (cf_extend_env (REVERSE (ast_pat_bindings pat)) insts
                   env) H Q)
          else cf_cases v nomatch_exn rows env H Q) /\
         (!s. validate_pat (sem_env_c env) s pat v (sem_env_v env))))
             H Q)`;;

(* HOL4 cfScript.sml:1011-1019: a proof *)

let cf_cases_local = prove
 (`!v nomatch_exn rows env.
      is_local (cf_cases v nomatch_exn rows env)`,
  CHEAT_TAC);;


(*------------------------------------------------------------------*)
(* Soundness predicate & lemmas *)

(* States that a hoare triple {H} e {Q} is valid in environment [env] *)
let htriple_valid_def = new_definition
  `htriple_valid (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e env H Q
  =
     (!st h_i h_k.
       SPLIT (st2heap p st) (h_i,h_k) ==>
       H h_i ==>
       (?r h_f h_g heap.
         SPLIT3 heap (h_f,h_k,h_g) /\ Q r h_f /\
         evaluate_to_heap st env e p heap r))`;;

(* Not used, but interesting: app_basic as an instance of htriple_valid *)
let app_basic_iff_htriple_valid = prove
 (`!env exp. semanticPrimitives_do_opapp [fv; argv] = SOME (env,exp) ==>
   (app_basic p fv argv H Q <=> htriple_valid p exp env H Q)`,
  CHEAT_TAC);;

let app_basic_eq_htriple_valid = prove
 (`app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
  (f:semanticPrimitives_v) (x:semanticPrimitives_v) H Q <=>
    (match semanticPrimitives_do_opapp [f; x] with
       SOME (env,exp) -> htriple_valid p exp env H Q
     | NONE -> (!st h1 h2. SPLIT (st2heap p st) (h1,h2) ==> ~(H h1)))`,
  CHEAT_TAC);;

(* Soundness for relation [R] *)
let sound_def = new_definition
  `sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e R' =
     (!env H Q.
       R' env H Q ==>
       htriple_valid p e env H Q)`;;

(* [local] *)
let star_split = prove
 (`!H1 H2 H3 H4 h1 h2 h3 h4.
     ((H1 * H2) (h1 UNION h2) ==> (H3 * H4) (h3 UNION h4)) ==>
     DISJOINT h1 h2 ==> H1 h1 ==> H2 h2 ==>
     (?u v. H3 u /\ H4 v /\ SPLIT (h3 UNION h4) (u,v))`,
  CHEAT_TAC);;

let sound_local = prove
 (`!e R'. sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e R' ==>
  sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e (\env.
  local (R' env))`,
  CHEAT_TAC);;

let sound_false = prove
 (`!e. sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e (\env
  H Q. F)`,
  CHEAT_TAC);;

(* [local] *)
let sound_local_false = prove
 (`!e. sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e (\env.
  local (\H Q. F))`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* Lemmas relating [app], and [htriple_valid] (usually on the
   expression composing the body of the applied function).
*)

(* [local] *)
let app_basic_of_htriple_valid = prove
 (`!clos body x env v H Q.
     semanticPrimitives_do_opapp [clos; x] = SOME (env,body) ==>
     htriple_valid (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) body env H Q ==>
     app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) clos x H Q`,
  CHEAT_TAC);;

(* [local] *)
let app_of_htriple_valid = prove
 (`!ns xvs env body H Q. ~(ns = []) ==>
     LENGTH ns = LENGTH xvs ==>
     htriple_valid (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) body (cf_extend_env ns xvs env) H
       Q ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryClosure env ns body) xvs H Q`,
  CHEAT_TAC);;

(* [local] *)
let app_rec_of_htriple_valid_aux = prove
 (`!f body params' xvs funs naryfuns env H Q fvs. ~(params' = []) ==>
     LENGTH params' = LENGTH xvs ==>
     naryfuns = letrec_pull_params funs ==>
     ALL_DISTINCT (MAP (\(f,_,_). f) naryfuns) ==>
     find_recfun f naryfuns = SOME (params',body) ==>
     htriple_valid (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) body
       (extend_env_rec (MAP (\(f,_,_). f) naryfuns) fvs params' xvs env)
       H Q ==>
     fvs = MAP (\(f,_,_). naryRecclosure env naryfuns f) naryfuns ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryRecclosure env naryfuns f) xvs H Q`,
  CHEAT_TAC);;

(* [local] *)
let app_rec_of_htriple_valid = prove
 (`!f params' body funs xvs env H Q. ~(params' = []) ==>
     LENGTH params' = LENGTH xvs ==>
     ALL_DISTINCT (MAP (\(f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (params',body) ==>
     htriple_valid (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) body
       (extend_env_rec
          (MAP (\(f,_,_). f) funs)
          (MAP (\(f,_,_). naryRecclosure env (letrec_pull_params funs) f)
            funs)
          params' xvs env)
        H Q ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryRecclosure env (letrec_pull_params funs) f) xvs H Q`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* Lemmas used in the soundness proof of FFI *)

let SPLIT_SING_2 = prove
 (`SPLIT s (x,{y}) <=> (s = y INSERT x) /\ ~(y IN x)`,
  CHEAT_TAC);;

(* [local] *)
let SUBSET_IN = prove
 (`!s t x. s SUBSET t /\ x IN s ==> x IN t`,
  CHEAT_TAC);;

let SPLIT_FFI_SET_IMP_DISJOINT = prove
 (`SPLIT (st2heap p st) (c,{cfHeapsBase_FFI_part s u ns ts}) ==>
    (!s1 ts1. ~(cfHeapsBase_FFI_part s1 u ns ts1 IN c))`,
  CHEAT_TAC);;

let SPLIT_IMP_Mem_NOT_IN = prove
 (`SPLIT (st2heap p st) ({cfHeapsBase_Mem y xs},c) ==>
    (!ys. ~(cfHeapsBase_Mem y ys IN c))`,
  CHEAT_TAC);;

let FLOOKUP_FUPDATE_LIST = prove
 (`!ns f. FLOOKUP (f |++ MAP (\n. (n,s)) ns) m =
           if MEM m ns then SOME s else FLOOKUP f m`,
  CHEAT_TAC);;

(* ALL_DISTINCT_FLAT_MEM_IMP *)
let cf_ALL_DISTINCT_FLAT_MEM_IMP = prove
 (`!p2. ALL_DISTINCT (FLAT p2) /\ MEM ns' p2 /\ MEM ns p2 /\
         MEM m ns' /\ MEM m ns ==> ns = ns'`,
  CHEAT_TAC);;

let ALL_DISTINCT_FLAT_FST_IMP = prove
 (`!p2. ALL_DISTINCT (FLAT (MAP FST p2)) /\
         MEM (ns,u') p2 /\ MEM (ns,u) p2 /\ ~(ns = []) ==> u = u'`,
  CHEAT_TAC);;

(*------------------------------------------------------------------*)
(* Definition of the [cf] functions, that generates the characteristic
   formula of a cakeml expression *)

let app_ref_def = new_definition
  `app_ref (x:semanticPrimitives_v) H Q =
     (!r. SEP_IMP (H * REF r x) (Q (cfHeapsBase_Val r)))`;;

let app_assign_def = new_definition
  `app_assign r (x:semanticPrimitives_v) H Q =
     (?x' F'.
        (SEP_IMP H (F' * REF r x')) /\
        (SEP_IMP (F' * REF r x) (Q (cfHeapsBase_Val
          (semanticPrimitives_Conv NONE [])))))`;;

let app_deref_def = new_definition
  `app_deref r H Q =
     (?x F'.
        (SEP_IMP H (F' * REF r x)) /\
        (SEP_IMP H (Q (cfHeapsBase_Val x))))`;;

let app_aalloc_def = new_definition
  `app_aalloc (n:int) v H Q =
     (!a.
        n >= (&0) /\
        (SEP_IMP (H * ARRAY a (REPLICATE (num_of_int n) v)) (Q
          (cfHeapsBase_Val a))))`;;

let app_asub_def = new_definition
  `app_asub a (i:int) H Q =
     (?vs F'.
        (&0) <= i /\ (num_of_int i) < LENGTH vs /\
        (SEP_IMP H (F' * ARRAY a vs)) /\
        (SEP_IMP H (Q (cfHeapsBase_Val (EL (num_of_int i) vs)))))`;;

let app_alength_def = new_definition
  `app_alength a H Q =
     (?vs F'.
        (SEP_IMP H (F' * ARRAY a vs)) /\
        (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv
          (ast_IntLit (&(LENGTH vs))))))))`;;

let app_aupdate_def = new_definition
  `app_aupdate a (i:int) v H Q =
     (?vs F'.
        (&0) <= i /\ (num_of_int i) < LENGTH vs /\
        (SEP_IMP H (F' * ARRAY a vs)) /\
        (SEP_IMP (F' * ARRAY a (LUPDATE v (num_of_int i) vs)) (Q
          (cfHeapsBase_Val (semanticPrimitives_Conv NONE [])))))`;;

let app_aw8alloc_def = new_definition
  `app_aw8alloc (n:int) w H Q =
     (!a.
        n >= (&0) /\
        (SEP_IMP (H * W8ARRAY a (REPLICATE (num_of_int n) w)) (Q
          (cfHeapsBase_Val a))))`;;

let app_aw8sub_def = new_definition
  `app_aw8sub a (i:int) H Q =
     (?ws F'.
        (&0) <= i /\ (num_of_int i) < LENGTH ws /\
        (SEP_IMP H (F' * W8ARRAY a ws)) /\
        (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv
          (ast_Word8 (EL (num_of_int i) ws)))))))`;;

let app_aw8length_def = new_definition
  `app_aw8length a H Q =
     (?ws F'.
        (SEP_IMP H (F' * W8ARRAY a ws)) /\
        (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv
          (ast_IntLit (&(LENGTH ws))))))))`;;

let app_aw8update_def = new_definition
  `app_aw8update a (i:int) w H Q =
     (?ws F'.
        (&0) <= i /\ (num_of_int i) < LENGTH ws /\
        (SEP_IMP H (F' * W8ARRAY a ws)) /\
        (SEP_IMP (F' * W8ARRAY a (LUPDATE w (num_of_int i) ws)) (Q
          (cfHeapsBase_Val (semanticPrimitives_Conv NONE [])))))`;;

let app_copyaw8aw8_def = new_definition
  `app_copyaw8aw8 s so l d do' H Q =
     (?ws wd F'.
        (&0) <= do' /\ (&0) <= so /\ (&0) <= l /\
        (num_of_int do' + num_of_int l) <= LENGTH wd /\ (num_of_int so +
          num_of_int l) <= LENGTH ws /\
        (SEP_IMP H (F' * W8ARRAY s ws * W8ARRAY d wd)) /\
        (
         SEP_IMP (F' * W8ARRAY s ws *
             W8ARRAY d (APPEND (APPEND (TAKE (num_of_int do') wd)
                        (TAKE (num_of_int l) (DROP (num_of_int so) ws)))
                        (DROP (num_of_int do' + num_of_int l) wd))) (Q
                          (cfHeapsBase_Val (semanticPrimitives_Conv NONE
                          [])))))`;;

let app_copystraw8_def = new_definition
  `app_copystraw8 s so l d do' H Q =
     (?wd F'.
        (&0) <= do' /\ (&0) <= so /\ (&0) <= l /\
        (num_of_int do' + num_of_int l) <= LENGTH wd /\ (num_of_int so +
          num_of_int l) <= strlen s /\
        (SEP_IMP H (F' * W8ARRAY d wd)) /\
        (
             SEP_IMP (F' * W8ARRAY d (APPEND (APPEND (TAKE (num_of_int do')
               wd)
                        (MAP (n2w o ORD) (TAKE (num_of_int l) (DROP
                          (num_of_int so) (explode s)))))
                        (DROP (num_of_int do' + num_of_int l) wd))) (Q
                          (cfHeapsBase_Val (semanticPrimitives_Conv NONE
                          [])))))`;;

let app_copyaw8str_def = new_definition
  `app_copyaw8str s so l H Q =
     (?ws F'.
        (&0) <= so /\ (&0) <= l /\
        (num_of_int so + num_of_int l) <= LENGTH ws /\
        (SEP_IMP H (F' * W8ARRAY s ws)) /\
        (
         SEP_IMP (F' * W8ARRAY s ws) (Q (cfHeapsBase_Val
           (semanticPrimitives_Litv (ast_StrLit (implode (MAP (CHR o w2n)
           (TAKE (num_of_int l) (DROP (num_of_int so) ws))))))))))`;;

let app_xoraw8str_def = new_definition
  `app_xoraw8str s d H Q =
     (?wd F'.
        strlen s <= LENGTH wd /\
        (SEP_IMP H (F' * W8ARRAY d wd)) /\
        (
               SEP_IMP (F' * W8ARRAY d (THE (xor_bytes (MAP (n2w o ORD)
                 (explode s)) wd))) (Q (cfHeapsBase_Val
                 (semanticPrimitives_Conv NONE [])))))`;;

let app_wordFromInt_W8_def = new_definition
  `app_wordFromInt_W8 (i:int) H Q =
     (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv (ast_Word8
       (i2w i))))))`;;

let app_wordFromInt_W64_def = new_definition
  `app_wordFromInt_W64 (i:int) H Q =
     (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv (ast_Word64
       (i2w i))))))`;;

let app_wordToInt_def = new_definition
  `app_wordToInt w H Q =
     (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv (ast_IntLit
       (&(w2n w)))))))`;;

let app_arith_def = new_definition
  `app_arith arith i1 i2 H Q =
     ((if arith = cfHeapsBase_Div \/ arith = ast_Mod then ~(i2 = 0) else T)
       /\
      MEM arith [ast_Add; ast_Sub; ast_Mul; cfHeapsBase_Div; ast_Mod]
        /\ SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv (ast_IntLit
        (match arith with ast_Add -> i1 + i2
                              | ast_Sub -> i1 - i2
                              | ast_Mul -> i1 * i2
                              | ast_Div -> i1 / i2
                              | ast_Mod -> i1 % i2
                              | _ -> (&0)))))) /\ SEP_IMPPOSTv_inv Q
                                POST_F)`;;

let app_int_cmp_def = new_definition
  `app_int_cmp cmp i1 i2 H Q =
     (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Boolv
       (semanticPrimitives_int_cmp cmp i1 i2)))))`;;

let app_equality_def = new_definition
  `app_equality v1 v2 H Q =
     (no_closures v1 /\ no_closures v2 /\
      types_match v1 v2 /\ SEP_IMP H (Q (cfHeapsBase_Val
        (semanticPrimitives_Boolv (v1 = v2)))))`;;

let cf_lit_def = new_definition
  `cf_lit l = (\(env:semanticPrimitives_v sem_env). local (\H Q. SEP_IMP H
  (Q (cfHeapsBase_Val (semanticPrimitives_Litv l)))))`;;

let cf_con_def = new_definition
  `cf_con cn args = (\env. local (\H Q.
     (?argsv cv.
        do_con_check (sem_env_c env) cn (LENGTH args) /\
        (build_conv (sem_env_c env) cn argsv = SOME cv) /\
        (exp2v_list env args = SOME argsv) /\ SEP_IMP H (Q
          (cfHeapsBase_Val cv)))))`;;

let cf_var_def = new_definition
  `cf_var name = (\env. local (\H Q.
     (?v.
        nsLookup (sem_env_v env) name = SOME v /\ SEP_IMP H (Q
          (cfHeapsBase_Val v)))))`;;

let cf_let_def = new_definition
  `cf_let n F1 F2 = (\env. local (\H Q.
     ?Q'. (F1 env H Q' /\ SEP_IMPPOSTv_inv Q' Q) /\
          (!xv. F2 (sem_env_v_fupd (K (nsOptBind n xv (sem_env_v env)))
            env) (Q' (cfHeapsBase_Val xv)) Q)))`;;

let cf_arith_def = new_definition
  `cf_arith arith x1 x2 = (\env. local (\H Q.
     ?i1 i2.
       exp2v env x1 = SOME (semanticPrimitives_Litv (ast_IntLit i1)) /\
       exp2v env x2 = SOME (semanticPrimitives_Litv (ast_IntLit i2)) /\
       app_arith arith i1 i2 H Q))`;;

let cf_int_cmp_def = new_definition
  `cf_int_cmp cmp x1 x2 = (\env. local (\H Q.
     ?i1 i2.
       exp2v env x1 = SOME (semanticPrimitives_Litv (ast_IntLit i1)) /\
       exp2v env x2 = SOME (semanticPrimitives_Litv (ast_IntLit i2)) /\
       app_int_cmp cmp i1 i2 H Q))`;;

let cf_equality_def = new_definition
  `cf_equality x1 x2 = (\env. local (\H Q.
     ?v1 v2.
       exp2v env x1 = SOME v1 /\
       exp2v env x2 = SOME v2 /\
       app_equality v1 v2 H Q))`;;

let cf_app_def = new_definition
  `cf_app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f args =
  (\env. local (\H Q.
     ?fv' argsv.
       exp2v env f = SOME fv' /\
       exp2v_list env args = SOME argsv /\
       app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
         list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
         fv' argsv H Q))`;;

let cf_fun_def = new_definition
  `cf_fun (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) f ns F1 F2
  = (\env. local (\H Q.
     !fv'.
       curried (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
         list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
         (LENGTH ns) fv' /\
       (!xvs H' Q'.
         LENGTH xvs = LENGTH ns ==>
         F1 (cf_extend_env ns xvs env) H' Q' ==>
         app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
           list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
           fv' xvs H' Q') ==>
       F2 (sem_env_v_fupd (K (nsBind f fv' (sem_env_v env))) env) H Q))`;;

let fun_rec_aux_def,fun_rec_aux_ind = define_guess
  `fun_rec_aux x1 fs fvs x4 x5 x6 F2 env H Q =
   match (x1,x4,x5,x6) with
     ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
       list),[],[],[]) ->
     (F2 (extend_env_rec fs fvs [] [] env) H Q)
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),CONS ns
     ns_acc,CONS fv' fv_acc,CONS Fbody Fs) ->
     (
      curried (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
        (LENGTH ns) fv' /\
      (!xvs H' Q'.
         LENGTH xvs = LENGTH ns ==>
         Fbody (extend_env_rec fs fvs ns xvs env) H' Q' ==>
         app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
           list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
           fv' xvs H' Q') ==>
      (fun_rec_aux (p:('ffi->(mlstring,ffi)fmap)#(mlstring
        list#(mlstring->word8 list->word8 list->ffi->(ffi
        cfHeapsBase_ffi_result) option)) list) fs fvs ns_acc fv_acc Fs F2 env H
        Q))
   | (_,_,_,_) -> F`;;

let cf_fun_rec_def = new_definition
  `cf_fun_rec (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) fs_Fs F2 =
  (\env. local (\H Q.
     let fs = MAP (\((f:mlstring#mlstring list#ast_exp),_). f) fs_Fs in
     let Fs = MAP (\(_,F). F) fs_Fs in
     let f_names = MAP (\(f,_,_). f) fs in
     let f_args = MAP (\(_,ns,_). ns) fs in
     !(fvs:semanticPrimitives_v list).
       LENGTH fvs = LENGTH fs ==>
       ALL_DISTINCT f_names /\
       fun_rec_aux (p:('ffi->(mlstring,ffi)fmap)#(mlstring
         list#(mlstring->word8 list->word8 list->ffi->(ffi
         cfHeapsBase_ffi_result) option)) list) f_names fvs f_args fvs Fs F2
         env H Q))`;;

let cf_ref_def = new_definition
  `cf_ref x = (\env. local (\H Q.
     ?xv.
       exp2v env x = SOME xv /\
       app_ref xv H Q))`;;

let cf_assign_def = new_definition
  `cf_assign r x = (\env. local (\H Q.
     ?rv xv.
       exp2v env r = SOME rv /\
       exp2v env x = SOME xv /\
       app_assign rv xv H Q))`;;

let cf_deref_def = new_definition
  `cf_deref r = (\env. local (\H Q.
     ?rv.
       exp2v env r = SOME rv /\
       app_deref rv H Q))`;;

let cf_aalloc_def = new_definition
  `cf_aalloc xn xv = (\env. local (\H Q.
     ?n v.
       exp2v env xn = SOME (semanticPrimitives_Litv (ast_IntLit n)) /\
       exp2v env xv = SOME v /\
       app_aalloc n v H Q))`;;

let cf_aalloc_empty_def = new_definition
  `cf_aalloc_empty xu = (\env. local (\H Q.
     exp2v env xu = SOME (semanticPrimitives_Conv NONE []) /\
     app_aalloc (&0) (semanticPrimitives_Litv (ast_IntLit (&0))) H Q))`;;

let cf_asub_def = new_definition
  `cf_asub xa xi = (\env. local (\H Q.
     ?a i.
       exp2v env xa = SOME a /\
       exp2v env xi = SOME (semanticPrimitives_Litv (ast_IntLit i)) /\
       app_asub a i H Q))`;;

let cf_alength_def = new_definition
  `cf_alength xa = (\env. local (\H Q.
     ?a.
       exp2v env xa = SOME a /\
       app_alength a H Q))`;;

let cf_aupdate_def = new_definition
  `cf_aupdate xa xi xv = (\env. local (\H Q.
     ?a i v.
       exp2v env xa = SOME a /\
       exp2v env xi = SOME (semanticPrimitives_Litv (ast_IntLit i)) /\
       exp2v env xv = SOME v /\
       app_aupdate a i v H Q))`;;

let cf_aw8alloc_def = new_definition
  `cf_aw8alloc xn xw = (\env. local (\H Q.
     ?n w.
       exp2v env xn = SOME (semanticPrimitives_Litv (ast_IntLit n)) /\
       exp2v env xw = SOME (semanticPrimitives_Litv (ast_Word8 w)) /\
       app_aw8alloc n w H Q))`;;

let cf_aw8sub_def = new_definition
  `cf_aw8sub xa xi = (\env. local (\H Q.
     ?a i.
       exp2v env xa = SOME a /\
       exp2v env xi = SOME (semanticPrimitives_Litv (ast_IntLit i)) /\
       app_aw8sub a i H Q))`;;

let cf_aw8length_def = new_definition
  `cf_aw8length xa = (\env. local (\H Q.
     ?a.
       exp2v env xa = SOME a /\
       app_aw8length a H Q))`;;

let cf_aw8update_def = new_definition
  `cf_aw8update xa xi xw = (\env. local (\H Q.
     ?a i w.
       exp2v env xa = SOME a /\
       exp2v env xi = SOME (semanticPrimitives_Litv (ast_IntLit i)) /\
       exp2v env xw = SOME (semanticPrimitives_Litv (ast_Word8 w)) /\
       app_aw8update a i w H Q))`;;

let cf_copyaw8aw8_def = new_definition
  `cf_copyaw8aw8 xs xso xl xd xdo = (\env. local (\H Q.
     ?s so l d do'.
       exp2v env xs = SOME s /\
       exp2v env xd = SOME d /\
       exp2v env xl = SOME (semanticPrimitives_Litv (ast_IntLit l)) /\
       exp2v env xso = SOME (semanticPrimitives_Litv (ast_IntLit so)) /\
       exp2v env xdo = SOME (semanticPrimitives_Litv (ast_IntLit do')) /\
       app_copyaw8aw8 s so l d do' H Q))`;;

let cf_copystraw8_def = new_definition
  `cf_copystraw8 xs xso xl xd xdo = (\env. local (\H Q.
     ?s so l d do'.
       exp2v env xs = SOME (semanticPrimitives_Litv (ast_StrLit s)) /\
       exp2v env xd = SOME d /\
       exp2v env xl = SOME (semanticPrimitives_Litv (ast_IntLit l)) /\
       exp2v env xso = SOME (semanticPrimitives_Litv (ast_IntLit so)) /\
       exp2v env xdo = SOME (semanticPrimitives_Litv (ast_IntLit do')) /\
       app_copystraw8 s so l d do' H Q))`;;

let cf_copyaw8str_def = new_definition
  `cf_copyaw8str xs xso xl = (\env. local (\H Q.
     ?s so l.
       exp2v env xs = SOME s /\
       exp2v env xso = SOME (semanticPrimitives_Litv (ast_IntLit so)) /\
       exp2v env xl = SOME (semanticPrimitives_Litv (ast_IntLit l)) /\
       app_copyaw8str s so l H Q))`;;

let cf_xoraw8str_def = new_definition
  `cf_xoraw8str xs xd = (\env. local (\H Q.
     ?s d.
       exp2v env xs = SOME (semanticPrimitives_Litv (ast_StrLit s)) /\
       exp2v env xd = SOME d /\
       app_xoraw8str s d H Q))`;;

let cf_wordFromInt_W8_def = new_definition
  `cf_wordFromInt_W8 xi = (\env. local (\H Q.
     ?i.
       exp2v env xi = SOME (semanticPrimitives_Litv (ast_IntLit i)) /\
       app_wordFromInt_W8 i H Q))`;;

let cf_wordFromInt_W64_def = new_definition
  `cf_wordFromInt_W64 xi = (\env. local (\H Q.
     ?i.
       exp2v env xi = SOME (semanticPrimitives_Litv (ast_IntLit i)) /\
       app_wordFromInt_W64 i H Q))`;;

let cf_wordToInt_W8_def = new_definition
  `cf_wordToInt_W8 xw = (\env. local (\H Q.
     ?w.
       exp2v env xw = SOME (semanticPrimitives_Litv (ast_Word8 w)) /\
       app_wordToInt w H Q))`;;

let cf_wordToInt_W64_def = new_definition
  `cf_wordToInt_W64 xw = (\env. local (\H Q.
     ?w.
       exp2v env xw = SOME (semanticPrimitives_Litv (ast_Word64 w)) /\
       app_wordToInt w H Q))`;;

let app_fptoword_def = new_definition
  `app_fptoword fp H Q =
   (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv (ast_Word64
     fp)))))`;;

let cf_fptoword_def = new_definition
  `cf_fptoword xd = (\env. local (\H Q.
     ?fp.
     exp2v env xd = SOME (semanticPrimitives_Litv (ast_Float64 fp)) /\
     app_fptoword fp H Q))`;;

let app_fpfromword_def = new_definition
  `app_fpfromword w H Q =
   (SEP_IMP H (Q (cfHeapsBase_Val (semanticPrimitives_Litv (ast_Float64
     w)))))`;;

let cf_fpfromword_def = new_definition
  `cf_fpfromword xw = (\env. local (\H Q.
     ?w.
     exp2v env xw = SOME (semanticPrimitives_Litv (ast_Word64 w)) /\
     app_fpfromword w H Q))`;;

let app_ffi_def = new_definition
  `app_ffi ffi_index c a H Q =
     ((?conf ws frame s u ns events.
          MEM ffi_index ns /\
          c = semanticPrimitives_Litv (ast_StrLit (implode (MAP (CHR o w2n)
            conf))) /\
          (SEP_IMP H (frame * W8ARRAY a ws * set_sep_one
            (cfHeapsBase_FFI_part s u ns events) *
                  cond (~(MEM (implode "") ns)))) /\
          (match u ffi_index conf ws s with
             SOME (FFIreturn vs s') -> SEP_IMP (frame * W8ARRAY a vs *
               set_sep_one (cfHeapsBase_FFI_part s' u ns
                  (APPEND events [IO_event (ffi_ExtCall ffi_index) conf (ZIP
                    ws vs)])) *
               cond (~(MEM (implode "") ns))) (Q (cfHeapsBase_Val
                 (semanticPrimitives_Conv NONE [])))
           | SOME (FFIdiverge) -> SEP_IMP (frame * W8ARRAY a ws *
             set_sep_one (cfHeapsBase_FFI_part s u ns events) *
               cond (~(MEM (implode "") ns))) (Q (cfHeapsBase_FFIDiv
                 ffi_index conf ws))
           | NONE -> F)))`;;

let cf_ffi_def = new_definition
  `cf_ffi ffi_index c r = (\env. local (\H Q.
     ?conf rv.
       exp2v env r = SOME rv /\
       exp2v env c = SOME conf /\
       app_ffi ffi_index conf rv H Q))`;;

let cf_log_def = new_definition
  `cf_log lop e1 cf2 = (\env. local (\H Q.
     ?v b.
       exp2v env e1 = SOME v /\
       BOOL b v /\
       (match (lop,b) with
            (Andalso,T) -> cf2 env H Q
          | (Orelse,F) -> cf2 env H Q
          | (Orelse,T) -> (SEP_IMP H (Q (cfHeapsBase_Val v)))
          | (Andalso,F) -> (SEP_IMP H (Q (cfHeapsBase_Val v))))))`;;

let cf_if_def = new_definition
  `cf_if cond' cf1 cf2 = (\env. local (\H Q.
     ?condv b.
       exp2v env cond' = SOME condv /\
       BOOL b condv /\
       (b = T ==> cf1 env H Q) /\
       (b = F ==> cf2 env H Q)))`;;

let cf_match_def = new_definition
  `cf_match e rows = (\env. local (\H Q.
     ?v.
       exp2v env e = SOME v /\
       cf_cases v semanticPrimitives_bind_exn_v rows env H Q))`;;

let cf_raise_def = new_definition
  `cf_raise e = (\env. local (\H Q.
     ?v.
       exp2v env e = SOME v /\ SEP_IMP H (Q (cfHeapsBase_Exn v))))`;;

let cf_handle_def = new_definition
  `cf_handle Fe rows = (\env. local (\H Q.
     ?Q'.
       (Fe env H Q' /\ SEP_IMPPOSTe_inv Q' Q) /\
       (!ev. cf_cases ev ev rows env (Q' (cfHeapsBase_Exn ev)) Q)))`;;

(* the termination relation that HOL4 gives is
     MEASURE (ast_exp_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 cfScript.sml:1974-1987: the tactic that proves the termination *)
let cf_def,cf_ind = define_guess
  `cf_cf x1' x2 =
   match (x1',x2) with
     ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
       list),ast_Lit l) -> cf_lit l
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),ast_Con
     opt args) -> cf_con opt args
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),ast_Var
     name) -> cf_var name
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),ast_Let
     opt e1 e2) ->
     (if is_bound_Fun opt e1 then
        (match Fun_body e1 with SOME body ->
             cf_fun (p:('ffi->(mlstring,ffi)fmap)#(mlstring
               list#(mlstring->word8 list->word8 list->ffi->(ffi
               cfHeapsBase_ffi_result) option)) list) (THE opt) (Fun_params e1)
               (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
                 list#(mlstring->word8 list->word8 list->ffi->(ffi
                 cfHeapsBase_ffi_result) option)) list) body) (cf_cf
                 (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
                 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
                 list) e2)
           | NONE -> cf_bottom)
      else cf_let opt (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
        list#(mlstring->word8 list->word8 list->ffi->(ffi
        cfHeapsBase_ffi_result) option)) list) e1) (cf_cf
        (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
        list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e2))
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
     list),ast_Letrec funs e) ->
     (cf_fun_rec (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list)
        (MAP (\x. (x,cf_cf p (SND (SND x)))) (letrec_pull_params funs))
        (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
          list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
          e))
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),ast_App
     op args) ->
     (match op with ast_Arith arith ast_IntT ->
           (match args with [x1; x2] -> cf_arith arith x1 x2
             | _ -> cf_bottom)
         | ast_Test (ast_Compare cmp) ast_IntT ->
           (match args with [x1; x2] -> cf_int_cmp cmp x1 x2
             | _ -> cf_bottom)
         | ast_Equality ->
           (match args with [x1; x2] -> cf_equality x1 x2
             | _ -> cf_bottom)
         | ast_Opapp ->
           (match dest_opapp (ast_App op args) with SOME (f,xs) -> cf_app
             (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
             list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
             f xs
             | NONE -> cf_bottom)
         | ast_Opref ->
           (match args with [x] -> cf_ref x
              | _ -> cf_bottom)
         | ast_Opassign ->
           (match args with [r; x] -> cf_assign r x
              | _ -> cf_bottom)
         | ast_Opderef ->
           (match args with [r] -> cf_deref r
              | _ -> cf_bottom)
         | ast_Aalloc ->
           (match args with [n; v] -> cf_aalloc n v
             | _ -> cf_bottom)
         | ast_AallocEmpty ->
           (match args with [u] -> cf_aalloc_empty u
             | _ -> cf_bottom)
         | ast_Asub ->
           (match args with [l; n] -> cf_asub l n
             | _ -> cf_bottom)
         | ast_Asub_unsafe ->
           (match args with [l; n] -> cf_asub l n
             | _ -> cf_bottom)
         | ast_Alength ->
           (match args with [l] -> cf_alength l
             | _ -> cf_bottom)
         | ast_Aupdate ->
           (match args with [l; n; v] -> cf_aupdate l n v
             | _ -> cf_bottom)
         | ast_Aupdate_unsafe ->
           (match args with [l; n; v] -> cf_aupdate l n v
             | _ -> cf_bottom)
         | ast_Aw8alloc ->
           (match args with [n; w] -> cf_aw8alloc n w
              | _ -> cf_bottom)
         | ast_Aw8sub ->
           (match args with [l; n] -> cf_aw8sub l n
              | _ -> cf_bottom)
         | ast_Aw8sub_unsafe ->
           (match args with [l; n] -> cf_aw8sub l n
              | _ -> cf_bottom)
         | ast_Aw8length ->
           (match args with [l] -> cf_aw8length l
              | _ -> cf_bottom)
         | ast_Aw8update ->
           (match args with [l; n; w] -> cf_aw8update l n w
              | _ -> cf_bottom)
         | ast_Aw8update_unsafe ->
           (match args with [l; n; w] -> cf_aw8update l n w
              | _ -> cf_bottom)
         | ast_CopyAw8Aw8 ->
           (match args with [s; so; l; d; do'] -> cf_copyaw8aw8 s so l d do'
              | _ -> cf_bottom)
         | ast_CopyStrAw8 ->
           (match args with [s; so; l; d; do'] -> cf_copystraw8 s so l d do'
              | _ -> cf_bottom)
         | ast_CopyAw8Str ->
           (match args with [s; so; l] -> cf_copyaw8str s so l
              | _ -> cf_bottom)
         | ast_XorAw8Str_unsafe ->
           (match args with [d; s] -> cf_xoraw8str s d
              | _ -> cf_bottom)
         | ast_FromTo ast_IntT (ast_WordT ast_W8) ->
           (match args with [i] -> cf_wordFromInt_W8 i
              | _ -> cf_bottom)
         | ast_FromTo ast_IntT (ast_WordT ast_W64) ->
           (match args with [i] -> cf_wordFromInt_W64 i
              | _ -> cf_bottom)
         | ast_FromTo (ast_WordT ast_W8) ast_IntT ->
           (match args with [w] -> cf_wordToInt_W8 w
              | _ -> cf_bottom)
         | ast_FromTo (ast_WordT ast_W64) ast_IntT ->
           (match args with [w] -> cf_wordToInt_W64 w
              | _ -> cf_bottom)
         | ast_FFI ffi_index ->
           (match args with [c; w] -> cf_ffi ffi_index c w
              | _ -> cf_bottom)
         | ast_FromTo (ast_WordT ast_W64) ast_Float64T ->
           (match args with [w] -> cf_fpfromword w
              | _ -> cf_bottom)
         | ast_FromTo ast_Float64T (ast_WordT ast_W64) ->
           (match args with [w] -> cf_fptoword w
              | _ -> cf_bottom)
         | _ -> cf_bottom)
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),ast_Log
     lop e1 e2) ->
     cf_log lop e1 (cf_cf p e2)
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),ast_If
     cond' e1 e2) ->
     cf_if cond' (cf_cf p e1) (cf_cf p e2)
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list),ast_Mat
     e branches) ->
     cf_match e (MAP (\b. (FST b,cf_cf p (SND b))) branches)
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
     list),ast_Raise e) -> cf_raise e
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
     list),ast_Handle e branches) ->
     cf_handle (cf_cf p e) (MAP (\b. (FST b,cf_cf p (SND b))) branches)
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
     list),ast_Lannot e _) -> cf_cf p e
   | ((p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option))
     list),ast_Tannot e _) -> cf_cf p e
   | (_,_) -> cf_bottom`;;

(* HOL4 cfScript.sml:1989-2030: ML code, not ported *)

(*------------------------------------------------------------------*)
(** Properties about [cf]. The main result is the proof of soundness,
    [cf_sound] *)

let cf_local = prove
 (`!e. is_local (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
  list#(mlstring->word8 list->word8 list->ffi->(ffi cfHeapsBase_ffi_result)
  option)) list) e env)`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2052-2059: a proof *)

(* HOL4 cfScript.sml:2061-2063: a proof *)

(* HOL4 cfScript.sml:2065-2067: a proof *)

(* HOL4 cfScript.sml:2069: ML code, not ported *)

(* HOL4 cfScript.sml:2071-2079: a proof *)

(* DROP_EL_CONS[local] *)
let cf_DROP_EL_CONS = prove
 (`!l n.
    n < LENGTH l ==>
    DROP n l = CONS (EL n l) (DROP (SUC n) l)`,
  CHEAT_TAC);;

(* [local] *)
let FST_rw = prove
 (`(\(x,_,_). x) = FST`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2096: ML code, not ported *)
(* [local] *)
let cf_letrec_sound_aux = prove
 (`!funs e.
     let naryfuns = letrec_pull_params funs in
     (!x. MEM x naryfuns ==>
          sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring
            list#(mlstring->word8 list->word8 list->ffi->(ffi
            cfHeapsBase_ffi_result) option)) list) (SND (SND x))
            (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
              list#(mlstring->word8 list->word8 list->ffi->(ffi
              cfHeapsBase_ffi_result) option)) list) (SND (SND x)))) ==>
     sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e
       (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e)
       ==>
     (!fns rest.
       funs = APPEND rest fns ==>
       (let naryrest = letrec_pull_params rest in
       let naryfns = letrec_pull_params fns in
       sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
         list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
         (ast_Letrec funs e)
         (\env H Q.
            let fvs = MAP (\(f,_,_). naryRecclosure env naryfuns f) naryfuns
              in
            ALL_DISTINCT (MAP (\(f,_,_). f) naryfuns) /\
            fun_rec_aux (p:('ffi->(mlstring,ffi)fmap)#(mlstring
              list#(mlstring->word8 list->word8 list->ffi->(ffi
              cfHeapsBase_ffi_result) option)) list)
              (MAP (\(f,_,_). f) naryfuns) fvs
              (MAP (\(_,ns,_). ns) naryfns)
              (DROP (LENGTH naryrest) fvs)
              (MAP (\x. cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
                list#(mlstring->word8 list->word8 list->ffi->(ffi
                cfHeapsBase_ffi_result) option)) list) (SND (SND x))) naryfns)
              (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
                list#(mlstring->word8 list->word8 list->ffi->(ffi
                cfHeapsBase_ffi_result) option)) list) e) env H Q)))`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2213: ML code, not ported *)
(* [local] *)
let cf_letrec_sound = prove
 (`!funs e.
    (!x. MEM x (letrec_pull_params funs) ==>
         sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
           list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
           (SND (SND x))
           (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
             list#(mlstring->word8 list->word8 list->ffi->(ffi
             cfHeapsBase_ffi_result) option)) list) (SND (SND x)))) ==>
    sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e
      (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e) ==>
    sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
      list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
      (ast_Letrec funs e)
      (\env H Q.
        let fvs = MAP
          (\(f,_,_). naryRecclosure env (letrec_pull_params funs) f)
          funs in
        ALL_DISTINCT (MAP (\(f,_,_). f) funs) /\
        fun_rec_aux (p:('ffi->(mlstring,ffi)fmap)#(mlstring
          list#(mlstring->word8 list->word8 list->ffi->(ffi
          cfHeapsBase_ffi_result) option)) list)
          (MAP (\(f,_,_). f) funs) fvs
          (MAP (\(_,ns,_). ns) (letrec_pull_params funs)) fvs
          (MAP (\x. cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
            list#(mlstring->word8 list->word8 list->ffi->(ffi
            cfHeapsBase_ffi_result) option)) list) (SND (SND x)))
             (letrec_pull_params funs))
          (cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring
            list#(mlstring->word8 list->word8 list->ffi->(ffi
            cfHeapsBase_ffi_result) option)) list) e) env H Q)`,
  CHEAT_TAC);;

let pmatch_NIL_IMP = prove
 (`(!envC refs p v env. ~(semanticPrimitives_pmatch envC [] p v env =
  Match_type_error) ==>
     semanticPrimitives_pmatch envC refs p v env = semanticPrimitives_pmatch
       envC [] p v env) /\
   (!envC refs ps vs env. ~(semanticPrimitives_pmatch_list envC [] ps vs env
     = Match_type_error) ==>
     semanticPrimitives_pmatch_list envC refs ps vs env =
       semanticPrimitives_pmatch_list envC [] ps vs env)`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2252: ML code, not ported *)
(* [local] *)
let cf_cases_evaluate_match = prove
 (`!v env H Q nomatch_exn rows p st h_i h_k.
    ALL (\b. sound p (SND b) (cf_cf p (SND b))) rows ==>
    cf_cases v nomatch_exn (MAP (\r. (FST r,cf_cf p (SND r))) rows) env H Q
      ==>
    SPLIT (st2heap p st) (h_i,h_k) ==> H h_i ==>
    (?r h_f h_g heap.
      can_pmatch_all (sem_env_c env) (semanticPrimitives_state_refs st) (MAP
        FST rows) v /\
      SPLIT3 heap (h_f,h_k,h_g) /\
      Q r h_f /\
      (match r with cfHeapsBase_Val v' -> (?ck st'.
          evaluate_evaluate_match (semanticPrimitives_state_clock_fupd (K
            ck) st) env v rows nomatch_exn =
          (st',Rval [v']) /\ semanticPrimitives_state_next_type_stamp
          st' = semanticPrimitives_state_next_type_stamp st
            /\ semanticPrimitives_state_next_exn_stamp
          st' = semanticPrimitives_state_next_exn_stamp st /\
          st2heap p st' = heap)
        | cfHeapsBase_Exn e -> (?ck st'.
          evaluate_evaluate_match (semanticPrimitives_state_clock_fupd (K
            ck) st) env v rows nomatch_exn =
          (st',Rerr (Rraise e)) /\ semanticPrimitives_state_next_type_stamp
          st' = semanticPrimitives_state_next_type_stamp st
            /\ semanticPrimitives_state_next_exn_stamp
          st' = semanticPrimitives_state_next_exn_stamp st /\
          st2heap p st' = heap)
        | cfHeapsBase_FFIDiv name conf bytes -> (?ck st'.
          evaluate_evaluate_match (semanticPrimitives_state_clock_fupd (K
            ck) st) env v rows nomatch_exn =
          (st',Rerr (Rabort (Rffi_error (Final_event (ffi_ExtCall name) conf
            bytes FFI_diverged)))) /\ semanticPrimitives_state_next_type_stamp
          st' = semanticPrimitives_state_next_type_stamp st
            /\ semanticPrimitives_state_next_exn_stamp
          st' = semanticPrimitives_state_next_exn_stamp st /\
          st2heap p st' = heap)
        | cfHeapsBase_Div io ->
          (!ck. ?st'. evaluate_evaluate_match
            (semanticPrimitives_state_clock_fupd (K ck) st) env v rows
            nomatch_exn =
              (st',Rerr (Rabort Rtimeout_error))) /\
          lprefix_lub (IMAGE (\ck. sptree_fromList (ffi_state_io_events
            (semanticPrimitives_state_ffi (FST (evaluate_evaluate_match
            (semanticPrimitives_state_clock_fupd (K ck) st) env v rows
            nomatch_exn))))) UNIV) io))`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2352: ML code, not ported *)
(* [local] *)
let cf_ffi_sound = prove
 (`sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) (ast_App
  (ast_FFI ffi_index) [c; r]) (\env. local (\H Q.
     ?cv rv. exp2v env r = SOME rv /\
          exp2v env c = SOME cv /\
          app_ffi ffi_index cv rv H Q))`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2570: ML code, not ported *)
(* [local] *)
let evaluate_add_to_clock_lemma = prove
 (`!extra p (s:'ffi semanticPrimitives_state) s' r e.
     evaluate s e p = (s',r) ==> ~(r = Rerr (Rabort Rtimeout_error)) ==>
     evaluate (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s + extra)) s) e p =
     (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s' + extra)) s',r)`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2581: ML code, not ported *)
(* [local] *)
let evaluate_match_add_to_clock_lemma = prove
 (`!extra (s:'ffi semanticPrimitives_state) env v rows err_v s' r.
     evaluate_evaluate_match s env v rows err_v = (s',r) ==> ~(r = Rerr
       (Rabort Rtimeout_error)) ==>
     evaluate_evaluate_match (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s + extra)) s) env v rows err_v =
     (semanticPrimitives_state_clock_fupd (K
       (semanticPrimitives_state_clock s' + extra)) s',r)`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2592-2600: ML code, not ported *)

let lprefix_lub_subset = prove
 (`lprefix_lub s l /\ s SUBSET t /\
   (!x. x IN t /\ ~(x IN s) ==> (?y. y IN s /\ LPREFIX x y)) ==>
   lprefix_lub t l`,
  CHEAT_TAC);;

let LPREFIX_fromList_fromList = prove
 (`LPREFIX (sptree_fromList x) (sptree_fromList y) = (x <<= y)`,
  CHEAT_TAC);;

let isPREFIX_TRANS = prove
 (`!x y z. x <<= y /\ y <<= z ==> x <<= z`,
  CHEAT_TAC);;

let can_pmatch_all_NIL_IMP = prove
 (`!ps envC v.
     can_pmatch_all envC [] ps v ==>
     (!refs. can_pmatch_all envC refs ps v)`,
  CHEAT_TAC);;

(* [local] *)
let IMP_xor_bytes_SOME = prove
 (`!s wd.
     strlen s <= LENGTH wd ==>
     (?xor_res. xor_bytes (MAP (n2w o ORD) (explode s)) wd = SOME xor_res)`,
  CHEAT_TAC);;

let cf_sound = prove
 (`!p e. sound (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
  list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e (cf_cf
  (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8 list->word8
  list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e)`,
  CHEAT_TAC);;

(* HOL4 cfScript.sml:2792-2794: a proof *)
    (* function declaration *)
    (* Eliminate the impossible case (Fun_body _ = NONE), then we call
      cf_strip_sound_tac *)
(* HOL4 cfScript.sml:2798-2799: a proof *)
    (* Instantiate the hypothesis with the closure *)
(* HOL4 cfScript.sml:2801-2824: a proof *)
    (* other cases of let-binding *)
(* HOL4 cfScript.sml:2826-2830: a proof *)
      (* e1 ~> Rval v *)
(* HOL4 cfScript.sml:2832-2874: a proof *)
        (* e2 ~> Rval v' || e2 ~> Rerr (Rraise v') *)
(* HOL4 cfScript.sml:2876-2889: a proof *)
      (* e1 ~> Rerr (Rraise v) *)
(* HOL4 cfScript.sml:2891-2895: a proof *)
      (* e1 ~> FFI diverge *)
(* HOL4 cfScript.sml:2897-2903: a proof *)
      (* e1 ~> timeout *)
(* HOL4 cfScript.sml:2905-2926: a proof *)

(* HOL4 cfScript.sml:2928-3099: a proof *)
    (* Aw8alloc & Aalloc *)
(* HOL4 cfScript.sml:3101-3125: a proof *)
    (* Aalloc_empty *)
(* HOL4 cfScript.sml:3127-3150: a proof *)
    (* Aw8sub & Asub *)
(* HOL4 cfScript.sml:3152-3168: a proof *)
    (* Aw8length & Alength *)
(* HOL4 cfScript.sml:3170-3185: a proof *)
    (* Aw8update & Aupdate *)
(* HOL4 cfScript.sml:3187-3211: a proof *)
    (* CopyStrAw8 *)
(* HOL4 cfScript.sml:3213-3245: a proof *)
    (* CopyAw8Str *)
(* HOL4 cfScript.sml:3247-3271: a proof *)
    (* CopyAw8Aw8 *)
(* HOL4 cfScript.sml:3273-3304: a proof *)

(* HOL4 cfScript.sml:3306-3314: a proof *)
  (* 1 argument *)
(* HOL4 cfScript.sml:3316-3362: a proof *)
  (* 2+ arguments *)
(* HOL4 cfScript.sml:3364-3367: a proof *)
    (* Do some unfolding, by definition of dest_opapp *)
(* HOL4 cfScript.sml:3369-3374: a proof *)
    (* Prepare for, and apply lemma [app_alt_ind_w] to split app *)
(* HOL4 cfScript.sml:3376-3379: a proof *)
    (* Specialize induction hypothesis with xs := pxs *)
(* HOL4 cfScript.sml:3381-3383: a proof *)
    (* Cleanup *)
(* HOL4 cfScript.sml:3385-3386: a proof *)
    (* Exploit the [app_basic (p:'ffi ffi_proj) g xv H' Q] we got from the ind. hyp. *)
(* HOL4 cfScript.sml:3388-3390: a proof *)
    (* Instantiate the result value, case split on it *)
(* HOL4 cfScript.sml:3392-3451: a proof *)
      (* res = Val _ || res = Exn _ *)
(* HOL4 cfScript.sml:3453-3457: a proof *)
      (* Instantiate the clock, cleanup *)
(* HOL4 cfScript.sml:3459-3462: a proof *)
      (* Finish proving the goal *)
(* HOL4 cfScript.sml:3464-3471: a proof *)

(* HOL4 cfScript.sml:3473-3511: a proof *)

(* HOL4 cfScript.sml:3513-3540: a proof *)

(* HOL4 cfScript.sml:3542-3569: a proof *)

(* HOL4 cfScript.sml:3571: a proof *)

let cf_sound' = prove
 (`!e env H Q st.
     cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e env
       H Q ==> H (st2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) st) ==>
     (?r h_f h_g heap.
       SPLIT heap (h_f,h_g) /\
       Q r h_f /\
       (match r with cfHeapsBase_Val v -> (?ck st'.
            evaluate (semanticPrimitives_state_clock_fupd (K ck) st) env [e]
              = (st',Rval [v]) /\ semanticPrimitives_state_next_type_stamp
            st' = semanticPrimitives_state_next_type_stamp st
              /\ semanticPrimitives_state_next_exn_stamp
            st' = semanticPrimitives_state_next_exn_stamp st /\
            st2heap p st' = heap)
          | cfHeapsBase_Exn v -> (?ck st'.
            evaluate (semanticPrimitives_state_clock_fupd (K ck) st) env [e]
              = (st',Rerr (Rraise v))
              /\ semanticPrimitives_state_next_type_stamp
            st' = semanticPrimitives_state_next_type_stamp st
              /\ semanticPrimitives_state_next_exn_stamp
            st' = semanticPrimitives_state_next_exn_stamp st /\
            st2heap p st' = heap)
          | cfHeapsBase_FFIDiv name conf bytes -> (?ck st'.
            evaluate (semanticPrimitives_state_clock_fupd (K ck) st) env [e]
              =
            (st',Rerr (Rabort (Rffi_error (Final_event (ffi_ExtCall name)
              conf bytes FFI_diverged))))
              /\ semanticPrimitives_state_next_type_stamp
            st' = semanticPrimitives_state_next_type_stamp st
              /\ semanticPrimitives_state_next_exn_stamp
            st' = semanticPrimitives_state_next_exn_stamp st /\
            st2heap p st' = heap)
          | cfHeapsBase_Div io ->
            (!ck. ?st'. evaluate (semanticPrimitives_state_clock_fupd (K ck)
              st) env [e] =
            (st',Rerr (Rabort Rtimeout_error))) /\
            lprefix_lub (IMAGE (\ck. sptree_fromList (ffi_state_io_events
              (semanticPrimitives_state_ffi (FST (evaluate
              (semanticPrimitives_state_clock_fupd (K ck) st) env [e])))))
              UNIV) io))`,
  CHEAT_TAC);;

let cf_sound_local = prove
 (`!e env H Q h i st.
     cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) e env
       H Q ==>
     SPLIT (st2heap (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) st) (h,i) ==>
     H h ==>
     (?r h' g heap.
       SPLIT3 heap (h',g,i) /\
       Q r h' /\
       (match r with cfHeapsBase_Val v -> (?ck st'.
            evaluate (semanticPrimitives_state_clock_fupd (K ck) st) env [e]
              = (st',Rval [v]) /\ semanticPrimitives_state_next_type_stamp
            st' = semanticPrimitives_state_next_type_stamp st
              /\ semanticPrimitives_state_next_exn_stamp
            st' = semanticPrimitives_state_next_exn_stamp st /\
            st2heap p st' = heap)
          | cfHeapsBase_Exn v -> (?ck st'.
            evaluate (semanticPrimitives_state_clock_fupd (K ck) st) env [e]
              = (st',Rerr (Rraise v))
              /\ semanticPrimitives_state_next_type_stamp
            st' = semanticPrimitives_state_next_type_stamp st
              /\ semanticPrimitives_state_next_exn_stamp
            st' = semanticPrimitives_state_next_exn_stamp st /\
            st2heap p st' = heap)
          | cfHeapsBase_FFIDiv name conf bytes -> (?ck st'.
            evaluate (semanticPrimitives_state_clock_fupd (K ck) st) env [e]
              =
            (st',Rerr (Rabort (Rffi_error (Final_event (ffi_ExtCall name)
              conf bytes FFI_diverged))))
              /\ semanticPrimitives_state_next_type_stamp
            st' = semanticPrimitives_state_next_type_stamp st
              /\ semanticPrimitives_state_next_exn_stamp
            st' = semanticPrimitives_state_next_exn_stamp st /\
            st2heap p st' = heap)
          | cfHeapsBase_Div io ->
            (!ck. ?st'. evaluate (semanticPrimitives_state_clock_fupd (K ck)
              st) env [e] =
            (st',Rerr (Rabort Rtimeout_error))) /\
            lprefix_lub (IMAGE (\ck. sptree_fromList (ffi_state_io_events
              (semanticPrimitives_state_ffi (FST (evaluate
              (semanticPrimitives_state_clock_fupd (K ck) st) env [e])))))
              UNIV) io))`,
  CHEAT_TAC);;

let app_basic_of_cf = prove
 (`!clos body x env env' v H Q.
     semanticPrimitives_do_opapp [clos; x] = SOME (env',body) ==>
     cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) body
       env' H Q ==>
     app_basic (p:('ffi->(mlstring,ffi)fmap)#(mlstring
       list#(mlstring->word8 list->word8 list->ffi->(ffi
       cfHeapsBase_ffi_result) option)) list) clos x H Q`,
  CHEAT_TAC);;

let app_of_cf = prove
 (`!ns env body xvs H Q. ~(ns = []) ==>
     LENGTH xvs = LENGTH ns ==>
     cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) body
       (cf_extend_env ns xvs env) H Q ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryClosure env ns body) xvs H Q`,
  CHEAT_TAC);;

let app_rec_of_cf = prove
 (`!f params' body funs xvs env H Q. ~(params' = []) ==>
     LENGTH params' = LENGTH xvs ==>
     ALL_DISTINCT (MAP (\(f,_,_). f) funs) ==>
     find_recfun f (letrec_pull_params funs) = SOME (params',body) ==>
     cf_cf (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) body
       (extend_env_rec
          (MAP (\(f,_,_). f) funs)
          (MAP (\(f,_,_). naryRecclosure env (letrec_pull_params funs) f)
            funs)
          params' xvs env)
        H Q ==>
     app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
       list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list)
       (naryRecclosure env (letrec_pull_params funs) f) xvs H Q`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["fv"];;

(* and the interface *)
let _ = unhide_overloads ();;
