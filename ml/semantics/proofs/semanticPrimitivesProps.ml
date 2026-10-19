(* ======================================================== *)
(*  semanticPrimitivesProps: ported from HOL4's
    semantics/proofs/semanticPrimitivesPropsScript.sml
    A proof theory about semanticPrimitives.ml, with 20 definitions
    and 61 theorems.  Needed by 28 files of the port.  *)
(* ======================================================== *)

(*
  Various basic properties of the semantic primitives.
*)

needs "basis/pure/mlstring.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;

cake_hide ["id"];;


let with_same_v = cake_theorem "with_same_v[simp]"
  (fun () ->
    `sem_env_v_fupd (K (sem_env_v env))
        (env:'v sem_env) = env`)
  CHEAT_TAC;;

let unchanged_env = cake_theorem "unchanged_env[simp]"
  (fun () ->
    `!(env:'a sem_env).
     mk_sem_env (sem_env_v env) (sem_env_c env) = env`)
  CHEAT_TAC;;

let semanticPrimitivesProps_with_same_clock =
  cake_theorem "with_same_clock"
  (fun () ->
    `semanticPrimitives_state_clock_fupd (K
  (semanticPrimitives_state_clock st))
        (st:'ffi semanticPrimitives_state) = st`)
  CHEAT_TAC;;

let semanticPrimitivesProps_Boolv_11 = cake_theorem "Boolv_11[simp]"
  (fun () ->
    `semanticPrimitives_Boolv b1 = semanticPrimitives_Boolv b2 <=> (b1
  = b2)`)
  CHEAT_TAC;;

let extend_dec_env_assoc = cake_theorem "extend_dec_env_assoc[simp]"
  (fun () ->
    `!env1 env2 env3.
      extend_dec_env env1 (extend_dec_env env2 env3) =
      extend_dec_env (extend_dec_env env1 env2) env3`)
  CHEAT_TAC;;

let shift_lookup_def = cake_define_list
  [`shift_lookup Lsl = word_lsl`;
   `shift_lookup Lsr = word_lsr`;
   `shift_lookup Asr = word_asr`;
   `shift_lookup Ror = word_ror`];;

let do_shift_def = cake_define
  `do_shift sh n x3 x4 =
        match (x3,x4) with
          (ast_W8,ast_Word8 w) -> SOME (ast_Word8 (shift_lookup sh w
            n))
        | (ast_W64,(ast_Word64 w)) -> SOME (ast_Word64 (shift_lookup
          sh w n))
        | (_1,_2) -> NONE`;;

(* HOL4 semanticPrimitivesPropsScript.sml:58-75: code that the source
   has in a comment *)

let lit_same_type_refl = cake_theorem "lit_same_type_refl[simp]"
  (fun () ->
    `!l. lit_same_type l l`)
  CHEAT_TAC;;

let lit_same_type_sym = cake_theorem "lit_same_type_sym"
  (fun () ->
    `!l1 l2. lit_same_type l1 l2 ==> lit_same_type l2 l1`)
  CHEAT_TAC;;

let pmatch_append = cake_theorem "pmatch_append"
  (fun () ->
    `(!(cenv:(mlstring,mlstring,num#stamp)namespace)
  (st:(semanticPrimitives_v store_v) list) p v env env' env''.
        (semanticPrimitives_pmatch cenv st p v env = Match env')
          ==>
        (semanticPrimitives_pmatch cenv st p v (env ++ env'') =
          Match (env' ++ env''))) /\
     (!(cenv:(mlstring,mlstring,num#stamp)namespace)
       (st:(semanticPrimitives_v store_v) list) ps v env env' env''.
        (semanticPrimitives_pmatch_list cenv st ps v env = Match
          env') ==>
        (semanticPrimitives_pmatch_list cenv st ps v (env ++
          env'') = Match (env' ++ env'')))`)
  CHEAT_TAC;;

let pmatch_extend = cake_theorem "pmatch_extend"
  (fun () ->
    `(!cenv s p v env env' env''.
      semanticPrimitives_pmatch cenv s p v env = Match env' ==>
      (?env''. env' = env'' ++ env /\ MAP FST env'' =
        ast_pat_bindings p)) /\
     (!cenv s ps vs env env' env''.
      semanticPrimitives_pmatch_list cenv s ps vs env = Match env'
        ==>
      (?env''. env' = env'' ++ env /\ MAP FST env'' =
        ast_pats_bindings ps))`)
  CHEAT_TAC;;

let pmatch_nsAppend = cake_theorem "pmatch_nsAppend"
  (fun () ->
    `(!ns st pat v env m ns'.
       (
      semanticPrimitives_pmatch ns st pat v env = No_match ==>
        semanticPrimitives_pmatch (nsAppend ns ns') st pat v env =
        No_match) /\
       (
      semanticPrimitives_pmatch ns st pat v env = Match m ==>
        semanticPrimitives_pmatch (nsAppend ns ns') st pat v env = Match
        m)) /\
     (!ns st pats vs env m ns'.
       (
      semanticPrimitives_pmatch_list ns st pats vs env = No_match
        ==> semanticPrimitives_pmatch_list (nsAppend ns ns') st pats vs
        env = No_match) /\
       (
      semanticPrimitives_pmatch_list ns st pats vs env = Match m
        ==> semanticPrimitives_pmatch_list (nsAppend ns ns') st pats
        vs env = Match m))`)
  CHEAT_TAC;;

(* HOL4 semanticPrimitivesPropsScript.sml:163: a theorem that HOL4
   states as the value of an ML expression: pmatch_nsAppend_No_match *)
(* HOL4 semanticPrimitivesPropsScript.sml:164: a theorem that HOL4
   states as the value of an ML expression: pmatch_nsAppend_Match *)

let pmatch_acc = cake_theorem "pmatch_acc"
  (fun () ->
    `(!envc store p v env env' env2.
       (semanticPrimitives_pmatch envc store p v env = Match env'
         <=>
        semanticPrimitives_pmatch envc store p v (env ++ env2) =
          Match (env' ++ env2)) /\
       (semanticPrimitives_pmatch envc store p v env = No_match <=>
        semanticPrimitives_pmatch envc store p v (env ++ env2) =
          No_match) /\
       (semanticPrimitives_pmatch envc store p v env =
         Match_type_error <=>
        semanticPrimitives_pmatch envc store p v (env ++ env2) =
          Match_type_error)) /\
     (!envc store ps vs env env' env2.
       (semanticPrimitives_pmatch_list envc store ps vs env = Match
         env' <=>
        semanticPrimitives_pmatch_list envc store ps vs (env ++
          env2) = Match (env' ++ env2)) /\
       (semanticPrimitives_pmatch_list envc store ps vs env =
         No_match <=>
        semanticPrimitives_pmatch_list envc store ps vs (env ++
          env2) = No_match) /\
       (semanticPrimitives_pmatch_list envc store ps vs env =
         Match_type_error <=>
        semanticPrimitives_pmatch_list envc store ps vs (env ++
          env2) = Match_type_error))`)
  CHEAT_TAC;;

(* HOL4 semanticPrimitivesPropsScript.sml:194-196: ML code, not
   ported *)

let pair_case_eq = cake_theorem "pair_case_eq[local]"
  (fun () ->
    `pair_CASE x f = v <=> (?x1 x2. x = (x1,x2) /\ f x1 x2 = v)`)
  CHEAT_TAC;;

let semanticPrimitivesProps_pair_lam_lem =
  cake_theorem "pair_lam_lem[local]"
  (fun () ->
    `!f v z. (let (x,y) = z in f x y) = v <=> (?x1 x2. z = (x1,x2) /\
  (f x1 x2 = v))`)
  CHEAT_TAC;;

(* HOL4 semanticPrimitivesPropsScript.sml:211-215: a theorem that
   HOL4 states as the value of an ML expression: do_app_cases *)

let do_opapp_cases = cake_theorem "do_opapp_cases"
  (fun () ->
    `!env' vs v.
      (semanticPrimitives_do_opapp vs = SOME (env',v)) =
     ((?v2 env'' n e.
      (vs = [semanticPrimitives_Closure env'' n e; v2]) /\
      (env' = sem_env_v_fupd (K (nsBind n v2 (sem_env_v env'')))
        env'') /\ (v = e)) \/
     (?v2 env'' funs n' n'' e.
      (vs = [semanticPrimitives_Recclosure env'' funs n'; v2]) /\
      (find_recfun n' funs = SOME (n'',e)) /\
      (ALL_DISTINCT (MAP (\(f,x,e). f) funs)) /\
      (env' = sem_env_v_fupd (K (nsBind n'' v2
        (semanticPrimitives_build_rec_env funs env'' (sem_env_v
        env'')))) env'' /\ (v = e))))`)
  CHEAT_TAC;;

let do_app_NONE_ffi = cake_theorem "do_app_NONE_ffi"
  (fun () ->
    `semanticPrimitives_do_app (refs,ffi) op args = NONE ==>
     semanticPrimitives_do_app (refs,ffi') op args = NONE`)
  CHEAT_TAC;;

let do_app_SOME_ffi_same = cake_theorem "do_app_SOME_ffi_same"
  (fun () ->
    `semanticPrimitives_do_app (refs,ffi) op args = SOME ((refs',ffi),r)
  /\ (!outcome. ~(r = Rerr (Rabort (Rffi_error outcome)))) ==>
     semanticPrimitives_do_app (refs,ffi') op args = SOME
       ((refs',ffi'),r)`)
  CHEAT_TAC;;

let do_app_ffi_unchanged = cake_theorem "do_app_ffi_unchanged"
  (fun () ->
    `!st ffi op vs st' ffi' res.
       (!s. ~(op = ast_FFI s)) /\
       semanticPrimitives_do_app (st,ffi) op vs = SOME
         ((st',ffi'),res) ==> ffi = ffi'`)
  CHEAT_TAC;;

let do_app_ffi_changed = cake_theorem "do_app_ffi_changed"
  (fun () ->
    `semanticPrimitives_do_app (st,ffi) op vs = SOME ((st',ffi'),res) /\
  ~(ffi = ffi') ==>
     (?s conf lnum ws ffi_st ws' b.
       op = ast_FFI s /\
       vs = [semanticPrimitives_Litv (ast_StrLit conf);
         semanticPrimitives_Loc b lnum] /\
       store_lookup lnum st = SOME (semanticPrimitives_W8array ws)
         /\ ~(s = (implode "")) /\ oracle
       ffi
          (ffi_ExtCall s) (ffi_state_ffi_state
          ffi)
          (MAP (\c. n2w (ORD c)) (explode conf))
          ws =
       Oracle_return ffi_st ws' /\
       LENGTH ws = LENGTH ws' /\
       st' = LUPDATE (semanticPrimitives_W8array ws') lnum st /\
         oracle
       ffi' = oracle ffi /\ ffi_state_ffi_state
       ffi' = ffi_st /\ ffi_state_io_events
       ffi' = ffi_state_io_events
         ffi ++
           [IO_event (ffi_ExtCall s) (MAP (\c. n2w (ORD c))
             (explode conf))
                     (ZIP ws ws')])`)
  CHEAT_TAC;;

let do_app_not_timeout = cake_theorem "do_app_not_timeout"
  (fun () ->
    `semanticPrimitives_do_app s op vs = SOME (s',Rerr (Rabort a)) ==>
  ~(a = Rtimeout_error)`)
  CHEAT_TAC;;

let do_app_type_error = cake_theorem "do_app_type_error"
  (fun () ->
    `semanticPrimitives_do_app s op es = SOME (x,Rerr (Rabort a)) ==>
  x = s`)
  CHEAT_TAC;;

let build_rec_env_help_lem =
  cake_theorem "build_rec_env_help_lem[local]"
  (fun () ->
    `!funs env funs'.
       ITLIST (\(f,x,e) env'. nsBind f
         (semanticPrimitives_Recclosure env funs' f) env') funs env' =
       nsAppend (alist_to_ns (MAP (\(f,n,e).
         (f,semanticPrimitives_Recclosure env funs' f)) funs)) env'`)
  CHEAT_TAC;;

(* Alternate definition for build_rec_env *)
let build_rec_env_merge = cake_theorem "build_rec_env_merge"
  (fun () ->
    `!funs funs' env env'.
      semanticPrimitives_build_rec_env funs env env' =
      nsAppend (alist_to_ns (MAP (\(f,n,e).
        (f,semanticPrimitives_Recclosure env funs f)) funs)) env'`)
  CHEAT_TAC;;

let do_con_check_build_conv = cake_theorem "do_con_check_build_conv"
  (fun () ->
    `!tenvC cn vs l.
      do_con_check tenvC cn l ==> (?v. build_conv tenvC cn vs =
        SOME v)`)
  CHEAT_TAC;;

let map_error_result_def = cake_define_list
  [`map_error_result f (Rraise e) = Rraise (f e)`;
   `map_error_result f (Rabort a) = Rabort a`];;

let map_error_result_Rtype_error =
  cake_theorem "map_error_result_Rtype_error[simp]"
  (fun () ->
    `map_error_result f e = (Rabort a) <=> e = Rabort a`)
  CHEAT_TAC;;

let map_error_result_I = cake_theorem "map_error_result_I[simp]"
  (fun () ->
    `map_error_result I e = e`)
  CHEAT_TAC;;

let map_result_def = cake_define_list
  [`map_result f1 f2 (Rval v) = Rval (f1 v)`;
   `map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e)`];;

let map_result_Rval = cake_theorem "map_result_Rval[simp]"
  (fun () ->
    `map_result f1 f2 e = Rval x <=> (?y. e = Rval y /\ x = f1 y)`)
  CHEAT_TAC;;

let map_result_Rerr = cake_theorem "map_result_Rerr[simp]"
  (fun () ->
    `map_result f1 f2 e = Rerr e' <=> (?a. e = Rerr a /\
  map_error_result f2 a = e')`)
  CHEAT_TAC;;

let exc_rel_def = cake_define
  `exc_rel R x2 x3 =
        match (x2,x3) with
          (Rraise v1,Rraise v2) -> R v1 v2
        | ((Rabort a1),(Rabort a2)) -> a1 = a2
        | (_3,_4) -> F`;;

let exc_rel_raise1 = cake_theorem "exc_rel_raise1[simp]"
  (fun () ->
    `exc_rel R (Rraise v) e = (?v'. (e = Rraise v') /\ R v v')`)
  CHEAT_TAC;;
let exc_rel_raise2 = cake_theorem "exc_rel_raise2[simp]"
  (fun () ->
    `exc_rel R e (Rraise v) = (?v'. (e = Rraise v') /\ R v' v)`)
  CHEAT_TAC;;
let exc_rel_type_error1 = cake_theorem "exc_rel_type_error1[simp]"
  (fun () ->
    `(exc_rel R (Rabort a) e = (e = Rabort a))`)
  CHEAT_TAC;;
let exc_rel_type_error2 = cake_theorem "exc_rel_type_error2[simp]"
  (fun () ->
    `(exc_rel R e (Rabort a) = (e = Rabort a))`)
  CHEAT_TAC;;

let exc_rel_refl = cake_theorem "exc_rel_refl[simp]"
  (fun () ->
    `(!x. R x x) ==> (!x. exc_rel R x x)`)
  CHEAT_TAC;;

let exc_rel_trans = cake_theorem "exc_rel_trans"
  (fun () ->
    `(!x y z. R x y /\ R y z ==> R x z) ==> (!x y z. exc_rel R x y /\
  exc_rel R y z ==> exc_rel R x z)`)
  CHEAT_TAC;;

let result_rel_def = cake_define
  `semanticPrimitivesProps_result_rel R1 R2 x3 x4 =
        match (x3,x4) with
          (Rval v1,Rval v2) -> R1 v1 v2
        | ((Rerr e1),(Rerr e2)) -> exc_rel R2 e1 e2
        | (_5,_6) -> F`;;
hol4_overload "result_rel" "semanticPrimitivesProps_result_rel";;

let result_rel_Rval = cake_theorem "result_rel_Rval[simp]"
  (fun () ->
    `semanticPrimitivesProps_result_rel R1 R2 (Rval v) r = (?v'. (r =
  Rval v') /\ R1 v v')`)
  CHEAT_TAC;;
let result_rel_Rerr1 = cake_theorem "result_rel_Rerr1[simp]"
  (fun () ->
    `semanticPrimitivesProps_result_rel R1 R2 (Rerr e) r = (?e'. (r =
  Rerr e') /\ exc_rel R2 e e')`)
  CHEAT_TAC;;
let result_rel_Rerr2 = cake_theorem "result_rel_Rerr2[simp]"
  (fun () ->
    `semanticPrimitivesProps_result_rel R1 R2 r (Rerr e) = (?e'. (r =
  Rerr e') /\ exc_rel R2 e' e)`)
  CHEAT_TAC;;

let result_rel_refl = cake_theorem "result_rel_refl[simp]"
  (fun () ->
    `(!x. R1 x x) /\ (!x. R2 x x) ==> (!x.
  semanticPrimitivesProps_result_rel R1 R2 x x)`)
  CHEAT_TAC;;

let result_rel_trans = cake_theorem "result_rel_trans"
  (fun () ->
    `(!x y z. R1 x y /\ R1 y z ==> R1 x z) /\ (!x y z. R2 x y /\ R2 y
  z ==> R2 x z) ==> (!x y z. semanticPrimitivesProps_result_rel R1 R2
  x y /\ semanticPrimitivesProps_result_rel R1 R2 y z ==>
  semanticPrimitivesProps_result_rel R1 R2 x z)`)
  CHEAT_TAC;;

let every_error_result_def = cake_define_list
  [`every_error_result P (Rraise e) = P e`;
   `every_error_result P (Rabort a) = T`];;

let every_result_def = cake_define_list
  [`every_result P1 P2 (Rval v) = (P1 v)`;
   `every_result P1 P2 (Rerr e) = (every_error_result P2 e)`];;

let map_sv_def = cake_define_list
  [`map_sv f (semanticPrimitives_Refv v) = semanticPrimitives_Refv (f
  v)`;
   `map_sv _7 (semanticPrimitives_W8array w) =
  (semanticPrimitives_W8array w)`;
   `map_sv f (semanticPrimitives_Varray vs) =
  (semanticPrimitives_Varray (MAP f vs))`;
   `map_sv f (semanticPrimitives_Thunk m v) =
  (semanticPrimitives_Thunk m (f v))`];;

let dest_Refv_def = cake_define
  `dest_Refv (semanticPrimitives_Refv v) = v`;;
let is_Refv_def = cake_define
  `is_Refv x1 =
      match x1 with
        semanticPrimitives_Refv _8 -> T
      | _9 -> F`;;

let sv_every_def = cake_define
  `sv_every P x2 =
      match x2 with
        semanticPrimitives_Refv v -> P v
      | (semanticPrimitives_Varray vs) -> EVERY P vs
      | (semanticPrimitives_Thunk m v) -> P v
      | _10 -> T`;;

let sv_rel_def = cake_define
  `semanticPrimitivesProps_sv_rel R x2 x3 =
      match (x2,x3) with
        (semanticPrimitives_Refv v1,semanticPrimitives_Refv v2) -> R
          v1 v2
      | ((semanticPrimitives_W8array w1),(semanticPrimitives_W8array
        w2)) -> (w1 = w2)
      | ((semanticPrimitives_Varray vs1),(semanticPrimitives_Varray
        vs2)) -> LIST_REL R vs1 vs2
      | ((semanticPrimitives_Thunk m1 v1),(semanticPrimitives_Thunk
        m2 v2)) -> (m1 = m2 /\ R v1 v2)
      | (_11,_12) -> F`;;
hol4_overload "sv_rel" "semanticPrimitivesProps_sv_rel";;

let sv_rel_refl = cake_theorem "sv_rel_refl[simp]"
  (fun () ->
    `!R x. (!x. R x x) ==> semanticPrimitivesProps_sv_rel R x x`)
  CHEAT_TAC;;

let sv_rel_trans = cake_theorem "sv_rel_trans"
  (fun () ->
    `!R. (!x y z. R x y /\ R y z ==> R x z) ==> (!x y z.
  semanticPrimitivesProps_sv_rel R x y /\
  semanticPrimitivesProps_sv_rel R y z ==>
  semanticPrimitivesProps_sv_rel R x z)`)
  CHEAT_TAC;;

let sv_rel_cases = cake_theorem "sv_rel_cases"
  (fun () ->
    `!x y.
      semanticPrimitivesProps_sv_rel R x y <=>
      (?v1 v2. x = semanticPrimitives_Refv v1 /\ y =
        semanticPrimitives_Refv v2 /\ R v1 v2) \/
      (?w. x = semanticPrimitives_W8array w /\ y =
        semanticPrimitives_W8array w) \/
      (?m v1 v2. x = semanticPrimitives_Thunk m v1 /\ y =
        semanticPrimitives_Thunk m v2 /\ R v1 v2) \/
      (?vs1 vs2. x = semanticPrimitives_Varray vs1 /\ y =
        semanticPrimitives_Varray vs2 /\ LIST_REL R vs1 vs2)`)
  CHEAT_TAC;;

let sv_rel_O = cake_theorem "sv_rel_O"
  (fun () ->
    `!R1 R2. semanticPrimitivesProps_sv_rel (O R1 R2) = O
  (semanticPrimitivesProps_sv_rel R1) (semanticPrimitivesProps_sv_rel
  R2)`)
  CHEAT_TAC;;

let sv_rel_mono = cake_theorem "sv_rel_mono"
  (fun () ->
    `(!x y. P x y ==> Q x y) ==> semanticPrimitivesProps_sv_rel P x y
  ==> semanticPrimitivesProps_sv_rel Q x y`)
  CHEAT_TAC;;

let store_v_vs_def = cake_define_list
  [`semanticPrimitivesProps_store_v_vs (semanticPrimitives_Refv v) =
  [v]`;
   `semanticPrimitivesProps_store_v_vs (semanticPrimitives_Varray vs)
  = vs`;
   `semanticPrimitivesProps_store_v_vs (semanticPrimitives_W8array
  _13) = []`;
   `semanticPrimitivesProps_store_v_vs (semanticPrimitives_Thunk
  _15 v) = [v]`];;
hol4_overload "store_v_vs" "semanticPrimitivesProps_store_v_vs";;

let store_vs_def = cake_define
  `store_vs s = FLAT (MAP semanticPrimitivesProps_store_v_vs s)`;;

let EVERY_sv_every_MAP_map_sv = cake_theorem "EVERY_sv_every_MAP_map_sv"
  (fun () ->
    `!P f ls. EVERY P (MAP f (store_vs ls)) ==> EVERY (sv_every P)
  (MAP (map_sv f) ls)`)
  CHEAT_TAC;;

let LIST_REL_store_vs_intro = cake_theorem "LIST_REL_store_vs_intro"
  (fun () ->
    `!P l1 l2. LIST_REL (semanticPrimitivesProps_sv_rel P) l1 l2 ==>
  LIST_REL P (store_vs l1) (store_vs l2)`)
  CHEAT_TAC;;

let EVERY_sv_every_EVERY_store_vs =
  cake_theorem "EVERY_sv_every_EVERY_store_vs"
  (fun () ->
    `!P ls. EVERY (sv_every P) ls <=> EVERY P (store_vs ls)`)
  CHEAT_TAC;;

let EVERY_store_vs_intro = cake_theorem "EVERY_store_vs_intro"
  (fun () ->
    `!P ls. EVERY (sv_every P) ls ==> EVERY P (store_vs ls)`)
  CHEAT_TAC;;

let map_sv_compose = cake_theorem "map_sv_compose"
  (fun () ->
    `map_sv f (map_sv g x) = map_sv (f o g) x`)
  CHEAT_TAC;;

let map_match_def = cake_define
  `map_match f x =
        match x with
          Match env -> Match (f env)
        | x -> x`;;

let find_recfun_ALOOKUP = cake_theorem "find_recfun_ALOOKUP"
  (fun () ->
    `!funs n. find_recfun n funs = ALOOKUP funs n`)
  CHEAT_TAC;;

let find_recfun_el = cake_theorem "find_recfun_el"
  (fun () ->
    `!f funs x e n.
      ALL_DISTINCT (MAP (\(f,x,e). f) funs) /\
      n < LENGTH funs /\
      EL n funs = (f,x,e) ==>
      find_recfun f funs = SOME (x,e)`)
  CHEAT_TAC;;

let ctors_of_tdef_def = cake_define
  `ctors_of_tdef (_16,_17,condefs) = MAP FST condefs`;;

let ctors_of_dec_def = cake_define
  `ctors_of_dec x1 =
      match x1 with
        Dtype locs tds -> FLAT (MAP ctors_of_tdef tds)
      | (Dexn locs s _18) -> [s]
      | _19 -> []`;;

(* free vars *)

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let FV_def = cake_define_list_cheat CHEAT_TAC
  [`FV (ast_Raise e) = FV e`;
   `FV (ast_Handle e pes) = FV e UNION FV_pes pes`;
   `FV (ast_Lit _21) = {}`;
   `FV (ast_Con _23 ls) = FV_list ls`;
   `FV (ast_Var id') = {id'}`;
   `FV (ast_Fun x e) = FV e DIFF {Short x}`;
   `FV (ast_App _25 es) = FV_list es`;
   `FV (ast_Log _26 e1 e2) = FV e1 UNION FV e2`;
   `FV (ast_If e1 e2 e3) = FV e1 UNION FV e2 UNION FV e3`;
   `FV (ast_Mat e pes) = FV e UNION FV_pes pes`;
   `FV (ast_Let xo e b) = FV e UNION (FV b DIFF (match xo with NONE
  -> {} | SOME x -> {Short x}))`;
   `FV (ast_Letrec defs b) = (FV_defs defs UNION FV b) DIFF
  set_of_list (MAP (Short o FST) defs)`;
   `FV (ast_Tannot e t) = FV e`;
   `FV (ast_Lannot e l) = FV e`;
   `FV_list [] = {}`;
   `FV_list (e :: es) = FV e UNION FV_list es`;
   `FV_pes [] = {}`;
   `FV_pes ((p,e) :: pes) =
         (FV e DIFF (IMAGE Short (set_of_list (ast_pat_bindings
           p)))) UNION FV_pes pes`;
   `FV_defs [] = {}`;
   `FV_defs ((_27,x,e) :: defs) =
         (FV e DIFF {Short x}) UNION FV_defs defs`];;

(* HOL4 semanticPrimitivesPropsScript.sml:663: the overload SFV,
   which the port expands *)

let FV_pes_MAP = cake_theorem "FV_pes_MAP"
  (fun () ->
    `FV_pes pes = BIGUNION (IMAGE (\(p,e). FV e DIFF (IMAGE Short
  (set_of_list (ast_pat_bindings p)))) (set_of_list pes))`)
  CHEAT_TAC;;

let FV_defs_MAP = cake_theorem "FV_defs_MAP"
  (fun () ->
    `!ls. FV_defs ls = BIGUNION (IMAGE (\(f,x,e). FV e DIFF {Short x})
  (set_of_list ls))`)
  CHEAT_TAC;;

let FV_dec_def = cake_define_list
  [`FV_dec (Dlet locs p e) = FV (ast_Mat e [(p,ast_Lit ARB)])`;
   `FV_dec (Dletrec locs defs) = FV (ast_Letrec defs (ast_Lit ARB))`;
   `FV_dec (Dtype _28 _29) = {}`;
   `FV_dec (Dtabbrev _30 _31 _32 _33) = {}`;
   `FV_dec (Dexn _34 _35 _36) = {}`];;

let nat_to_v_11 = cake_theorem "nat_to_v_11[simp]"
  (fun () ->
    `!i j. nat_to_v i = nat_to_v j <=> i = j`)
  CHEAT_TAC;;

let concrete_v_list = cake_theorem "concrete_v_list[simp]"
  (fun () ->
    `!xs. concrete_v_list xs = EVERY concrete_v xs`)
  CHEAT_TAC;;

let concrete_v_simps = cake_theorem "concrete_v_simps[simp]"
  (fun () ->
    `(concrete_v (semanticPrimitives_Litv l:semanticPrimitives_v) = T)
  /\
     (concrete_v (semanticPrimitives_Loc b n) = T) /\
     (concrete_v (semanticPrimitives_Conv stmp xs) = EVERY
       concrete_v xs) /\
     (concrete_v (semanticPrimitives_Vectorv xs) = EVERY concrete_v
       xs) /\
     (concrete_v (semanticPrimitives_Env id e) = F) /\
     (concrete_v (semanticPrimitives_Closure e2 nm x) = F) /\
     (concrete_v (semanticPrimitives_Recclosure e3 funs nm2) = F)`)
  CHEAT_TAC;;

let prim_type_cases = cake_theorem "prim_type_cases"
  (fun () ->
    `!ty.
       ty = ast_BoolT \/
       ty = ast_IntT \/
       ty = ast_CharT \/
       ty = ast_StrT \/
       ty = ast_WordT ast_W8 \/
       ty = ast_WordT ast_W64 \/
       ty = ast_Float64T`)
  CHEAT_TAC;;

let do_conversion_check_type = cake_theorem "do_conversion_check_type"
  (fun () ->
    `do_conversion v ty1 ty2 = SOME (INR res) ==>
     semanticPrimitives_check_type ty2 res`)
  CHEAT_TAC;;

let do_arith_check_type = cake_theorem "do_arith_check_type"
  (fun () ->
    `do_arith a ty vs = SOME (INR res) ==>
     semanticPrimitives_check_type ty res`)
  CHEAT_TAC;;

cake_hide [];;
