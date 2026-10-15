(* ======================================================== *)
(*  infer: ported from HOL4's
    compiler/inference/inferScript.sml  *)
(* ======================================================== *)

(*
  Definition of CakeML's type inferencer.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "lib/integer_word.ml";;
needs "lib/peg.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
(* HOL4 ancestors outside the port: string *)


new_type_abbrev("err_var",`: (mlstring,mlstring,mlstring
   list#t)namespace`);;

let loc_err_info_FIELDS = define_record "loc_err_info"
  ["loc","locs option";
   "err","(mlstring,mlstring,mlstring list#t)namespace"];;

let failwith_def = cake_define
  `(infer_failwith:loc_err_info->'ga->'gb->('gc,locs option#'ga)exc#'gb)
  l msg =
     (\s. (M_failure (loc_err_info_loc l,msg),s))`;;
hol4_overload "failwith" "infer_failwith";;

let guard_def = cake_define
  `guard P l msg = (if P then return one else failwith l msg)`;;

let read_def = cake_define
  `(read:'ga->('ga,'gb)exc#'ga) =
   (\s. (M_success s,s))`;;

let write_def = cake_define
  `(write:'ga->'ga->(1,'gb)exc#'ga) v =
   (\s. (M_success one,v))`;;

let lookup_st_ex_def = cake_define
  `lookup_st_ex l err id' ienv st =
     (match nsLookup ienv id' with NONE -> (M_failure
       (loc_err_info_loc l,concat [(implode "Undefined "); err;
       (implode ": "); id_to_string id']),st) | SOME v -> (M_success
       v,st))`;;

let infer_st_FIELDS = define_record "infer_st"
  ["next_uvar","num";
   "subst","(num,infer_t)fmap";
   "next_id","num"];;

let fresh_uvar_def = cake_define
  `(fresh_uvar:infer_st->(infer_t,'ga)exc#infer_st) =
   (\s. (M_success (Infer_Tuvar (infer_st_next_uvar
     s)),infer_st_next_uvar_fupd (K (infer_st_next_uvar s + 1)) s))`;;

let n_fresh_uvar_def = cake_define
  `n_fresh_uvar (n:num) =
   (if n = 0 then
     return [] else
     monad_bind fresh_uvar (\v. monad_bind (n_fresh_uvar (n - 1)) (\
        vs.
        return (v :: vs))))`;;

let n_fresh_id_def = cake_define
  `n_fresh_id n =
   (\s.
   (M_success (GENLIST (\x. infer_st_next_id s + x)
     n),infer_st_next_id_fupd (K (infer_st_next_id s + n)) s))`;;

(* Doesn't reset the ID component *)
let init_infer_state_def = cake_define
  `init_infer_state st = infer_st_subst_fupd (K FEMPTY)
  (infer_st_next_uvar_fupd (K 0) st)`;;

let init_state_def = cake_define
  `init_state =
   (\st.
     (M_success one,init_infer_state st))`;;

let add_constraint_def = cake_define
  `add_constraint (l:loc_err_info) t1 t2 =
   (\st.
     match t_unify (infer_st_subst st) t1 t2 with NONE ->
           (M_failure (loc_err_info_loc l,concat [(implode
             "Type mismatch between ");
                              inf_type_to_string (loc_err_info_err l)
                              (t_walkstar (infer_st_subst st) t1);
                              (implode " and ");
                              inf_type_to_string (loc_err_info_err l)
                              (t_walkstar (infer_st_subst st)
                                t2)]),st) | SOME s ->
           (M_success one,infer_st_subst_fupd (K s) st))`;;

let add_constraints_def = cake_define
  `add_constraints l x2 x3 =
        match (x2,x3) with
          ([],[]) ->
     return one
        | ((t1 :: ts1),(t2 :: ts2)) ->
     monad_bind (add_constraint l t1 t2) (\one. monad_bind
       (add_constraints l ts1 ts2) (\
        one.
        return one))
        | (_1,_2) ->
     failwith l ((implode
       "Internal error: Bad call to add_constraints"))`;;

let get_next_uvar_def = cake_define
  `get_next_uvar =
     (\st. (M_success (infer_st_next_uvar st),st))`;;

let apply_subst_def = cake_define
  `apply_subst t =
     monad_bind read (\st.
        return (t_walkstar (infer_st_subst st) t))`;;

let apply_subst_list_def = cake_define
  `apply_subst_list ts =
     monad_bind read (\st.
        return (MAP (t_walkstar (infer_st_subst st)) ts))`;;

(* We use a state argument for the inferencer's typing environment. This
   corresponds to the type system's typing environment
  The module and variable environment's types differ slightly.
*)

let inf_env_FIELDS = define_record "inf_env"
  ["inf_v","(mlstring,mlstring,num#infer_t)namespace";
   "inf_c","(mlstring,mlstring,mlstring list#t list#num)namespace";
   "inf_t","(mlstring,mlstring,mlstring list#t)namespace"];;

(* Generalise the unification variables greater than m, starting at
   deBruijn index n.
 * Return how many were generalised, the generalised type, and a
   substitution
 * that describes the generalisation *)
let generalise_def = cake_define
  `(generalise m n s (Infer_Tapp ts tc) =
     (let (num_gen,s',ts') = generalise_list m n s ts in
       (num_gen,s',Infer_Tapp ts' tc))) /\
   (generalise m n s (Infer_Tuvar uv) =
     (match FLOOKUP s uv with SOME n -> (0,s,Infer_Tvar_db n) | NONE
       ->
           (if m <= uv then
             (1,s |+ (uv,n),Infer_Tvar_db n) else
             (0,s,Infer_Tuvar uv)))) /\
   (generalise m n s (Infer_Tvar_db k) =
       (0,s,Infer_Tvar_db k)) /\
   (generalise_list m n s [] =
     (0,s,[])) /\
   (generalise_list m n s (t :: ts) =
     (let (num_gen,s',t') = generalise m n s t in
     let (num_gen',s'',ts') = generalise_list m (num_gen + n) s' ts
       in
       (num_gen + num_gen',s'',t' :: ts')))`;;

let infer_type_subst_def = cake_define
  `(infer_type_subst s (Tvar tv) =
     (match ALOOKUP s tv with SOME t -> t | NONE -> Infer_Tvar_db 0))
       /\
   (infer_type_subst s (Tvar_db n) =
     Infer_Tvar_db n) /\
   (infer_type_subst s (Tapp ts tn) =
     Infer_Tapp (infer_type_subst_list s ts) tn) /\
   (infer_type_subst_list s [] = []) /\
   (infer_type_subst_list s (x :: xs) =
     infer_type_subst s x :: infer_type_subst_list s xs)`;;

let infer_deBruijn_subst_def = cake_define
  `(infer_deBruijn_subst s (Infer_Tvar_db n) =
     (if n < LENGTH s then
       EL n s else
       Infer_Tvar_db (n - LENGTH s))) /\
   (infer_deBruijn_subst s (Infer_Tapp ts tn) =
     Infer_Tapp (infer_deBruijn_subst_list s ts) tn) /\
   (infer_deBruijn_subst s (Infer_Tuvar n) =
     Infer_Tuvar n) /\
   (infer_deBruijn_subst_list s [] = []) /\
   (infer_deBruijn_subst_list s (t :: ts) =
     infer_deBruijn_subst s t :: infer_deBruijn_subst_list s ts)`;;

let type_name_check_subst_def = cake_define
  `(type_name_check_subst l err_string_f tenvT fvs (Atvar tv) =
     monad_ignore_bind
       (guard (MEM tv fvs) l (err_string_f tv)) (
       return (Tvar tv))) /\
   (type_name_check_subst l f tenvT fvs (Attup ts) =
     monad_bind (type_name_check_subst_list l f tenvT fvs ts) (\
       ts'.
       return (Ttup ts'))) /\
   (type_name_check_subst l f tenvT fvs (Atfun t1 t2) =
     monad_bind (type_name_check_subst l f tenvT fvs t1) (\
       t1'. monad_bind (type_name_check_subst l f tenvT fvs t2) (\
       t2'.
       return (Tfn t1' t2')))) /\
   (type_name_check_subst l f tenvT fvs (Atapp ts tc) =
     monad_bind (type_name_check_subst_list l f tenvT fvs ts) (\
       ts'. monad_bind (lookup_st_ex l (implode "type constructor")
         tc tenvT) (\
       (tvs',t'). monad_ignore_bind
       (guard (LENGTH tvs' = LENGTH ts) l
                  (concat [(implode "Type constructor ");
                    id_to_string tc; (implode " given ");
                           toString (&LENGTH ts); (implode
                             " arguments, but expected ");
                           toString (&LENGTH tvs')])) (
       return (type_subst (alist_to_fmap (ZIP (tvs',ts'))) t'))))) /\
   (type_name_check_subst_list l f tenvT fvs [] = return []) /\
   (type_name_check_subst_list l f tenvT fvs (t :: ts) =
     monad_bind (type_name_check_subst l f tenvT fvs t) (\
       t'. monad_bind (type_name_check_subst_list l f tenvT fvs ts)
         (\
       ts'.
       return (t' :: ts'))))`;;

(* HOL4 ML code, not ported:
val type_name_check_subst_alt =
  type_name_check_subst_def
  |> SRULE [bind_guard, ignore_bind_guard]
  |> SRULE [st_ex_bind_pair]
  |> SRULE [st_ex_bind_def,st_ex_ignore_bind_def,lookup_st_ex_def,
            st_ex_return_def];
*)

let type_name_check_sub_def = cake_define
  `(type_name_check_sub l tenvT fvs (Atvar tv) =
        (\s. if MEM tv fvs then (M_success (Tvar tv),s) else
          (M_failure (loc_err_info_loc l,INR tv),s))) /\
   (type_name_check_sub l tenvT fvs (Attup ts) =
        (\s. match type_name_check_sub_list l tenvT fvs ts s with
               (M_success ts',s) -> (M_success (Ttup ts'),s) |
                 (M_failure x,s) -> (M_failure x,s))) /\
   (type_name_check_sub l tenvT fvs (Atfun t1 t2) =
        (\s. match type_name_check_sub l tenvT fvs t1 s with
               (M_success t1',s) ->
                 (match type_name_check_sub l tenvT fvs t2 s with
                    (M_success t2',s) -> (M_success (Tfn t1' t2'),s)
                      | (M_failure x,s) -> (M_failure x,s)) | (M_failure
                      x,s) -> (M_failure x,s))) /\
   (type_name_check_sub l tenvT fvs (Atapp ts tc) =
        (\s. match type_name_check_sub_list l tenvT fvs ts s with
               (M_success ts',s) ->
                 (match
                    (match nsLookup tenvT tc with
                      NONE ->
                        (M_failure
                           (loc_err_info_loc l,INL
                            (concat
                              [(implode "Undefined ");
                              (implode "type constructor"); (implode
                                ": ");
                              id_to_string tc])),s) | SOME v ->
                                (M_success v,s)) with
                    (M_success (y,z),s) ->
                      (if LENGTH y = LENGTH ts then
                        (M_success (type_subst (alist_to_fmap (ZIP
                          (y,ts'))) z),
                         s) else
                        (M_failure
                           (loc_err_info_loc l,INL
                            (concat
                              [(implode "Type constructor ");
                                id_to_string tc;
                              (implode " given "); toString (LENGTH
                                ts);
                              (implode " arguments, but expected ");
                              toString (LENGTH y)])),s)) | (M_failure
                                x,s) -> (M_failure x,s)) | (M_failure
                                x,s) -> (M_failure x,s))) /\
   (type_name_check_sub_list l tenvT fvs [] = (\s. (M_success [],s)))
     /\
   (type_name_check_sub_list l tenvT fvs (t :: ts) =
       (\s. match type_name_check_sub l tenvT fvs t s with
              (M_success t',s) ->
                (match type_name_check_sub_list l tenvT fvs ts s with
                   (M_success ts',s) -> (M_success (t' :: ts'),s)
                     | (M_failure x,s) -> (M_failure x,s)) |
                     (M_failure x,s) -> (M_failure x,s)))`;;

let find_dup_def = cake_define
  `find_dup [] = NONE /\
   find_dup (x :: xs) = (if MEM x xs then SOME x else find_dup xs)`;;

let check_dups_def = cake_define
  `(check_dups l f [] = return one) /\
   (check_dups l f (h :: t) =
      (if MEM h t then
        failwith l (f h) else
        check_dups l f t))`;;

let check_ctor_types_def = cake_define
  `(check_ctor_types l tenvT tvs [] = return one) /\
   (check_ctor_types l tenvT tvs ((cn,ts) :: ctors) =
     monad_ignore_bind
       (type_name_check_subst_list l
             (\tv. concat [(implode "Unbound type variable "); tv;
                           (implode
                             " in type definition with constructor ");
                             cn])
             tenvT tvs ts) (
       check_ctor_types l tenvT tvs ctors))`;;

let check_ctors_def = cake_define
  `(check_ctors l tenvT [] = return one) /\
   (check_ctors l tenvT ((tvs,tn,ctors) :: tds) =
     monad_ignore_bind
       (check_dups l
                  (\n. concat [(implode "Duplicate constructor "); n;
                              (implode
                                " in the definition of type "); tn])
                  (MAP FST ctors)) (monad_ignore_bind
       (check_dups l
                  (\n. concat [(implode
                    "Duplicate type variable binding "); n;
                              (implode
                                " in the definition of type "); tn])
                  tvs) (monad_ignore_bind
       (check_ctor_types l tenvT tvs ctors) (
       check_ctors l tenvT tds))))`;;

let check_type_definition_def = cake_define
  `check_type_definition l tenvT tds =
     monad_ignore_bind
       (check_dups l
                  (\n. concat [(implode
                    "Duplicate type constructor "); n;
                              (implode

      " in a mutually recursive type definition")])
                  (MAP (FST o SND) tds)) (
       check_ctors l tenvT tds)`;;

let infer_p_def = cake_define_list
  [`infer_p l ienv (Pvar n:ast_pat) =
        monad_bind fresh_uvar (\t.
           return (t,[(n,t)]))`;
   `infer_p l ienv Pany =
        monad_bind fresh_uvar (\t.
           return (t,[]))`;
   `infer_p l ienv (Plit (IntLit i):ast_pat) =
        return (Infer_Tapp [] Tint_num,[])`;
   `infer_p l ienv (Plit (Char s):ast_pat) =
        return (Infer_Tapp [] Tchar_num,[])`;
   `infer_p l ienv (Plit (StrLit s):ast_pat) =
        return (Infer_Tapp [] Tstring_num,[])`;
   `infer_p l ienv (Plit (Word8 w):ast_pat) =
        return (Infer_Tapp [] Tword8_num,[])`;
   `infer_p l ienv (Plit (Word64 w):ast_pat) =
        return (Infer_Tapp [] Tword64_num,[])`;
   `infer_p l ienv (Plit (Float64 f):ast_pat) =
        failwith l (implode "Floats cannot be used in patterns")`;
   `infer_p l ienv (Pcon cn_opt ps:ast_pat) =
        (match cn_opt with NONE ->
              monad_bind (infer_ps l ienv ps) (\(ts,tenv).
                 return (Infer_Tapp ts Ttup_num,tenv)) | SOME cn ->
              monad_bind (lookup_st_ex l (implode "constructor") cn
                (inf_env_inf_c ienv)) (\(tvs',ts,tn). monad_bind
                (infer_ps l ienv ps) (\
                 (ts'',tenv). monad_bind (n_fresh_uvar (LENGTH
                   tvs')) (\
                 ts'. monad_ignore_bind
                 (guard (LENGTH ts'' = LENGTH ts) l
                       (concat [(implode "Constructor ");
                         id_to_string cn; (implode " given ");
                              toString (&LENGTH ts''); (implode
                                " arguments, but expected ");
                              toString (&LENGTH ts)])) (monad_bind
                                (add_constraints l ts'' (MAP
                                (infer_type_subst (ZIP (tvs',ts'))) ts))
                                (\
                 one.
                 return (Infer_Tapp ts' tn,tenv)))))))`;
   `infer_p l ienv (Pref p:ast_pat) =
        monad_bind (infer_p l ienv p) (\(t,tenv).
          return (Infer_Tapp [t] Tref_num,tenv))`;
   `infer_p l ienv (Pas p v:ast_pat) =
        monad_bind (infer_p l ienv p) (\(t,tenv).
          return (t,tenv ++ [(v,t)]))`;
   `infer_p l ienv (Ptannot p t:ast_pat) =
       monad_bind (infer_p l ienv p) (\(t',tenv). monad_bind
         (type_name_check_subst l
                  (\tv. concat [(implode "Type variable "); tv;
                    (implode " found in type annotation. ");
                              (implode

      "Type variables are not supported in type annotations.")])
      (inf_env_inf_t
                  ienv) [] t) (\
          t''. monad_bind (add_constraint l t' (infer_type_subst []
            t'')) (\
          one.
          return (t',tenv))))`;
   `infer_ps l ienv [] =
        return ([],[])`;
   `infer_ps l ienv (p :: ps) =
        monad_bind (infer_p l ienv p) (\(t,tenv). monad_bind
          (infer_ps l ienv ps) (\
           (ts,tenv').
           return (t :: ts,tenv' ++ tenv)))`];;

let word_tc_def = cake_define
  `(word_tc W8 = Tword8_num) /\
   (word_tc W64 = Tword64_num)`;;

let op_to_string_def = cake_define
  `op_to_string x1 =
        match x1 with
          (Shift _3 _4 _5) -> ((implode "Shift"),1)
        | Equality -> ((implode "Equality"),2)
        | (Arith a ty) ->
        ((implode "Arith"),
         (match supported_arith a ty with SOME n -> (n:num) | NONE ->
           0))
        | (FromTo _6 _7) -> ((implode "FromTo"),1)
        | (Test _8 _9) -> ((implode "Test"),2)
        | Opapp -> ((implode "Opapp"),2)
        | Opassign -> ((implode "Opassign"),2)
        | Opref -> ((implode "Opref"),1)
        | Opderef -> ((implode "Opderef"),1)
        | Aw8alloc -> ((implode "Aw8alloc"),2)
        | Aw8sub -> ((implode "Aw8sub"),2)
        | Aw8length -> ((implode "Aw8length"),1)
        | Aw8update -> ((implode "Aw8update"),3)
        | Aw8sub_unsafe -> ((implode "Aw8sub_unsafe"),2)
        | Aw8update_unsafe -> ((implode "Aw8update_unsafe"),3)
        | XorAw8Str_unsafe -> ((implode "XorAw8Str_unsafe"),2)
        | CopyStrStr -> ((implode "CopyStrStr"),3)
        | CopyStrAw8 -> ((implode "CopyStrAw8"),5)
        | CopyAw8Str -> ((implode "CopyAw8Str"),3)
        | CopyAw8Aw8 -> ((implode "CopyAw8Aw8"),5)
        | Strsub -> ((implode "Strsub"),2)
        | Implode -> ((implode "Implode"),1)
        | Explode -> ((implode "Explode"),1)
        | Strlen -> ((implode "Strlen"),1)
        | Strcat -> ((implode "Strcat"),1)
        | VfromList -> ((implode "VfromList"),1)
        | Vsub -> ((implode "Vsub"),2)
        | Vsub_unsafe -> ((implode "Vsub_unsafe"),2)
        | Vlength -> ((implode "Vlength"),1)
        | Aalloc -> ((implode "Aalloc"),2)
        | AallocEmpty -> ((implode "AallocEmpty"),1)
        | AallocFixed -> ((implode "AallocFixed"),1)
        | Asub -> ((implode "Asub"),2)
        | Alength -> ((implode "Alength"),1)
        | Aupdate -> ((implode "Aupdate"),3)
        | Asub_unsafe -> ((implode "Asub_unsafe"),2)
        | Aupdate_unsafe -> ((implode "Aupdate_unsafe"),3)
        | ConfigGC -> ((implode "ConfigGC"),2)
        | Eval -> ((implode "Eval"),6)
        | Env_id -> ((implode "Env_id"),1)
        | ListAppend -> ((implode "ListAppend"),2)
        | (FFI _10) -> ((implode "FFI"),2)
        | (ThunkOp ForceThunk) -> ((implode "ForceThunk"),1)
        | (ThunkOp (AllocThunk _11)) -> ((implode "AllocThunk"),1)
        | (ThunkOp (UpdateThunk _12)) -> ((implode
          "UpdateThunk"),2)`;;

(* HOL4 overload (expanded in the port):
     Tem = Infer_Tapp [] *)

let t_num_of_def = cake_define
  `t_num_of x1 =
      match x1 with
        BoolT -> Tbool_num
      | IntT -> Tint_num
      | CharT -> Tchar_num
      | StrT -> Tstring_num
      | (WordT W8) -> Tword8_num
      | (WordT W64) -> Tword64_num
      | Float64T -> Tdouble_num`;;

let op_simple_constraints_def = cake_define
  `op_simple_constraints op =
     (match op with Arith a ty -> (match supported_arith a ty with
       NONE -> (F,[],(Infer_Tapp []) Tbool_num) | SOME arity ->
                          (T,REPLICATE arity ((Infer_Tapp [])
                            (t_num_of ty)),(Infer_Tapp []) (t_num_of
                            ty))) | FromTo ty1 ty2 ->
                            (supported_conversion ty1 ty2,
                           [(Infer_Tapp []) (t_num_of ty1)],
                           (Infer_Tapp []) (t_num_of ty2)) | Test
                             test ty -> (supported_test test ty,
                         [(Infer_Tapp []) (t_num_of ty); (Infer_Tapp
                           []) (t_num_of ty)],
                         (Infer_Tapp []) Tbool_num) | Shift wz _13
                           _14 -> (T,[(Infer_Tapp []) (word_tc
                           wz)],(Infer_Tapp []) (word_tc wz)) | Aw8alloc
                           -> (T,[(Infer_Tapp []) Tint_num; (Infer_Tapp
                           []) Tword8_num],(Infer_Tapp [])
                           Tword8array_num) | Aw8sub -> (T,[(Infer_Tapp
                           []) Tword8array_num; (Infer_Tapp [])
                           Tint_num],(Infer_Tapp []) Tword8_num) |
                           Aw8length -> (T,[(Infer_Tapp [])
                           Tword8array_num],(Infer_Tapp []) Tint_num) |
                           Aw8update -> (T,[(Infer_Tapp [])
                           Tword8array_num; (Infer_Tapp []) Tint_num;
                           (Infer_Tapp []) Tword8_num],
           (Infer_Tapp []) Ttup_num) | CopyStrStr -> (T,[(Infer_Tapp
             []) Tstring_num; (Infer_Tapp []) Tint_num; (Infer_Tapp [])
             Tint_num],
           (Infer_Tapp []) Tstring_num) | CopyStrAw8 ->
             (T,[(Infer_Tapp []) Tstring_num; (Infer_Tapp []) Tint_num;
             (Infer_Tapp []) Tint_num;
               (Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
                 Tint_num],(Infer_Tapp []) Ttup_num) | CopyAw8Str ->
                 (T,[(Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
                 Tint_num; (Infer_Tapp []) Tint_num],
           (Infer_Tapp []) Tstring_num) | CopyAw8Aw8 ->
             (T,[(Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
             Tint_num; (Infer_Tapp []) Tint_num;
               (Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
                 Tint_num],(Infer_Tapp []) Ttup_num) | Strsub ->
                 (T,[(Infer_Tapp []) Tstring_num; (Infer_Tapp [])
                 Tint_num],(Infer_Tapp []) Tchar_num) | Strlen ->
                 (T,[(Infer_Tapp []) Tstring_num],(Infer_Tapp [])
                 Tint_num) | ConfigGC -> (T,[(Infer_Tapp []) Tint_num;
                 (Infer_Tapp []) Tint_num],(Infer_Tapp []) Ttup_num) |
                 FFI _15 -> (T,[(Infer_Tapp []) Tstring_num; (Infer_Tapp
                 []) Tword8array_num],(Infer_Tapp []) Ttup_num) |
                 Implode -> (T,[Infer_Tapp [Infer_Tapp [] Tchar_num]
                 Tlist_num],
           (Infer_Tapp []) Tstring_num) | Explode ->
             (T,[(Infer_Tapp []) Tstring_num],Infer_Tapp [(Infer_Tapp
             []) Tchar_num] Tlist_num) | Strcat -> (T,[Infer_Tapp
             [(Infer_Tapp []) Tstring_num] Tlist_num],(Infer_Tapp [])
             Tstring_num) | _16 -> (F,[],(Infer_Tapp []) Tbool_num))`;;

let op_n_args_msg_def = cake_define
  `op_n_args_msg op n =
     (let (ops,args) = op_to_string op in
     concat [(implode "Primitive "); ops; (implode " given ");
         toString (&n); (implode " arguments, but expects ");
         toString (&args)])`;;

let constrain_op_def = cake_define
  `constrain_op l op ts s =
     (let (simple,op_arg_ts,op_ret_t) = op_simple_constraints op in
     if simple then
       if ~(LENGTH ts = LENGTH op_arg_ts) then failwith l
         (op_n_args_msg op (LENGTH ts)) s else monad_bind
         (add_constraints l ts (MAP I op_arg_ts)) (\one.
         return op_ret_t) s else match (op,ts) with (Equality,[t1;
           t2]) ->
          monad_bind (add_constraint l t1 t2) (\one.
             return (Infer_Tapp [] Tbool_num)) s | (Opapp,[t1; t2])
               ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t1 (Infer_Tapp [t2; uvar] Tfn_num)) (\
             one.
             return uvar)) s | (Opassign,[t1; t2]) ->
          monad_bind (add_constraint l t1 (Infer_Tapp [t2] Tref_num))
            (\one.
             return (Infer_Tapp [] Ttup_num)) s | (Opref,[t]) ->
               return (Infer_Tapp [t] Tref_num) s | (Opderef,[t]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t (Infer_Tapp [uvar] Tref_num)) (\
             one.
             return uvar)) s | (VfromList,[t]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t (Infer_Tapp [uvar] Tlist_num)) (\
             one.
             return (Infer_Tapp [uvar] Tvector_num))) s | (Vsub,[t1;
               t2]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t1 (Infer_Tapp [uvar] Tvector_num)) (\
             one. monad_bind (add_constraint l t2 (Infer_Tapp []
               Tint_num)) (\
             one.
             return uvar))) s | (Vlength,[t]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t (Infer_Tapp [uvar] Tvector_num)) (\
             one.
             return (Infer_Tapp [] Tint_num))) s | (Aalloc,[t1; t2])
               ->
          monad_bind (add_constraint l t1 (Infer_Tapp [] Tint_num))
            (\one.
             return (Infer_Tapp [t2] Tarray_num)) s |
               (AallocEmpty,[t1]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t1 (Infer_Tapp [] Ttup_num)) (\
             one.
             return (Infer_Tapp [uvar] Tarray_num))) s | (Asub,[t1;
               t2]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t1 (Infer_Tapp [uvar] Tarray_num)) (\
             one. monad_bind (add_constraint l t2 (Infer_Tapp []
               Tint_num)) (\
             one.
             return uvar))) s | (Alength,[t]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t (Infer_Tapp [uvar] Tarray_num)) (\
             one.
             return (Infer_Tapp [] Tint_num))) s | (Aupdate,[t1; t2;
               t3]) ->
          monad_bind (add_constraint l t1 (Infer_Tapp [t3]
            Tarray_num)) (\one. monad_bind (add_constraint l t2
            (Infer_Tapp [] Tint_num)) (\
             one.
             return (Infer_Tapp [] Ttup_num))) s | (ListAppend,[t1;
               t2]) ->
          monad_bind fresh_uvar (\uvar. monad_bind (add_constraint l
            t1 (Infer_Tapp [uvar] Tlist_num)) (\
             one. monad_bind (add_constraint l t2 (Infer_Tapp [uvar]
               Tlist_num)) (\
             one.
             return (Infer_Tapp [uvar] Tlist_num)))) s |
               (Vsub_unsafe,_17) -> failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (Asub_unsafe,_18) -> failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (Aupdate_unsafe,_19) -> failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (Aw8sub_unsafe,_20) -> failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (Aw8update_unsafe,_21) -> failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (XorAw8Str_unsafe,_22) -> failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (AallocFixed,_23) -> failwith l ((implode
               "Unsafe ops do not have a type")) s | (Eval,_24) ->
               failwith l ((implode "Unsafe ops do not have a type"))
               s | (Env_id,_25) -> failwith l ((implode
               "Unsafe ops do not have a type")) s | (ThunkOp
               _26,_27) -> failwith l ((implode
               "Thunk ops do not have a type")) s | (Arith _28
               _29,_30) -> failwith l ((implode "Type mismatch")) s |
               (FromTo _31 _32,_33) -> failwith l ((implode
               "Type mismatch")) s | (Test _34 _35,_36) -> failwith l
               ((implode "Type mismatch")) s | _37 -> failwith l
               (op_n_args_msg op (LENGTH ts)) s)`;;

let infer_e_def = cake_define_list
  [`infer_e l ienv (Raise e:ast_exp) =
        monad_bind (infer_e l ienv e) (\t2. monad_bind
          (add_constraint l t2 (Infer_Tapp [] Texn_num)) (\
           one. monad_bind fresh_uvar (\
           t1.
           return t1)))`;
   `infer_e l ienv (Handle e pes:ast_exp) =
        (if pes = [] then
          failwith l ((implode "No patterns in handle")) else
          monad_bind (infer_e l ienv e) (\t1. monad_bind (infer_pes
            l ienv pes (Infer_Tapp [] Texn_num) t1) (\
             one.
             return t1)))`;
   `infer_e l ienv (Lit (IntLit i):ast_exp) =
        return (Infer_Tapp [] Tint_num)`;
   `infer_e l ienv (Lit (Char c):ast_exp) =
        return (Infer_Tapp [] Tchar_num)`;
   `infer_e l ienv (Lit (StrLit s):ast_exp) =
        return (Infer_Tapp [] Tstring_num)`;
   `infer_e l ienv (Lit (Word8 w):ast_exp) =
        return (Infer_Tapp [] Tword8_num)`;
   `infer_e l ienv (Lit (Word64 _38):ast_exp) =
        return (Infer_Tapp [] Tword64_num)`;
   `infer_e l ienv (Lit (Float64 _39):ast_exp) =
        return (Infer_Tapp [] Tdouble_num)`;
   `infer_e l ienv (Var id':ast_exp) =
        monad_bind (lookup_st_ex l (implode "variable") id'
          (inf_env_inf_v ienv)) (\(tvs,t). monad_bind (n_fresh_uvar tvs)
          (\
           uvs.
           return (infer_deBruijn_subst uvs t)))`;
   `infer_e l ienv (Con cn_opt es:ast_exp) =
        (match cn_opt with
            NONE ->
             monad_bind (infer_es l ienv es) (\ts.
                return (Infer_Tapp ts Ttup_num)) | SOME cn ->
             monad_bind (lookup_st_ex l (implode "constructor") cn
               (inf_env_inf_c ienv)) (\(tvs',ts,tn). monad_bind
               (infer_es l ienv es) (\
                ts''. monad_bind (n_fresh_uvar (LENGTH tvs')) (\
                ts'. monad_ignore_bind
                 (guard (LENGTH ts'' = LENGTH ts) l
                       (concat [(implode "Constructor ");
                         id_to_string cn; (implode " given ");
                              toString (&LENGTH ts''); (implode
                                " arguments, but expected ");
                              toString (&LENGTH ts)])) (monad_bind
                                (add_constraints l ts'' (MAP
                                (infer_type_subst (ZIP (tvs',ts'))) ts))
                                (\
                one.
                return (Infer_Tapp ts' tn)))))))`;
   `infer_e l ienv (Fun x e:ast_exp) =
        monad_bind fresh_uvar (\t1. monad_bind (infer_e l
          (inf_env_inf_v_fupd (K (nsBind x (0,t1) (inf_env_inf_v ienv)))
          ienv) e) (\
           t2.
           return (Infer_Tapp [t1; t2] Tfn_num)))`;
   `infer_e l ienv (App op es:ast_exp) =
        monad_bind (infer_es l ienv es) (\ts. monad_bind
          (constrain_op l op ts) (\
           t.
           return t))`;
   `infer_e l ienv (Log log e1 e2:ast_exp) =
        monad_bind (infer_e l ienv e1) (\t1. monad_bind (infer_e l
          ienv e2) (\
           t2. monad_bind (add_constraint l t1 (Infer_Tapp []
             Tbool_num)) (\
           one. monad_bind (add_constraint l t2 (Infer_Tapp []
             Tbool_num)) (\
           one.
           return (Infer_Tapp [] Tbool_num)))))`;
   `infer_e l ienv (If e1 e2 e3:ast_exp) =
        monad_bind (infer_e l ienv e1) (\t1. monad_bind
          (add_constraint l t1 (Infer_Tapp [] Tbool_num)) (\
           one. monad_bind (infer_e l ienv e2) (\
           t2. monad_bind (infer_e l ienv e3) (\
           t3. monad_bind (add_constraint l t2 t3) (\
           one.
           return t2)))))`;
   `infer_e l ienv (Mat e pes:ast_exp) =
        (if pes = [] then
          failwith l ((implode "No patterns in case")) else
          monad_bind (infer_e l ienv e) (\t1. monad_bind fresh_uvar
            (\
             t2. monad_bind (infer_pes l ienv pes t1 t2) (\
             one.
             return t2))))`;
   `infer_e l ienv (Let x e1 e2:ast_exp) =
          monad_bind (infer_e l ienv e1) (\t1. monad_bind (infer_e l
            (inf_env_inf_v_fupd (K (nsOptBind x (0,t1) (inf_env_inf_v
            ienv))) ienv) e2) (\
             t2.
             return t2))`;
   `infer_e l ienv (Letrec funs e:ast_exp) =
        monad_ignore_bind
          (check_dups l (\n. concat [(implode
            "Duplicate function name "); n;
                              (implode

      " in mutually recursive function definition")])
                       (MAP FST funs)) (monad_bind (n_fresh_uvar
                         (LENGTH funs)) (\
           uvars. monad_bind (return (nsAppend (alist_to_ns (MAP2
             (\(f,x,e) uvar. (f,(0,uvar))) funs uvars)) (inf_env_inf_v
             ienv))) (\
           env'. monad_bind (infer_funs l (inf_env_inf_v_fupd (K
             env') ienv) funs) (\
           funs_ts. monad_bind (add_constraints l uvars funs_ts) (\
           one. monad_bind (infer_e l (inf_env_inf_v_fupd (K env')
             ienv) e) (\
           t.
           return t))))))`;
   `infer_e l ienv (Tannot e t:ast_exp) =
        monad_bind (infer_e l ienv e) (\t'. monad_bind
          (type_name_check_subst l
                  (\tv. concat [(implode "Type variable "); tv;
                    (implode " found in type annotation. ");
                              (implode

      "Type variables are not supported in type annotations.")])
      (inf_env_inf_t
                  ienv) [] t) (\
           t''. monad_bind (add_constraint l t' (infer_type_subst []
             t'')) (\
           one.
           return t')))`;
   `infer_e l ienv (Lannot e new_l:ast_exp) =
        infer_e (loc_err_info_loc_fupd (K (SOME new_l)) l) ienv e`;
   `infer_es l ienv [] =
        return []`;
   `infer_es l ienv (e :: es) =
        monad_bind (infer_e l ienv e) (\t. monad_bind (infer_es l
          ienv es) (\
           ts.
           return (t :: ts)))`;
   `infer_pes l ienv [] t1 t2 =
         return one`;
   `infer_pes l ienv ((p,e) :: pes) t1 t2 =
        monad_bind (infer_p l ienv p) (\(t1',env').
          monad_ignore_bind
          (check_dups l (\n. concat [(implode
            "Duplicate variable "); n; (implode " in pattern")])
                    (MAP FST env')) (monad_bind (add_constraint l t1
                      t1') (\
           one. monad_bind (infer_e l (inf_env_inf_v_fupd (K
             (nsAppend (alist_to_ns (MAP (\(n,t). (n,(0,t))) env'))
             (inf_env_inf_v ienv))) ienv) e) (\
           t2'. monad_bind (add_constraint l t2 t2') (\
           one. monad_bind (infer_pes l ienv pes t1 t2) (\
           one.
           return one))))))`;
   `infer_funs l ienv [] = return []`;
   `infer_funs l ienv ((f,x,e) :: funs) =
        monad_bind fresh_uvar (\uvar. monad_bind (infer_e l
          (inf_env_inf_v_fupd (K (nsBind x (0,uvar) (inf_env_inf_v
          ienv))) ienv) e) (\
           t. monad_bind (infer_funs l ienv funs) (\
           ts.
           return (Infer_Tapp [uvar; t] Tfn_num :: ts))))`];;

let extend_dec_ienv_def = cake_define
  `extend_dec_ienv ienv' ienv =
      mk_inf_env (nsAppend (inf_env_inf_v ienv') (inf_env_inf_v
        ienv)) (nsAppend (inf_env_inf_c ienv') (inf_env_inf_c ienv))
        (nsAppend (inf_env_inf_t ienv') (inf_env_inf_t ienv))`;;

let lift_ienv_def = cake_define
  `lift_ienv mn ienv =
     mk_inf_env (nsLift mn (inf_env_inf_v ienv)) (nsLift mn
       (inf_env_inf_c ienv)) (nsLift mn (inf_env_inf_t ienv))`;;

let infer_d_def = cake_define
  `(infer_d ienv (Dlet locs p e) =
     monad_bind init_state (\one. monad_bind get_next_uvar (\
        n. monad_bind (infer_e (mk_loc_err_info (SOME locs)
          (inf_env_inf_t ienv)) ienv e) (\
        t1. monad_bind (infer_p (mk_loc_err_info (SOME locs)
          (inf_env_inf_t ienv)) ienv p) (\
        (t2,env'). monad_ignore_bind
        (check_dups (mk_loc_err_info (SOME locs) (inf_env_inf_t
          ienv))
                      (\n. concat [(implode "Duplicate variable ");
                        n;
                              (implode

      " in the left-hand side of a definition")])
                   (MAP FST env')) (monad_bind (add_constraint
                     (mk_loc_err_info (SOME locs) (inf_env_inf_t ienv))
                     t1 t2) (\
        one. monad_bind (apply_subst_list (MAP SND env')) (\
        ts. monad_bind (return (generalise_list n 0 FEMPTY ts)) (\
        (num_tvs,s,ts'). monad_bind (guard (num_tvs = 0 \/ is_value
          e) (mk_loc_err_info (SOME locs) (inf_env_inf_t ienv))
                    ((implode "Value restriction violated"))) (\
        one.
        return (mk_inf_env (alist_to_ns (ZIP (MAP FST env',MAP (\t.
          (num_tvs,t)) ts'))) nsEmpty nsEmpty))))))))))) /\
   (infer_d ienv (Dletrec locs funs) =
     monad_ignore_bind
       (check_dups (mk_loc_err_info (SOME locs) (inf_env_inf_t ienv))
          (\n. concat [(implode "Duplicate function name "); n;
               (implode
                 " a mutually recursive function definition")])
                  (MAP FST funs)) (monad_bind init_state (\
        one. monad_bind get_next_uvar (\
        next. monad_bind (n_fresh_uvar (LENGTH funs)) (\
        uvars. monad_bind (return (nsAppend (alist_to_ns (MAP2
          (\(f,x,e) uvar. (f,(0,uvar))) funs uvars)) (inf_env_inf_v
          ienv))) (\
        env'. monad_bind (infer_funs (mk_loc_err_info (SOME locs)
          (inf_env_inf_t ienv))
                              (inf_env_inf_v_fupd (K env') ienv)
                                funs) (\
        funs_ts. monad_bind (add_constraints (mk_loc_err_info (SOME
          locs) (inf_env_inf_t ienv)) uvars funs_ts) (\
        one. monad_bind (apply_subst_list uvars) (\
        ts. monad_bind (return (generalise_list next 0 FEMPTY ts)) (\
        (num_gen,s,ts').
        return (mk_inf_env (alist_to_ns (MAP2 (\(f,x,e) t.
          (f,(num_gen,t))) funs ts')) nsEmpty nsEmpty))))))))))) /\
   (infer_d ienv (Dtype locs tdefs) =
     monad_bind (n_fresh_id (LENGTH tdefs)) (\
        tids. monad_bind (return (alist_to_ns (MAP2 (\(tvs,tn,ctors)
          i. (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs tids))) (\
        ienvT1. monad_bind (return (nsAppend ienvT1 (inf_env_inf_t
          ienv))) (\
        ienvT2. monad_ignore_bind
        (check_type_definition (mk_loc_err_info (SOME locs)
          (inf_env_inf_t ienv)) ienvT2 tdefs) (
        return (mk_inf_env nsEmpty (build_ctor_tenv ienvT2 tdefs
          tids) ienvT1)))))) /\
   (infer_d ienv (Dtabbrev locs tvs tn t) =
     monad_ignore_bind
       (check_dups (mk_loc_err_info (SOME locs) (inf_env_inf_t ienv))
          (\n. concat [(implode
            "Duplicate type variable bindings for ");
                       n; (implode " in type abbreviation ");
                       tn])
                 tvs) (monad_bind (type_name_check_subst
                   (mk_loc_err_info (SOME locs) (inf_env_inf_t ienv))
               (\tv. concat [(implode "Unbound type variable "); tv;
                 (implode " in type abbreviation "); tn]) (inf_env_inf_t
               ienv) tvs t) (\
        t'.
        return (mk_inf_env nsEmpty nsEmpty (nsSing tn (tvs,t'))))))
          /\
   (infer_d ienv (Dexn locs cn ts) =
     monad_bind (type_name_check_subst_list (mk_loc_err_info (SOME
       locs) (inf_env_inf_t ienv))
               (\tv. concat [(implode "Type variable "); tv; (implode
                 " found in declaration of exception "); cn;
                             (implode

      ". Type variables are not allowed in exception declarations.")])
      (inf_env_inf_t
               ienv) [] ts) (\
       ts'.
       return (mk_inf_env nsEmpty (nsSing cn ([],ts',Texn_num))
         nsEmpty))) /\
   (infer_d ienv (Denv n) =
     failwith (mk_loc_err_info NONE (inf_env_inf_t ienv))
       ((implode "Env declaration (Denv) is not supported."))) /\
   (infer_d ienv (Dmod mn ds) =
     monad_bind (infer_ds ienv ds) (\ienv'.
        return (lift_ienv mn ienv'))) /\
   (infer_d ienv (Dlocal lds ds) =
     monad_bind (infer_ds ienv lds) (\ienv'.
       infer_ds (extend_dec_ienv ienv' ienv) ds)) /\
   (infer_ds ienv [] =
     return (mk_inf_env nsEmpty nsEmpty nsEmpty)) /\
   (infer_ds ienv (d :: ds) =
     monad_bind (infer_d ienv d) (\
       ienv'. monad_bind (infer_ds (extend_dec_ienv ienv' ienv) ds)
         (\
       ienv''.
       return (extend_dec_ienv ienv'' ienv'))))`;;

(* The starting Id should be greater than Tlist_num :: (Tbool_num ::
   prim_type_nums) *)
let start_type_id_def = cake_define
  `start_type_id =
     ITLIST MAX (Tlist_num :: Tbool_num :: prim_type_nums) 0 + 1`;;

let infertype_prog_def = cake_define
  `infertype_prog ienv prog =
     (match FST (infer_ds ienv prog (init_infer_state (mk_infer_st
       0 FEMPTY start_type_id))) with M_success new_ienv -> M_success
       (extend_dec_ienv new_ienv ienv) | M_failure x -> M_failure x)`;;

let infertype_prog_inc_def = cake_define
  `infertype_prog_inc (ienv,next_id) prog =
   (match infer_ds ienv prog (init_infer_state (mk_infer_st ARB ARB
     next_id)) with
     (M_success new_ienv,st) ->
     (M_success (extend_dec_ienv new_ienv ienv,infer_st_next_id
       st)) | (M_failure x,_40) -> M_failure x)`;;

let init_config_def = cake_define
  `(infer_init_config:inf_env) =
     mk_inf_env nsEmpty (?_c prim_tenv) (type_env_t prim_tenv)`;;
hol4_overload "init_config" "infer_init_config";;

(* The following aren't needed to run the inferencer, but are useful in
   the proofs
 * about it *)

let infer_deBruijn_inc_def = cake_define
  `(infer_deBruijn_inc n (Infer_Tvar_db m) =
     Infer_Tvar_db (m + n)) /\
   (infer_deBruijn_inc n (Infer_Tapp ts tn) =
     Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn) /\
   (infer_deBruijn_inc n (Infer_Tuvar m) =
     Infer_Tuvar m)`;;

let infer_subst_def = cake_define
  `(infer_subst s (Infer_Tvar_db n) = Infer_Tvar_db n) /\
   (infer_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (infer_subst
     s) ts) tc) /\
   (infer_subst s (Infer_Tuvar n) =
     (match FLOOKUP s n with
         NONE -> Infer_Tuvar n | SOME m -> Infer_Tvar_db m))`;;

let pure_add_constraints_def = cake_define
  `(pure_add_constraints s [] s' = (s = s')) /\
   (pure_add_constraints s1 ((t1,t2) :: rest) s' =
     (?s2. (t_unify s1 t1 t2 = SOME s2) /\
          pure_add_constraints s2 rest s'))`;;

let check_t_def = cake_define
  `(check_t n uvars (Infer_Tuvar v) = (v IN uvars)) /\
   (check_t n uvars (Infer_Tvar_db n') =
     (n' < n)) /\
   (check_t n uvars (Infer_Tapp ts tc) = EVERY (check_t n uvars)
     ts)`;;

let ienv_val_ok_def = cake_define
  `ienv_val_ok uvars env =
     nsAll (\x (tvs,t). check_t tvs uvars t) env`;;

let check_s_def = cake_define
  `check_s tvs uvs s =
     (!uv. uv IN FDOM s ==> check_t tvs uvs (FAPPLY s uv))`;;

(* Adding the constraints extra_constraints moves the constraint set
   from s1 to
 * s2, and s2 is required to be complete in that it assigns to (at
   least) all
 * the uvars ≤ next_uvar, and when we apply it to any uvar, we get back
   a type
 * without any uvars in it. *)
let sub_completion_def = cake_define
  `sub_completion tvs next_uvar s1 extra_constraints s2 =
     (pure_add_constraints s1 extra_constraints s2 /\
      (count next_uvar SUBSET FDOM s2) /\
      (!uv. uv IN FDOM s2 ==> check_t tvs {} (t_walkstar s2
        (Infer_Tuvar uv))))`;;

(* printing of types *)

(* HOL4 termination: \\ fs [LESS_EQ,LENGTH_FILTER_LEQ] *)
let alist_nub_def = cake_define_wf
  `MEASURE LENGTH`
  `alist_nub [] = [] /\
   alist_nub ((x,y) :: xs) = (x,y) :: alist_nub (FILTER (\t. ~(x =
     FST t)) xs)`;;

let ns_nub_def = cake_define
  `ns_nub (Bind xs ys) = Bind (alist_nub xs) (alist_nub (inner_ns_nubs
  ys)) /\
   inner_ns_nubs [] = [] /\
   inner_ns_nubs ((x,y) :: tl) = (x,ns_nub y) :: inner_ns_nubs tl`;;

let ns_to_alist_def = cake_define
  `(ns_to_alist (Bind [] []) = []) /\
   (ns_to_alist (Bind [] ((n,x) :: ms)) =
     MAP (\(x,y). (^ (^ n (implode ".")) x,y)) (ns_to_alist x) ++
     ns_to_alist (Bind [] ms)) /\
   (ns_to_alist (Bind ((s,x) :: xs) m) = (s,x) :: ns_to_alist
     (Bind xs m))`;;

let inf_env_to_types_string_def = cake_define
  `inf_env_to_types_string s =
     (let l = ns_to_alist (ns_nub (inf_env_inf_v s)) in
     let xs = MAP (\(n,_41,t). concat [n; (implode ": ");
                              inf_type_to_string (inf_env_inf_t s) t;
                              (implode "\n")]) l in
        REVERSE xs)`;;
