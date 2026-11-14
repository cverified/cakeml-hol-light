(* ======================================================== *)
(*  infer: ported from HOL4's
    compiler/inference/inferScript.sml
    A definition theory, with 51 definitions, 3 datatypes and 22
    theorems.  Needed by 9 files of the port.  *)
(* ======================================================== *)

(*
  Definition of CakeML's type inferencer.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/inference/unify.ml";;
needs "compiler/parsing/cmlPEG.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/peg.ml";;
needs "lib/term.ml";;
needs "misc/misc.ml";;
needs "pancake/panLang.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/primTypes.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "infer"
  ["ast"; "infer_t"; "misc"; "ml_monadBase"; "namespace";
   "namespaceProps"; "primTypes"; "typeSystem"; "unify"];;

let _ = do_list hide_constant ["not"];;
(* HOL4 ancestors outside the port: string *)

hol4_overload "++" "otherwise";;


new_type_abbrev("err_var",`: (mlstring,mlstring,mlstring
   list#t)namespace`);;

let loc_err_info_FIELDS = define_record "loc_err_info"
  ["loc","locs option";
   "err","(mlstring,mlstring,mlstring list#t)namespace"];;

let failwith_def = new_definition
  `(infer_failwith:loc_err_info->'a->'b->('c,locs option#'a)exc#'b) l
  msg =
     (\s. (M_failure (loc_err_info_loc l,msg),s))`;;
hol4_overload "failwith" "infer_failwith";;

let guard_def = new_definition
  `infer_guard P l msg = (if P then st_ex_return one else
  infer_failwith l msg)`;;
hol4_overload "guard" "infer_guard";;

let read_def = new_definition
  `(read:'a->('a,'b)exc#'a) =
   (\s. (M_success s,s))`;;

let write_def = new_definition
  `(write:'a->'a->(1,'b)exc#'a) v =
   (\s. (M_success one,v))`;;

let lookup_st_ex_def = new_definition
  `lookup_st_ex l err id' ienv st =
     (match nsLookup ienv id' with NONE -> (M_failure
       (loc_err_info_loc l,mlstring_concat [(implode "Undefined ");
       err; (implode ": "); id_to_string id']),st) | SOME v ->
       (M_success v,st))`;;

let infer_st_FIELDS = define_record "infer_st"
  ["next_uvar","num";
   "subst","(num,infer_t)fmap";
   "next_id","num"];;

let fresh_uvar_def = new_definition
  `(fresh_uvar:infer_st->(infer_t,'a)exc#infer_st) =
   (\s. (M_success (Infer_Tuvar (infer_st_next_uvar
     s)),infer_st_next_uvar_fupd (K (infer_st_next_uvar s + 1)) s))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let n_fresh_uvar_def,n_fresh_uvar_ind = define_wf
  `MEASURE (\x0. (\n. n) x0)`
  [`n_fresh_uvar (n:num) =
   (if n = 0 then
     st_ex_return [] else
     st_ex_bind fresh_uvar (\v. st_ex_bind (n_fresh_uvar (n - 1)) (\
        vs.
        st_ex_return (CONS v vs))))`];;

let n_fresh_id_def = new_definition
  `n_fresh_id n =
   (\s.
   (M_success (list_of_seq (\x. infer_st_next_id s + x)
     n),infer_st_next_id_fupd (K (infer_st_next_id s + n)) s))`;;

(* Doesn't reset the ID component *)
let init_infer_state_def = new_definition
  `init_infer_state st = infer_st_subst_fupd (K FEMPTY)
  (infer_st_next_uvar_fupd (K 0) st)`;;

let init_state_def = new_definition
  `init_state =
   (\st.
     (M_success one,init_infer_state st))`;;

let add_constraint_def = new_definition
  `add_constraint (l:loc_err_info) t1 t2 =
   (\st.
     match t_unify (infer_st_subst st) t1 t2 with NONE ->
           (M_failure (loc_err_info_loc l,mlstring_concat [(implode
             "Type mismatch between ");
                              inf_type_to_string (loc_err_info_err l)
                              (t_walkstar (infer_st_subst st) t1);
                              (implode " and ");
                              inf_type_to_string (loc_err_info_err l)
                              (t_walkstar (infer_st_subst st)
                                t2)]),st) | SOME s ->
           (M_success one,infer_st_subst_fupd (K s) st))`;;

let _ = size_thms "infer_t";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let add_constraints_def,add_constraints_ind = define_wf
  `MEASURE (\(x0,x1,x2). infer_t_size1 x1 + infer_t_size1 x2)`
  [`add_constraints l x2 x3 =
        match (x2,x3) with
          ([],[]) ->
     st_ex_return one
        | ((CONS t1 ts1),(CONS t2 ts2)) ->
     st_ex_bind (add_constraint l t1 t2) (\one. st_ex_bind
       (add_constraints l ts1 ts2) (\
        one.
        st_ex_return one))
        | (_1,_2) ->
     infer_failwith l ((implode
       "Internal error: Bad call to add_constraints"))`];;

let get_next_uvar_def = new_definition
  `get_next_uvar =
     (\st. (M_success (infer_st_next_uvar st),st))`;;

let apply_subst_def = new_definition
  `apply_subst t =
     st_ex_bind read (\st.
        st_ex_return (t_walkstar (infer_st_subst st) t))`;;

let apply_subst_list_def = new_definition
  `apply_subst_list ts =
     st_ex_bind read (\st.
        st_ex_return (MAP (t_walkstar (infer_st_subst st)) ts))`;;

(* We use a state argument for the inferencer's typing environment. This corresponds to the type system's typing environment
  The module and variable environment's types differ slightly.
*)

let inf_env_FIELDS = define_record "inf_env"
  ["inf_v","(mlstring,mlstring,num#infer_t)namespace";
   "inf_c","(mlstring,mlstring,mlstring list#t list#num)namespace";
   "inf_t","(mlstring,mlstring,mlstring list#t)namespace"];;

(* Generalise the unification variables greater than m, starting at deBruijn index n.
 * Return how many were generalised, the generalised type, and a substitution
 * that describes the generalisation *)
let generalise_def,generalise_ind = define_mutual_rec
  [`generalise m n s (Infer_Tapp ts tc) =
      (let (num_gen,s',ts') = generalise_list m n s ts in
        (num_gen,s',Infer_Tapp ts' tc))`;
   `generalise m n s (Infer_Tuvar uv) =
      (match FLOOKUP s uv with SOME n -> (0,s,Infer_Tvar_db n) |
        NONE ->
            (if m <= uv then
              (1,s |+ (uv,n),Infer_Tvar_db n) else
              (0,s,Infer_Tuvar uv)))`;
   `generalise m n s (Infer_Tvar_db k) =
        (0,s,Infer_Tvar_db k)`;
   `generalise_list m n s [] =
      (0,s,[])`;
   `generalise_list m n s (CONS t ts) =
      (let (num_gen,s',t') = generalise m n s t in
      let (num_gen',s'',ts') = generalise_list m (num_gen + n) s' ts
        in
        (num_gen + num_gen',s'',CONS t' ts'))`];;

let infer_type_subst_def,infer_type_subst_ind = define_mutual_rec
  [`infer_type_subst s (Tvar tv) =
      (match ALOOKUP s tv with SOME t -> t | NONE ->
        Infer_Tvar_db 0)`;
   `// should not happen
    infer_type_subst s (Tvar_db n) =
    Infer_Tvar_db n`;
   `infer_type_subst s (Tapp ts tn) =
      Infer_Tapp (infer_type_subst_list s ts) tn`;
   `infer_type_subst_list s [] = []`;
   `infer_type_subst_list s (CONS x xs) = CONS (infer_type_subst s
  x) (infer_type_subst_list s xs)`];;

let infer_type_subst_alt = prove
 (`(infer_type_subst s (Tvar tv) =
     (match ALOOKUP s tv with SOME t -> t | NONE -> Infer_Tvar_db 0))
       /\
   (
     // should not happen
     infer_type_subst s (Tvar_db n) =
     Infer_Tvar_db n) /\
   (infer_type_subst s (Tapp ts tn) =
     Infer_Tapp (MAP (infer_type_subst s) ts) tn)`,
  CHEAT_TAC);;

let infer_deBruijn_subst_def,infer_deBruijn_subst_ind =
  define_mutual_rec
  [`infer_deBruijn_subst s (Infer_Tvar_db n) =
      (if n < LENGTH s then
        EL n s else
        // should not happen
        Infer_Tvar_db (n - LENGTH s))`;
   `infer_deBruijn_subst s (Infer_Tapp ts tn) =
      Infer_Tapp (infer_deBruijn_subst_list s ts) tn`;
   `infer_deBruijn_subst s (Infer_Tuvar n) =
      Infer_Tuvar n`;
   `infer_deBruijn_subst_list s [] = []`;
   `infer_deBruijn_subst_list s (CONS t ts) = CONS
  (infer_deBruijn_subst s t) (infer_deBruijn_subst_list s ts)`];;

let infer_deBruijn_subst_alt = prove
 (`(infer_deBruijn_subst s (Infer_Tvar_db n) =
     (if n < LENGTH s then
       EL n s else
       // should not happen
       Infer_Tvar_db (n - LENGTH s))) /\
   (infer_deBruijn_subst s (Infer_Tapp ts tn) =
     Infer_Tapp (MAP (infer_deBruijn_subst s) ts) tn) /\
   (infer_deBruijn_subst s (Infer_Tuvar n) =
     Infer_Tuvar n)`,
  CHEAT_TAC);;

let _ = size_thms "ast_t";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let type_name_check_subst_def,type_name_check_subst_ind =
  define_mutual_wf
  `MEASURE (sum_measure (\(x0,x1,x2,x3,x4). ast_t_size x4)
  (\(x0,x1,x2,x3,x4). ast_t_size1 x4))`
  [`type_name_check_subst l err_string_f tenvT fvs (Atvar tv) =
        st_ex_ignore_bind
          (infer_guard (MEM tv fvs) l (err_string_f tv)) (
          st_ex_return (Tvar tv))`;
   `type_name_check_subst l f tenvT fvs (Attup ts) =
        st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) (\
          ts'.
          st_ex_return (Ttup ts'))`;
   `type_name_check_subst l f tenvT fvs (Atfun t1 t2) =
        st_ex_bind (type_name_check_subst l f tenvT fvs t1) (\
          t1'. st_ex_bind (type_name_check_subst l f tenvT fvs t2)
            (\
          t2'.
          st_ex_return (Tfn t1' t2')))`;
   `type_name_check_subst l f tenvT fvs (Atapp ts tc) =
        st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) (\
          ts'. st_ex_bind (lookup_st_ex l (implode
            "type constructor") tc tenvT) (\
          (tvs',t'). st_ex_ignore_bind
          (infer_guard (LENGTH tvs' = LENGTH ts) l
                     (mlstring_concat [(implode
                       "Type constructor "); id_to_string tc; (implode
                       " given ");
                              toString (&(LENGTH ts)); (implode
                                " arguments, but expected ");
                              toString (&(LENGTH tvs'))])) (
          st_ex_return (type_subst (alist_to_fmap (ZIP tvs' ts'))
            t'))))`;
   `type_name_check_subst_list l f tenvT fvs [] = st_ex_return []`;
   `type_name_check_subst_list l f tenvT fvs (CONS t ts) =
        st_ex_bind (type_name_check_subst l f tenvT fvs t) (\
          t'. st_ex_bind (type_name_check_subst_list l f tenvT fvs
            ts) (\
          ts'.
          st_ex_return (CONS t' ts')))`];;

let bind_guard = prove
 (`st_ex_bind (infer_guard b l x) g =
   (\s. if b then g one s else (M_failure (loc_err_info_loc
     l,x),s))`,
  CHEAT_TAC);;

let ignore_bind_guard = prove
 (`st_ex_ignore_bind (infer_guard b l x) g =
   (\s. if b then g s else (M_failure (loc_err_info_loc l,x),s))`,
  CHEAT_TAC);;

let st_ex_bind_pair = prove
 (`monad_bind x f =
   (\s.
      match x s with (M_success (y,z),s) -> f (y,z) s | (M_failure
        x,s) -> (M_failure x,s))`,
  CHEAT_TAC);;

let st_ex_bind_triple = prove
 (`monad_bind x f =
   (\s.
      match x s with (M_success (y,z,q),s) -> f (y,z,q) s |
        (M_failure x,s) -> (M_failure x,s))`,
  CHEAT_TAC);;

(* HOL4 inferScript.sml:307-312: ML code, not ported *)

let _ = size_thms "ast_t";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let type_name_check_sub_def,type_name_check_sub_ind = define_mutual_wf
  `MEASURE (sum_measure (\(x0,x1,x2,x3). ast_t_size x3)
  (\(x0,x1,x2,x3). ast_t_size1 x3))`
  [`type_name_check_sub l tenvT fvs (Atvar tv) =
            (\s. if MEM tv fvs then (M_success (Tvar tv),s) else
              (M_failure (loc_err_info_loc l,INR tv),s))`;
   `type_name_check_sub l tenvT fvs (Attup ts) =
            (\s. match type_name_check_sub_list l tenvT fvs ts s
              with
                   (M_success ts',s) -> (M_success (Ttup ts'),s)
                     | (M_failure x,s) -> (M_failure x,s))`;
   `type_name_check_sub l tenvT fvs (Atfun t1 t2) =
            (\s. match type_name_check_sub l tenvT fvs t1 s with
                   (M_success t1',s) ->
                     (match type_name_check_sub l tenvT fvs t2 s
                       with
                        (M_success t2',s) -> (M_success (Tfn t1'
                          t2'),s) | (M_failure x,s) -> (M_failure
                          x,s)) | (M_failure x,s) -> (M_failure x,s))`;
   `type_name_check_sub l tenvT fvs (Atapp ts tc) =
            (\s. match type_name_check_sub_list l tenvT fvs ts s
              with
                   (M_success ts',s) ->
                     (match
                        (match nsLookup tenvT tc with
                          NONE ->
                            (M_failure
                              (loc_err_info_loc l,INL
                              (mlstring_concat
                              [(implode "Undefined ");
                              (implode "type constructor"); (implode
                                ": ");
                              id_to_string tc])),s) | SOME v ->
                                (M_success v,s)) with
                        (M_success (y,z),s) ->
                          (if LENGTH y = LENGTH ts then
                            (M_success (type_subst (alist_to_fmap
                              (ZIP y ts')) z),
                             s) else
                            (M_failure
                              (loc_err_info_loc l,INL
                              (mlstring_concat
                              [(implode "Type constructor ");
                                id_to_string tc;
                              (implode " given "); toString (LENGTH
                                ts);
                              (implode " arguments, but expected ");
                              toString (LENGTH y)])),s)) |
                                (M_failure x,s) -> (M_failure x,s)) |
                                (M_failure x,s) -> (M_failure x,s))`;
   `type_name_check_sub_list l tenvT fvs [] = (\s. (M_success [],s))`;
   `type_name_check_sub_list l tenvT fvs (CONS t ts) =
           (\s. match type_name_check_sub l tenvT fvs t s with
                  (M_success t',s) ->
                    (match type_name_check_sub_list l tenvT fvs ts s
                      with
                       (M_success ts',s) -> (M_success (CONS t'
                         ts'),s) | (M_failure x,s) -> (M_failure
                         x,s)) | (M_failure x,s) -> (M_failure
                         x,s))`];;

let to_type_name_check_sub = prove
 (`(!t l f tenvT fvs.
      type_name_check_subst l f tenvT fvs t =
      (\(s:'a). match type_name_check_sub l tenvT fvs t s with
        (M_failure (x,INR r),s) -> (M_failure (x,f r),s) | (M_failure
        (x,INL r),s) -> (M_failure (x,r),s) | (M_success y,s) ->
        (M_success y,s))) /\
   (!t l f tenvT fvs.
      type_name_check_subst_list l f tenvT fvs t =
      (\(s:'a). match type_name_check_sub_list l tenvT fvs t s with
        (M_failure (x,INR r),s) -> (M_failure (x,f r),s) | (M_failure
        (x,INL r),s) -> (M_failure (x,r),s) | (M_success y,s) ->
        (M_success y,s)))`,
  CHEAT_TAC);;

let bind_type_name_check_subst = prove
 (`(st_ex_bind (type_name_check_subst l f tenvT fvs t) g =
    (\(s:'a). match type_name_check_sub l tenvT fvs t s with
      (M_failure (x,INR r),s) -> (M_failure (x,f r),s) | (M_failure
      (x,INL r),s) -> (M_failure (x,r),s) | (M_success y,s) -> g y s))
      /\
   (st_ex_bind (type_name_check_subst_list l f tenvT fvs ts) gs =
    (\(s:'a). match type_name_check_sub_list l tenvT fvs ts s with
      (M_failure (x,INR r),s) -> (M_failure (x,f r),s) | (M_failure
      (x,INL r),s) -> (M_failure (x,r),s) | (M_success y,s) -> gs y
      s))`,
  CHEAT_TAC);;

let ignore_bind_type_name_check_subst = prove
 (`(st_ex_ignore_bind (type_name_check_subst l f tenvT fvs t) g =
    (\(s:'a). match type_name_check_sub l tenvT fvs t s with
      (M_failure (x,INR r),s) -> (M_failure (x,f r),s) | (M_failure
      (x,INL r),s) -> (M_failure (x,r),s) | (M_success y,s) -> g s)) /\
   (st_ex_ignore_bind (type_name_check_subst_list l f tenvT fvs ts)
     gs =
    (\(s:'a). match type_name_check_sub_list l tenvT fvs ts s with
      (M_failure (x,INR r),s) -> (M_failure (x,f r),s) | (M_failure
      (x,INL r),s) -> (M_failure (x,r),s) | (M_success y,s) -> gs s))`,
  CHEAT_TAC);;

let find_dup_def,find_dup_ind = define_rec
  [`find_dup [] = NONE`;
   `find_dup (CONS x xs) = (if MEM x xs then SOME x else find_dup
  xs)`];;

let _ = size_thms "loc_err_info";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let check_dups_def,check_dups_ind = define_wf
  `MEASURE (\(x0,x1,x2). loc_err_info_size x0)`
  [`check_dups l f [] = st_ex_return one`;
   `check_dups l f (CONS h t) =
         (if MEM h t then
           infer_failwith l (f h) else
           check_dups l f t)`];;

let check_dups_eq_find_dup = prove
 (`!xs.
     st_ex_ignore_bind (check_dups l f xs) g =
     (\s. match find_dup xs with NONE -> g s | SOME x -> (M_failure
       (loc_err_info_loc l,f x),s))`,
  CHEAT_TAC);;

let _ = size_thms "ast_t";;
let _ = size_thms "mlstring";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let check_ctor_types_def,check_ctor_types_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). list_size (pair_size mlstring_size
  ast_t_size1) x3)`
  [`check_ctor_types l tenvT tvs [] = st_ex_return one`;
   `check_ctor_types l tenvT tvs (CONS (cn,ts) ctors) =
        st_ex_ignore_bind
          (type_name_check_subst_list l
                (\tv. mlstring_concat [(implode
                  "Unbound type variable "); tv;
                              (implode

      " in type definition with constructor "); cn])
                tenvT tvs ts) (
          check_ctor_types l tenvT tvs ctors)`];;

(* HOL4 inferScript.sml:475-476: a theorem that HOL4 states as the
   value of an ML expression: check_ctor_types_expand *)

let _ = size_thms "ast_t";;
let _ = size_thms "mlstring";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let check_ctors_def,check_ctors_ind = define_wf
  `MEASURE (\(x0,x1,x2).      list_size      (pair_size (list_size
  mlstring_size)      (pair_size mlstring_size      (list_size
  (pair_size mlstring_size ast_t_size1))))      x2)`
  [`check_ctors l tenvT [] = st_ex_return one`;
   `check_ctors l tenvT (CONS (tvs,tn,ctors) tds) =
        st_ex_ignore_bind
          (check_dups l
                     (\n. mlstring_concat [(implode
                       "Duplicate constructor "); n;
                              (implode
                                " in the definition of type "); tn])
                     (MAP FST ctors)) (st_ex_ignore_bind
          (check_dups l
                     (\n. mlstring_concat [(implode
                       "Duplicate type variable binding "); n;
                              (implode
                                " in the definition of type "); tn])
                     tvs) (st_ex_ignore_bind
          (check_ctor_types l tenvT tvs ctors) (
          check_ctors l tenvT tds)))`];;

(* HOL4 inferScript.sml:495-497: a theorem that HOL4 states as the
   value of an ML expression: check_ctors_expand *)

let check_type_definition_def = new_definition
  `check_type_definition l tenvT tds =
     st_ex_ignore_bind
       (check_dups l
                  (\n. mlstring_concat [(implode
                    "Duplicate type constructor "); n;
                              (implode

      " in a mutually recursive type definition")])
                  (MAP (FST o SND) tds)) (
       check_ctors l tenvT tds)`;;

(* HOL4 inferScript.sml:510-511: a theorem that HOL4 states as the
   value of an ML expression: check_type_definition_expand *)

let infer_p_def,infer_p_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`infer_p l ienv (ast_Pvar n:ast_pat) =
        st_ex_bind fresh_uvar (\t.
           st_ex_return (t,[(n,t)]))`;
   `infer_p l ienv (ast_Pany:ast_pat) =
        st_ex_bind fresh_uvar (\t.
           st_ex_return (t,[]))`;
   `infer_p l ienv (ast_Plit (ast_IntLit i):ast_pat) =
        st_ex_return (Infer_Tapp [] Tint_num,[])`;
   `infer_p l ienv (ast_Plit (ast_Char s):ast_pat) =
        st_ex_return (Infer_Tapp [] Tchar_num,[])`;
   `infer_p l ienv (ast_Plit (ast_StrLit s):ast_pat) =
        st_ex_return (Infer_Tapp [] Tstring_num,[])`;
   `infer_p l ienv (ast_Plit (ast_Word8 w):ast_pat) =
        st_ex_return (Infer_Tapp [] Tword8_num,[])`;
   `infer_p l ienv (ast_Plit (ast_Word64 w):ast_pat) =
        st_ex_return (Infer_Tapp [] Tword64_num,[])`;
   `infer_p l ienv (ast_Plit (ast_Float64 f):ast_pat) =
        infer_failwith l (implode
          "Floats cannot be used in patterns")`;
   `infer_p l ienv (ast_Pcon cn_opt ps:ast_pat) =
        (match cn_opt with NONE ->
              st_ex_bind (infer_ps l ienv ps) (\(ts,tenv).
                 st_ex_return (Infer_Tapp ts Ttup_num,tenv)) | SOME
                   cn ->
              st_ex_bind (lookup_st_ex l (implode "constructor") cn
                (inf_env_inf_c ienv)) (\(tvs',ts,tn). st_ex_bind
                (infer_ps l ienv ps) (\
                 (ts'',tenv). st_ex_bind (n_fresh_uvar (LENGTH
                   tvs')) (\
                 ts'. st_ex_ignore_bind
                 (infer_guard (LENGTH ts'' = LENGTH ts) l
                       (mlstring_concat [(implode "Constructor ");
                         id_to_string cn; (implode " given ");
                              toString (&(LENGTH ts'')); (implode
                                " arguments, but expected ");
                              toString (&(LENGTH ts))])) (st_ex_bind
                                (add_constraints l ts'' (MAP
                                (infer_type_subst (ZIP tvs' ts')) ts))
                                (\
                 one.
                 st_ex_return (Infer_Tapp ts' tn,tenv)))))))`;
   `infer_p l ienv (ast_Pref p:ast_pat) =
        st_ex_bind (infer_p l ienv p) (\(t,tenv).
          st_ex_return (Infer_Tapp [t] Tref_num,tenv))`;
   `infer_p l ienv (ast_Pas p v:ast_pat) =
        st_ex_bind (infer_p l ienv p) (\(t,tenv).
          st_ex_return (t,APPEND tenv [(v,t)]))`;
   `infer_p l ienv (ast_Ptannot p t) =
       st_ex_bind (infer_p l ienv p) (\(t',tenv). st_ex_bind
         (type_name_check_subst l
                  (\tv. mlstring_concat [(implode "Type variable ");
                    tv; (implode " found in type annotation. ");
                              (implode (APPEND

      "Type variables are not supported in type annotatio" "ns."))])
      (inf_env_inf_t
                  ienv) [] t) (\
          t''. st_ex_bind (add_constraint l t' (infer_type_subst []
            t'')) (\
          one.
          st_ex_return (t',tenv))))`;
   `infer_ps l ienv [] =
        st_ex_return ([],[])`;
   `infer_ps l ienv (CONS p ps) =
        st_ex_bind (infer_p l ienv p) (\(t,tenv). st_ex_bind
          (infer_ps l ienv ps) (\
           (ts,tenv').
           st_ex_return (CONS t ts,APPEND tenv' tenv)))`];;

let option_case_rand = prove
 (`(match x with NONE -> y | SOME a -> f a) s =
   (match x with NONE -> y s | SOME a -> f a s)`,
  CHEAT_TAC);;

(* HOL4 inferScript.sml:584-589: a theorem that HOL4 states as the
   value of an ML expression: infer_p_expand *)

let word_tc_def = define_cases
  [`word_tc ast_W8 = Tword8_num`;
   `word_tc (ast_W64:word_size) = Tword64_num`];;

let op_to_string_def = new_definition
  `op_to_string x1 =
        match x1 with
          (ast_Shift _6 _7 _8:ast_op) -> ((implode "Shift"),1)
        | ast_Equality -> ((implode "Equality"),2)
        | (ast_Arith a ty) ->
        ((implode "Arith"),
         (match supported_arith a ty with SOME n -> (n:num) | NONE ->
           0))
        | (ast_FromTo _9 _10) -> ((implode "FromTo"),1)
        | (ast_Test _11 _12) -> ((implode "Test"),2)
        | ast_Opapp -> ((implode "Opapp"),2)
        | ast_Opassign -> ((implode "Opassign"),2)
        | ast_Opref -> ((implode "Opref"),1)
        | ast_Opderef -> ((implode "Opderef"),1)
        | ast_Aw8alloc -> ((implode "Aw8alloc"),2)
        | ast_Aw8sub -> ((implode "Aw8sub"),2)
        | ast_Aw8length -> ((implode "Aw8length"),1)
        | ast_Aw8update -> ((implode "Aw8update"),3)
        | ast_Aw8sub_unsafe -> ((implode "Aw8sub_unsafe"),2)
        | ast_Aw8update_unsafe -> ((implode "Aw8update_unsafe"),3)
        | ast_XorAw8Str_unsafe -> ((implode "XorAw8Str_unsafe"),2)
        | ast_CopyStrStr -> ((implode "CopyStrStr"),3)
        | ast_CopyStrAw8 -> ((implode "CopyStrAw8"),5)
        | ast_CopyAw8Str -> ((implode "CopyAw8Str"),3)
        | ast_CopyAw8Aw8 -> ((implode "CopyAw8Aw8"),5)
        | ast_Strsub -> ((implode "Strsub"),2)
        | ast_Implode -> ((implode "Implode"),1)
        | ast_Explode -> ((implode "Explode"),1)
        | ast_Strlen -> ((implode "Strlen"),1)
        | ast_Strcat -> ((implode "Strcat"),1)
        | ast_VfromList -> ((implode "VfromList"),1)
        | ast_Vsub -> ((implode "Vsub"),2)
        | ast_Vsub_unsafe -> ((implode "Vsub_unsafe"),2)
        | ast_Vlength -> ((implode "Vlength"),1)
        | ast_Aalloc -> ((implode "Aalloc"),2)
        | ast_AallocEmpty -> ((implode "AallocEmpty"),1)
        | ast_AallocFixed -> ((implode "AallocFixed"),1)
        | ast_Asub -> ((implode "Asub"),2)
        | ast_Alength -> ((implode "Alength"),1)
        | ast_Aupdate -> ((implode "Aupdate"),3)
        | ast_Asub_unsafe -> ((implode "Asub_unsafe"),2)
        | ast_Aupdate_unsafe -> ((implode "Aupdate_unsafe"),3)
        | ast_ConfigGC -> ((implode "ConfigGC"),2)
        | ast_Eval -> ((implode "Eval"),6)
        | ast_Env_id -> ((implode "Env_id"),1)
        | ast_ListAppend -> ((implode "ListAppend"),2)
        | (ast_FFI _13) -> ((implode "FFI"),2)
        | (ast_ThunkOp ForceThunk) -> ((implode "ForceThunk"),1)
        | (ast_ThunkOp (AllocThunk _14)) -> ((implode
          "AllocThunk"),1)
        | (ast_ThunkOp (UpdateThunk _15)) -> ((implode
          "UpdateThunk"),2)`;;

(* HOL4 inferScript.sml:646: the overload Tem, which the port expands *)

let t_num_of_def = new_definition
  `t_num_of x1 =
      match x1 with
        ast_BoolT -> Tbool_num
      | ast_IntT -> Tint_num
      | ast_CharT -> Tchar_num
      | ast_StrT -> Tstring_num
      | (ast_WordT ast_W8) -> Tword8_num
      | (ast_WordT ast_W64) -> Tword64_num
      | ast_Float64T -> Tdouble_num`;;

let op_simple_constraints_def = new_definition
  `op_simple_constraints op =
     (match op with ast_Arith a ty -> (match supported_arith a ty
       with NONE -> (F,[],(Infer_Tapp []) Tbool_num) | SOME arity ->
                          (T,REPLICATE arity ((Infer_Tapp [])
                            (t_num_of ty)),(Infer_Tapp []) (t_num_of
                            ty))) | ast_FromTo ty1 ty2 ->
                            (supported_conversion ty1 ty2,
                           [(Infer_Tapp []) (t_num_of ty1)],
                           (Infer_Tapp []) (t_num_of ty2)) | ast_Test
                             test ty -> (supported_test test ty,
                         [(Infer_Tapp []) (t_num_of ty); (Infer_Tapp
                           []) (t_num_of ty)],
                         (Infer_Tapp []) Tbool_num) | ast_Shift wz
                           _16 _17 -> (T,[(Infer_Tapp []) (word_tc
                           wz)],(Infer_Tapp []) (word_tc wz)) |
                           ast_Aw8alloc -> (T,[(Infer_Tapp []) Tint_num;
                           (Infer_Tapp []) Tword8_num],(Infer_Tapp [])
                           Tword8array_num) | ast_Aw8sub ->
                           (T,[(Infer_Tapp []) Tword8array_num;
                           (Infer_Tapp []) Tint_num],(Infer_Tapp [])
                           Tword8_num) | ast_Aw8length ->
                           (T,[(Infer_Tapp [])
                           Tword8array_num],(Infer_Tapp []) Tint_num) |
                           ast_Aw8update -> (T,[(Infer_Tapp [])
                           Tword8array_num; (Infer_Tapp []) Tint_num;
                           (Infer_Tapp []) Tword8_num],
           (Infer_Tapp []) Ttup_num) | ast_CopyStrStr ->
             (T,[(Infer_Tapp []) Tstring_num; (Infer_Tapp []) Tint_num;
             (Infer_Tapp []) Tint_num],
           (Infer_Tapp []) Tstring_num) | ast_CopyStrAw8 ->
             (T,[(Infer_Tapp []) Tstring_num; (Infer_Tapp []) Tint_num;
             (Infer_Tapp []) Tint_num;
               (Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
                 Tint_num],(Infer_Tapp []) Ttup_num) | ast_CopyAw8Str ->
                 (T,[(Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
                 Tint_num; (Infer_Tapp []) Tint_num],
           (Infer_Tapp []) Tstring_num) | ast_CopyAw8Aw8 ->
             (T,[(Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
             Tint_num; (Infer_Tapp []) Tint_num;
               (Infer_Tapp []) Tword8array_num; (Infer_Tapp [])
                 Tint_num],(Infer_Tapp []) Ttup_num) | ast_Strsub ->
                 (T,[(Infer_Tapp []) Tstring_num; (Infer_Tapp [])
                 Tint_num],(Infer_Tapp []) Tchar_num) | ast_Strlen ->
                 (T,[(Infer_Tapp []) Tstring_num],(Infer_Tapp [])
                 Tint_num) | ast_ConfigGC -> (T,[(Infer_Tapp [])
                 Tint_num; (Infer_Tapp []) Tint_num],(Infer_Tapp [])
                 Ttup_num) | ast_FFI _18 -> (T,[(Infer_Tapp [])
                 Tstring_num; (Infer_Tapp [])
                 Tword8array_num],(Infer_Tapp []) Ttup_num) |
                 ast_Implode -> (T,[Infer_Tapp [Infer_Tapp [] Tchar_num]
                 Tlist_num],
           (Infer_Tapp []) Tstring_num) | ast_Explode ->
             (T,[(Infer_Tapp []) Tstring_num],Infer_Tapp [(Infer_Tapp
             []) Tchar_num] Tlist_num) | ast_Strcat -> (T,[Infer_Tapp
             [(Infer_Tapp []) Tstring_num] Tlist_num],(Infer_Tapp [])
             Tstring_num) | _19 -> (F,[],(Infer_Tapp []) Tbool_num))`;;

let op_n_args_msg_def = new_definition
  `op_n_args_msg op n =
     (let (ops,args) = op_to_string op in
     mlstring_concat [(implode "Primitive "); ops; (implode
       " given ");
         toString (&n); (implode " arguments, but expects ");
         toString (&args)])`;;

let constrain_op_def = new_definition
  `constrain_op l op ts s =
     (let (simple,op_arg_ts,op_ret_t) = op_simple_constraints op in
     if simple then
       if ~(LENGTH ts = LENGTH op_arg_ts) then infer_failwith l
         (op_n_args_msg op (LENGTH ts)) s else st_ex_bind
         (add_constraints l ts (MAP I op_arg_ts)) (\one.
         st_ex_return op_ret_t) s else match (op,ts) with
           (ast_Equality,[t1; t2]) ->
          st_ex_bind (add_constraint l t1 t2) (\one.
             st_ex_return (Infer_Tapp [] Tbool_num)) s |
               (ast_Opapp,[t1; t2]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t1 (Infer_Tapp [t2; uvar] Tfn_num)) (\
             one.
             st_ex_return uvar)) s | (ast_Opassign,[t1; t2]) ->
          st_ex_bind (add_constraint l t1 (Infer_Tapp [t2] Tref_num))
            (\one.
             st_ex_return (Infer_Tapp [] Ttup_num)) s |
               (ast_Opref,[t]) -> st_ex_return (Infer_Tapp [t] Tref_num)
               s | (ast_Opderef,[t]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t (Infer_Tapp [uvar] Tref_num)) (\
             one.
             st_ex_return uvar)) s | (ast_VfromList,[t]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t (Infer_Tapp [uvar] Tlist_num)) (\
             one.
             st_ex_return (Infer_Tapp [uvar] Tvector_num))) s |
               (ast_Vsub,[t1; t2]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t1 (Infer_Tapp [uvar] Tvector_num)) (\
             one. st_ex_bind (add_constraint l t2 (Infer_Tapp []
               Tint_num)) (\
             one.
             st_ex_return uvar))) s | (ast_Vlength,[t]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t (Infer_Tapp [uvar] Tvector_num)) (\
             one.
             st_ex_return (Infer_Tapp [] Tint_num))) s |
               (ast_Aalloc,[t1; t2]) ->
          st_ex_bind (add_constraint l t1 (Infer_Tapp [] Tint_num))
            (\one.
             st_ex_return (Infer_Tapp [t2] Tarray_num)) s |
               (ast_AallocEmpty,[t1]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t1 (Infer_Tapp [] Ttup_num)) (\
             one.
             st_ex_return (Infer_Tapp [uvar] Tarray_num))) s |
               (ast_Asub,[t1; t2]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t1 (Infer_Tapp [uvar] Tarray_num)) (\
             one. st_ex_bind (add_constraint l t2 (Infer_Tapp []
               Tint_num)) (\
             one.
             st_ex_return uvar))) s | (ast_Alength,[t]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t (Infer_Tapp [uvar] Tarray_num)) (\
             one.
             st_ex_return (Infer_Tapp [] Tint_num))) s |
               (ast_Aupdate,[t1; t2; t3]) ->
          st_ex_bind (add_constraint l t1 (Infer_Tapp [t3]
            Tarray_num)) (\one. st_ex_bind (add_constraint l t2
            (Infer_Tapp [] Tint_num)) (\
             one.
             st_ex_return (Infer_Tapp [] Ttup_num))) s |
               (ast_ListAppend,[t1; t2]) ->
          st_ex_bind fresh_uvar (\uvar. st_ex_bind (add_constraint l
            t1 (Infer_Tapp [uvar] Tlist_num)) (\
             one. st_ex_bind (add_constraint l t2 (Infer_Tapp [uvar]
               Tlist_num)) (\
             one.
             st_ex_return (Infer_Tapp [uvar] Tlist_num)))) s |
               (ast_Vsub_unsafe,_20) -> infer_failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (ast_Asub_unsafe,_21) -> infer_failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (ast_Aupdate_unsafe,_22) -> infer_failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (ast_Aw8sub_unsafe,_23) -> infer_failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (ast_Aw8update_unsafe,_24) -> infer_failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (ast_XorAw8Str_unsafe,_25) -> infer_failwith l ((implode
               "Unsafe ops do not have a type")) s |
               (ast_AallocFixed,_26) -> infer_failwith l ((implode
               "Unsafe ops do not have a type")) s | (
         // not actually unsafe
         ast_Eval,_27) -> infer_failwith l ((implode
           "Unsafe ops do not have a type")) s | (ast_Env_id,_28) ->
           infer_failwith l ((implode
           "Unsafe ops do not have a type")) s | (ast_ThunkOp
           _29,_30) -> infer_failwith l ((implode
           "Thunk ops do not have a type")) s | (ast_Arith _31
           _32,_33) -> infer_failwith l ((implode "Type mismatch")) s
           | (ast_FromTo _34 _35,_36) -> infer_failwith l ((implode
           "Type mismatch")) s | (ast_Test _37 _38,_39) ->
           infer_failwith l ((implode "Type mismatch")) s | _40 ->
           infer_failwith l (op_n_args_msg op (LENGTH ts)) s)`;;

(* HOL4 inferScript.sml:796-797: a theorem that HOL4 states as the
   value of an ML expression: constrain_op_case_def *)

(* HOL4 inferScript.sml:799-800: a theorem that HOL4 states as the
   value of an ML expression: constrain_op_expand *)

let st_ex_bind_failure = prove
 (`st_ex_bind f g s = (M_failure r,s') <=>
   (f s = (M_failure r,s') \/
     (?x st. f s = (M_success x,st) /\ g x st = (M_failure r,s')))`,
  CHEAT_TAC);;

let constrain_op_error_msg_sanity = prove
 (`!l op args s l' s' msg.
     LENGTH args = SND (op_to_string op) /\
     constrain_op l op args s = (M_failure (l',msg),s') ==>
     IS_PREFIX (explode msg) "Type mismatch" \/
     IS_PREFIX (explode msg) "Unsafe" \/
     IS_PREFIX (explode msg) "Thunk"`,
  CHEAT_TAC);;

let infer_e_def,infer_e_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`infer_e l ienv (ast_Raise e:ast_exp) =
        st_ex_bind (infer_e l ienv e) (\t2. st_ex_bind
          (add_constraint l t2 (Infer_Tapp [] Texn_num)) (\
           one. st_ex_bind fresh_uvar (\
           t1.
           st_ex_return t1)))`;
   `infer_e l ienv (ast_Handle e pes:ast_exp) =
        (if pes = [] then
          infer_failwith l ((implode "No patterns in handle")) else
          st_ex_bind (infer_e l ienv e) (\t1. st_ex_bind (infer_pes
            l ienv pes (Infer_Tapp [] Texn_num) t1) (\
             one.
             st_ex_return t1)))`;
   `infer_e l ienv (ast_Lit (ast_IntLit i):ast_exp) =
        st_ex_return (Infer_Tapp [] Tint_num)`;
   `infer_e l ienv (ast_Lit (ast_Char c):ast_exp) =
        st_ex_return (Infer_Tapp [] Tchar_num)`;
   `infer_e l ienv (ast_Lit (ast_StrLit s):ast_exp) =
        st_ex_return (Infer_Tapp [] Tstring_num)`;
   `infer_e l ienv (ast_Lit (ast_Word8 w):ast_exp) =
        st_ex_return (Infer_Tapp [] Tword8_num)`;
   `infer_e l ienv (ast_Lit (ast_Word64 _42):ast_exp) =
        st_ex_return (Infer_Tapp [] Tword64_num)`;
   `infer_e l ienv (ast_Lit (ast_Float64 _44):ast_exp) =
        st_ex_return (Infer_Tapp [] Tdouble_num)`;
   `infer_e l ienv (Var id':ast_exp) =
        st_ex_bind (lookup_st_ex l (implode "variable") id'
          (inf_env_inf_v ienv)) (\(tvs,t). st_ex_bind (n_fresh_uvar tvs)
          (\
           uvs.
           st_ex_return (infer_deBruijn_subst uvs t)))`;
   `infer_e l ienv (ast_Con cn_opt es:ast_exp) =
        (match cn_opt with
            NONE ->
             st_ex_bind (infer_es l ienv es) (\ts.
                st_ex_return (Infer_Tapp ts Ttup_num)) | SOME cn ->
             st_ex_bind (lookup_st_ex l (implode "constructor") cn
               (inf_env_inf_c ienv)) (\(tvs',ts,tn). st_ex_bind
               (infer_es l ienv es) (\
                ts''. st_ex_bind (n_fresh_uvar (LENGTH tvs')) (\
                ts'. st_ex_ignore_bind
                 (infer_guard (LENGTH ts'' = LENGTH ts) l
                       (mlstring_concat [(implode "Constructor ");
                         id_to_string cn; (implode " given ");
                              toString (&(LENGTH ts'')); (implode
                                " arguments, but expected ");
                              toString (&(LENGTH ts))])) (st_ex_bind
                                (add_constraints l ts'' (MAP
                                (infer_type_subst (ZIP tvs' ts')) ts))
                                (\
                one.
                st_ex_return (Infer_Tapp ts' tn)))))))`;
   `infer_e l ienv (ast_Fun x e:ast_exp) =
        st_ex_bind fresh_uvar (\t1. st_ex_bind (infer_e l
          (inf_env_inf_v_fupd (K (nsBind x (0,t1) (inf_env_inf_v ienv)))
          ienv) e) (\
           t2.
           st_ex_return (Infer_Tapp [t1; t2] Tfn_num)))`;
   `infer_e l ienv (ast_App op es:ast_exp) =
        st_ex_bind (infer_es l ienv es) (\ts. st_ex_bind
          (constrain_op l op ts) (\
           t.
           st_ex_return t))`;
   `infer_e l ienv (ast_Log log e1 e2) =
        st_ex_bind (infer_e l ienv e1) (\t1. st_ex_bind (infer_e l
          ienv e2) (\
           t2. st_ex_bind (add_constraint l t1 (Infer_Tapp []
             Tbool_num)) (\
           one. st_ex_bind (add_constraint l t2 (Infer_Tapp []
             Tbool_num)) (\
           one.
           st_ex_return (Infer_Tapp [] Tbool_num)))))`;
   `infer_e l ienv (ast_If e1 e2 e3:ast_exp) =
        st_ex_bind (infer_e l ienv e1) (\t1. st_ex_bind
          (add_constraint l t1 (Infer_Tapp [] Tbool_num)) (\
           one. st_ex_bind (infer_e l ienv e2) (\
           t2. st_ex_bind (infer_e l ienv e3) (\
           t3. st_ex_bind (add_constraint l t2 t3) (\
           one.
           st_ex_return t2)))))`;
   `infer_e l ienv (ast_Mat e pes:ast_exp) =
        (if pes = [] then
          infer_failwith l ((implode "No patterns in case")) else
          st_ex_bind (infer_e l ienv e) (\t1. st_ex_bind fresh_uvar
            (\
             t2. st_ex_bind (infer_pes l ienv pes t1 t2) (\
             one.
             st_ex_return t2))))`;
   `infer_e l ienv (ast_Let x e1 e2:ast_exp) =
          // Don't do polymorphism for non-top-level lets
          // if is_value e1 then
          // do n <- get_next_uvar;
          // t1 <- infer_e l ienv e1;
          // t1' <- apply_subst t1;
          // (num_gen,s,t1'') <- return (generalise n 0 FEMPTY t1');
          // t2 <- infer_e l (ienv with inf_v:=(bind x (num_gen,t1'') ienv.inf_v)) e2;
          // return t2
          // od
          // else
          st_ex_bind (infer_e l ienv e1) (\t1. st_ex_bind (infer_e l
            (inf_env_inf_v_fupd (K (nsOptBind x (0,t1) (inf_env_inf_v
            ienv))) ienv) e2) (\
             t2.
             st_ex_return t2))`;
   `// Don't do polymorphism for non-top-level let recs
    // (infer_e l ienv (Letrec funs e) =
    // do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name variable";
    // next <- get_next_uvar;
    // uvars <- n_fresh_uvar (LENGTH funs);
    // env' <- return (merge (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars) env);
    // funs_ts <- infer_funs l (ienv with inf_v := env') funs;
    // () <- add_constraints l uvars funs_ts;
    // ts <- apply_subst_list uvars;
    // (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
    // env'' <- return (merge (list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts') env);
    // t <- infer_e l (ienv with inf_v := env'') e;
    // return t
    // od) ∧
    infer_e l ienv (ast_Letrec funs e:ast_exp) =
     st_ex_ignore_bind
       (check_dups l (\n. mlstring_concat [(implode
         "Duplicate function name "); n;
                              (implode

      " in mutually recursive function definition")])
                    (MAP FST funs)) (st_ex_bind (n_fresh_uvar
                      (LENGTH funs)) (\
        uvars. st_ex_bind (st_ex_return (nsAppend (alist_to_ns (MAP2
          (\(f,x,e) uvar. (f,(0,uvar))) funs uvars)) (inf_env_inf_v
          ienv))) (\
        env'. st_ex_bind (infer_funs l (inf_env_inf_v_fupd (K env')
          ienv) funs) (\
        funs_ts. st_ex_bind (add_constraints l uvars funs_ts) (\
        one. st_ex_bind (infer_e l (inf_env_inf_v_fupd (K env')
          ienv) e) (\
        t.
        st_ex_return t))))))`;
   `infer_e l ienv (ast_Tannot e t) =
        st_ex_bind (infer_e l ienv e) (\t'. st_ex_bind
          (type_name_check_subst l
                  (\tv. mlstring_concat [(implode "Type variable ");
                    tv; (implode " found in type annotation. ");
                              (implode (APPEND

      "Type variables are not supported in type annotatio" "ns."))])
      (inf_env_inf_t
                  ienv) [] t) (\
           t''. st_ex_bind (add_constraint l t' (infer_type_subst []
             t'')) (\
           one.
           st_ex_return t')))`;
   `infer_e l ienv (ast_Lannot e new_l) =
        infer_e (loc_err_info_loc_fupd (K (SOME new_l)) l) ienv e`;
   `infer_es l ienv [] =
        st_ex_return []`;
   `infer_es l ienv (CONS e es) =
        st_ex_bind (infer_e l ienv e) (\t. st_ex_bind (infer_es l
          ienv es) (\
           ts.
           st_ex_return (CONS t ts)))`;
   `infer_pes l ienv [] t1 t2 =
         st_ex_return one`;
   `infer_pes l ienv (CONS (p,e) pes) t1 t2 =
        st_ex_bind (infer_p l ienv p) (\(t1',env').
          st_ex_ignore_bind
          (check_dups l (\n. mlstring_concat [(implode
            "Duplicate variable "); n; (implode " in pattern")])
                    (MAP FST env')) (st_ex_bind (add_constraint l t1
                      t1') (\
           one. st_ex_bind (infer_e l (inf_env_inf_v_fupd (K
             (nsAppend (alist_to_ns (MAP (\(n,t). (n,(0,t))) env'))
             (inf_env_inf_v ienv))) ienv) e) (\
           t2'. st_ex_bind (add_constraint l t2 t2') (\
           one. st_ex_bind (infer_pes l ienv pes t1 t2) (\
           one.
           st_ex_return one))))))`;
   `infer_funs l ienv [] = st_ex_return []`;
   `infer_funs l ienv (CONS (f,x,e) funs) =
        st_ex_bind fresh_uvar (\uvar. st_ex_bind (infer_e l
          (inf_env_inf_v_fupd (K (nsBind x (0,uvar) (inf_env_inf_v
          ienv))) ienv) e) (\
           t. st_ex_bind (infer_funs l ienv funs) (\
           ts.
           st_ex_return (CONS (Infer_Tapp [uvar; t] Tfn_num)
             ts))))`];;

(* [local] *)
let FUN_EQ_THM_state = prove
 (`f = g <=> (!s. f s = g s)`,
  CHEAT_TAC);;

(* HOL4 inferScript.sml:1033-1038: a theorem that HOL4 states as the
   value of an ML expression: infer_e_expand *)

let extend_dec_ienv_def = new_definition
  `extend_dec_ienv ienv' ienv =
      mk_inf_env (nsAppend (inf_env_inf_v ienv') (inf_env_inf_v
        ienv)) (nsAppend (inf_env_inf_c ienv') (inf_env_inf_c ienv))
        (nsAppend (inf_env_inf_t ienv') (inf_env_inf_t ienv))`;;

let lift_ienv_def = new_definition
  `lift_ienv mn ienv =
     mk_inf_env (nsLift mn (inf_env_inf_v ienv)) (nsLift mn
       (inf_env_inf_c ienv)) (nsLift mn (inf_env_inf_t ienv))`;;

let infer_d_def,infer_d_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`infer_d ienv (Dlet locs p e) =
      st_ex_bind init_state (\one. st_ex_bind get_next_uvar (\
         n. st_ex_bind (infer_e (mk_loc_err_info (SOME locs)
           (inf_env_inf_t ienv)) ienv e) (\
         t1. st_ex_bind (infer_p (mk_loc_err_info (SOME locs)
           (inf_env_inf_t ienv)) ienv p) (\
         (t2,env'). st_ex_ignore_bind
         (check_dups (mk_loc_err_info (SOME locs) (inf_env_inf_t
           ienv))
                       (\n. mlstring_concat [(implode
                         "Duplicate variable "); n;
                              (implode

      " in the left-hand side of a definition")])
                    (MAP FST env')) (st_ex_bind (add_constraint
                      (mk_loc_err_info (SOME locs) (inf_env_inf_t ienv))
                      t1 t2) (\
         one. st_ex_bind (apply_subst_list (MAP SND env')) (\
         ts. st_ex_bind (st_ex_return (generalise_list n 0 FEMPTY
           ts)) (\
         (num_tvs',s,ts'). st_ex_bind (infer_guard (num_tvs' = 0 \/
           is_value e) (mk_loc_err_info (SOME locs) (inf_env_inf_t
           ienv))
                     ((implode "Value restriction violated"))) (\
         one.
         st_ex_return (mk_inf_env (alist_to_ns (ZIP (MAP FST
           env') (MAP (\t. (num_tvs',t)) ts'))) nsEmpty
           nsEmpty))))))))))`;
   `infer_d ienv (Dletrec locs funs) =
      st_ex_ignore_bind
        (check_dups (mk_loc_err_info (SOME locs) (inf_env_inf_t
          ienv))
           (\n. mlstring_concat [(implode
             "Duplicate function name "); n;
                (implode
                  " a mutually recursive function definition")])
                   (MAP FST funs)) (st_ex_bind init_state (\
         one. st_ex_bind get_next_uvar (\
         next'. st_ex_bind (n_fresh_uvar (LENGTH funs)) (\
         uvars. st_ex_bind (st_ex_return (nsAppend (alist_to_ns
           (MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars))
           (inf_env_inf_v ienv))) (\
         env'. st_ex_bind (infer_funs (mk_loc_err_info (SOME locs)
           (inf_env_inf_t ienv))
                              (inf_env_inf_v_fupd (K env') ienv)
                                funs) (\
         funs_ts. st_ex_bind (add_constraints (mk_loc_err_info (SOME
           locs) (inf_env_inf_t ienv)) uvars funs_ts) (\
         one. st_ex_bind (apply_subst_list uvars) (\
         ts. st_ex_bind (st_ex_return (generalise_list next' 0
           FEMPTY ts)) (\
         (num_gen,s,ts').
         st_ex_return (mk_inf_env (alist_to_ns (MAP2 (\(f,x,e) t.
           (f,(num_gen,t))) funs ts')) nsEmpty nsEmpty))))))))))`;
   `infer_d ienv (Dtype locs tdefs) =
      st_ex_bind (n_fresh_id (LENGTH tdefs)) (\
         tids. st_ex_bind (st_ex_return (alist_to_ns (MAP2
           (\(tvs,tn,ctors) i. (tn,(tvs,Tapp (MAP Tvar tvs) i))) tdefs
           tids))) (\
         ienvT1. st_ex_bind (st_ex_return (nsAppend ienvT1
           (inf_env_inf_t ienv))) (\
         ienvT2. st_ex_ignore_bind
         (check_type_definition (mk_loc_err_info (SOME locs)
           (inf_env_inf_t ienv)) ienvT2 tdefs) (
         st_ex_return (mk_inf_env nsEmpty (build_ctor_tenv ienvT2
           tdefs tids) ienvT1)))))`;
   `infer_d ienv (Dtabbrev locs tvs tn t) =
      st_ex_ignore_bind
        (check_dups (mk_loc_err_info (SOME locs) (inf_env_inf_t
          ienv))
           (\n. mlstring_concat [(implode
             "Duplicate type variable bindings for ");
                        n; (implode " in type abbreviation ");
                        tn])
                  tvs) (st_ex_bind (type_name_check_subst
                    (mk_loc_err_info (SOME locs) (inf_env_inf_t ienv))
                (\tv. mlstring_concat [(implode
                  "Unbound type variable "); tv; (implode
                  " in type abbreviation "); tn]) (inf_env_inf_t
                ienv) tvs t) (\
         t'.
         st_ex_return (mk_inf_env nsEmpty nsEmpty (nsSing tn
           (tvs,t')))))`;
   `infer_d ienv (Dexn locs cn ts) =
      st_ex_bind (type_name_check_subst_list (mk_loc_err_info (SOME
        locs) (inf_env_inf_t ienv))
                (\tv. mlstring_concat [(implode "Type variable ");
                  tv; (implode " found in declaration of exception ");
                  cn;
                              (implode (APPEND

      ". Type variables are not allowed in exception decl"
      "arations."))]) (inf_env_inf_t
                ienv) [] ts) (\
        ts'.
        st_ex_return (mk_inf_env nsEmpty (nsSing cn
          ([],ts',Texn_num)) nsEmpty))`;
   `infer_d ienv (Denv n) =
      infer_failwith (mk_loc_err_info NONE (inf_env_inf_t ienv))
        ((implode "Env declaration (Denv) is not supported."))`;
   `infer_d ienv (Dmod mn ds) =
      st_ex_bind (infer_ds ienv ds) (\ienv'.
         st_ex_return (lift_ienv mn ienv'))`;
   `infer_d ienv (Dlocal lds ds) =
      st_ex_bind (infer_ds ienv lds) (\ienv'.
        infer_ds (extend_dec_ienv ienv' ienv) ds)`;
   `infer_ds ienv [] =
      st_ex_return (mk_inf_env nsEmpty nsEmpty nsEmpty)`;
   `infer_ds ienv (CONS d ds) =
      st_ex_bind (infer_d ienv d) (\
        ienv'. st_ex_bind (infer_ds (extend_dec_ienv ienv' ienv) ds)
          (\
        ienv''.
        st_ex_return (extend_dec_ienv ienv'' ienv')))`];;

(* HOL4 inferScript.sml:1147-1152: a theorem that HOL4 states as the
   value of an ML expression: infer_d_expand *)

(* The starting Id should be greater than Tlist_num :: (Tbool_num :: prim_type_nums) *)
let start_type_id_def = new_definition
  `start_type_id =
     ITLIST MAX (CONS Tlist_num (CONS Tbool_num prim_type_nums)) 0 +
       1`;;

let infertype_prog_def = new_definition
  `infertype_prog ienv prog =
     (match FST (infer_ds ienv prog (init_infer_state (mk_infer_st
       0 FEMPTY start_type_id))) with M_success new_ienv -> M_success
       (extend_dec_ienv new_ienv ienv) | M_failure x -> M_failure x)`;;

let infertype_prog_inc_def = new_definition
  `infertype_prog_inc (ienv,next_id) prog =
   (match infer_ds ienv prog (init_infer_state (mk_infer_st ARB ARB
     next_id)) with
     (M_success new_ienv,st) ->
     (M_success (extend_dec_ienv new_ienv ienv,infer_st_next_id
       st)) | (M_failure x,_55) -> M_failure x)`;;

let infer_init_config_def = new_definition
  `(infer_init_config:inf_env) =
     mk_inf_env nsEmpty (type_env_c prim_tenv) (type_env_t
       prim_tenv)`;;
hol4_overload "init_config" "infer_init_config";;

(* The following aren't needed to run the inferencer, but are useful in the proofs
 * about it *)

let infer_deBruijn_inc_def,infer_deBruijn_inc_ind = define_shaped_rec
  "nested"
  [`infer_deBruijn_inc n (Infer_Tvar_db m) =
        Infer_Tvar_db (m + n)`;
   `infer_deBruijn_inc n (Infer_Tapp ts tn) =
        Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn`;
   `infer_deBruijn_inc n (Infer_Tuvar m) =
        Infer_Tuvar m`];;

let infer_subst_def,infer_subst_ind = define_shaped_rec
  "nested"
  [`infer_subst s (Infer_Tvar_db n) = Infer_Tvar_db n`;
   `infer_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (infer_subst
  s) ts) tc`;
   `infer_subst s (Infer_Tuvar n) =
        (match FLOOKUP s n with
            NONE -> Infer_Tuvar n | SOME m -> Infer_Tvar_db m)`];;

let pure_add_constraints_def,pure_add_constraints_ind = define_rec
  [`pure_add_constraints s [] s' = (s = s')`;
   `pure_add_constraints s1 (CONS (t1,t2) rest) s' =
      (?s2. (t_unify s1 t1 t2 = SOME s2) /\
           pure_add_constraints s2 rest s')`];;

let check_t_def,check_t_ind = define_shaped_rec
  "nested"
  [`check_t n uvars (Infer_Tuvar v) = (v IN uvars)`;
   `check_t n uvars (Infer_Tvar_db n') =
        (n' < n)`;
   `check_t n uvars (Infer_Tapp ts tc) = ALL (check_t n uvars) ts`];;

let ienv_val_ok_def = new_definition
  `ienv_val_ok uvars env =
     nsAll (\x (tvs,t). check_t tvs uvars t) env`;;

let check_s_def = new_definition
  `check_s tvs uvs s =
     (!uv. uv IN FDOM s ==> check_t tvs uvs (FAPPLY s uv))`;;

(* Adding the constraints extra_constraints moves the constraint set from s1 to
 * s2, and s2 is required to be complete in that it assigns to (at least) all
 * the uvars ≤ next_uvar, and when we apply it to any uvar, we get back a type
 * without any uvars in it. *)
let sub_completion_def = new_definition
  `sub_completion tvs next_uvar s1 extra_constraints s2 =
     (pure_add_constraints s1 extra_constraints s2 /\
      (count next_uvar SUBSET FDOM s2) /\
      (!uv. uv IN FDOM s2 ==> check_t tvs {} (t_walkstar s2
        (Infer_Tuvar uv))))`;;

(* printing of types *)

(* the termination relation that HOL4 gives is
     MEASURE LENGTH
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 inferScript.sml:1243-1245: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let alist_nub_def,alist_nub_ind = define_guess_cheat
  [`alist_nub [] = []`;
   `alist_nub (CONS (x,y) xs) = CONS (x,y) (alist_nub (FILTER (\t.
  ~(x = FST t)) xs))`];;

let ns_nub_def,ns_nub_ind = define_mutual_shaped_rec
  "maplist>nested"
  [`ns_nub (Bind xs ys) = Bind (alist_nub xs) (alist_nub
  (inner_ns_nubs ys))`;
   `inner_ns_nubs [] = []`;
   `inner_ns_nubs (CONS (x,y) tl) = CONS (x,ns_nub y)
  (inner_ns_nubs tl)`];;

(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let ns_to_alist_def,ns_to_alist_ind = define_guess_cheat
  [`ns_to_alist (Bind [] []) = []`;
   `ns_to_alist (Bind [] (CONS (n,x) ms)) = APPEND (MAP (\(x,y). ((\x y.
  strcat x y) ((\x y. strcat x y) n (implode ".")) x,y)) (ns_to_alist
  x))
        (ns_to_alist (Bind [] ms))`;
   `ns_to_alist (Bind (CONS (s,x) xs) m) = CONS (s,x) (ns_to_alist
  (Bind xs m))`];;

let inf_env_to_types_string_def = new_definition
  `inf_env_to_types_string s =
     (let l = ns_to_alist (ns_nub (inf_env_inf_v s)) in
     let xs = MAP (\(n,_56,t). mlstring_concat [n; (implode ": ");
                              inf_type_to_string (inf_env_inf_t s) t;
                              (implode "\n")]) l in
        // sort mlstring_le
        REVERSE xs)`;;

hol4_only "++" "APPEND";;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["not"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
