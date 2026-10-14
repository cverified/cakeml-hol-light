(* ======================================================== *)
(*  typeSystem: ported from HOL4's
    semantics/typeSystemScript.sml  *)
(* ======================================================== *)

(*
  Specification of CakeML's type system.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/pattern_matching/pattern_exh.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/location.ml";;
needs "lib/ternaryComparisons.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;

new_type_abbrev("type_ident",`: num`);;

(* Types *)
let t_INDUCT,t_RECURSION = define_datatype
  "t = Tvar (mlstring) | Tvar_db (num) | Tapp (t list) (num)";;


(* Some abbreviations *)
let tarray_num_def = cake_define
  `(((Tarray_num:num):num) = ((0:num)))`;;

let tbool_num_def = cake_define
  `(((Tbool_num:num):num) = ((1:num)))`;;

let tchar_num_def = cake_define
  `(((Tchar_num:num):num) = ((2:num)))`;;

let texn_num_def = cake_define
  `(((Texn_num:num):num) = ((3:num)))`;;

let tfn_num_def = cake_define
  `(((Tfn_num:num):num) = ((4:num)))`;;

let tint_num_def = cake_define
  `(((Tint_num:num):num) = ((5:num)))`;;

let tlist_num_def = cake_define
  `(((Tlist_num:num):num) = ((6:num)))`;;

let tref_num_def = cake_define
  `(((Tref_num:num):num) = ((7:num)))`;;

let tstring_num_def = cake_define
  `(((Tstring_num:num):num) = ((8:num)))`;;

let ttup_num_def = cake_define
  `(((Ttup_num:num):num) = ((9:num)))`;;

let tvector_num_def = cake_define
  `(((Tvector_num:num):num) = ((10:num)))`;;

let tword64_num_def = cake_define
  `(((Tword64_num:num):num) = ((11:num)))`;;

let tword8_num_def = cake_define
  `(((Tword8_num:num):num) = ((12:num)))`;;

let tword8array_num_def = cake_define
  `(((Tword8array_num:num):num) = ((13:num)))`;;

let tdouble_num_def = cake_define
  `(((Tdouble_num:num):num) = ((14:num)))`;;

(* The numbers for the primitive types *)
let prim_type_nums_def = cake_define
  `(prim_type_nums:num list) =
   [Tarray_num; Tchar_num; Texn_num; Tfn_num; Tint_num; Tref_num;
     Tstring_num;
    Ttup_num; Tvector_num; Tword64_num; Tword8_num;
      Tword8array_num; Tdouble_num]`;;

let tarray_def = cake_define
  `((Tarray:t->t) t = (Tapp [t] Tarray_num))`;;

let tbool_def = cake_define
  `((Tbool:t) = (Tapp [] Tbool_num))`;;

let tchar_def = cake_define
  `((Tchar:t) = (Tapp [] Tchar_num))`;;

let texn_def = cake_define
  `((Texn:t) = (Tapp [] Texn_num))`;;

let tfn_def = cake_define
  `((Tfn:t->t->t) t1 t2 = (Tapp [t1; t2] Tfn_num))`;;

let tint_def = cake_define
  `((Tint:t) = (Tapp [] Tint_num))`;;

let tlist_def = cake_define
  `((Tlist:t->t) t = (Tapp [t] Tlist_num))`;;

let tref_def = cake_define
  `((Tref:t->t) t = (Tapp [t] Tref_num))`;;

let tstring_def = cake_define
  `((Tstring:t) = (Tapp [] Tstring_num))`;;

let ttup_def = cake_define
  `((Ttup:t list->t) ts = (Tapp ts Ttup_num))`;;

let tvector_def = cake_define
  `((Tvector:t->t) t = (Tapp [t] Tvector_num))`;;

let tword64_def = cake_define
  `((Tword64:t) = (Tapp [] Tword64_num))`;;

let tword8_def = cake_define
  `((Tword8:t) = (Tapp [] Tword8_num))`;;

let tword8array_def = cake_define
  `((Tword8array:t) = (Tapp [] Tword8array_num))`;;

let tdouble_def = cake_define
  `((Tdouble:t) = (Tapp [] Tdouble_num))`;;

(* Check that the free type variables are in the given list. Every
   deBruijn
 * variable must be smaller than the first argument. So if it is 0, no
   deBruijn
 * indices are permitted. *)
let check_freevars_def = cake_define
  `((check_freevars:num->mlstring list->t->bool) dbmax tvs (Tvar tv) =
      (MEM tv tvs)) /\
   ((check_freevars:num->mlstring list->t->bool) dbmax tvs (Tapp ts
     tn) =
      (EVERY (check_freevars dbmax tvs) ts)) /\
   ((check_freevars:num->mlstring list->t->bool) dbmax tvs
     (Tvar_db n) = (n < dbmax))`;;

let check_freevars_ast_def = cake_define
  `((check_freevars_ast:mlstring list->ast_t->bool) tvs (Atvar tv) =
      (MEM tv tvs)) /\
   ((check_freevars_ast:mlstring list->ast_t->bool) tvs (Attup ts) =
      (EVERY (check_freevars_ast tvs) ts)) /\
   ((check_freevars_ast:mlstring list->ast_t->bool) tvs (Atfun t1 t2)
     =
      (check_freevars_ast tvs t1 /\ check_freevars_ast tvs t2)) /\
   ((check_freevars_ast:mlstring list->ast_t->bool) tvs (Atapp ts tn)
     =
      (EVERY (check_freevars_ast tvs) ts))`;;

(* Simultaneous substitution of types for type variables in a type *)
let type_subst_def = cake_define
  `((type_subst:(mlstring,t)fmap->t->t) s (Tvar tv) =
      ((match FLOOKUP s tv with
         NONE -> Tvar tv | SOME (t) -> t))) /\
   ((type_subst:(mlstring,t)fmap->t->t) s (Tapp ts tn) =
      (Tapp (MAP (type_subst s) ts) tn)) /\
   ((type_subst:(mlstring,t)fmap->t->t) s (Tvar_db n) = (Tvar_db
     n))`;;

(* Increment the deBruijn indices in a type by n levels, skipping all
   levels
 * less than skip. *)
let deBruijn_inc_def = cake_define
  `((deBruijn_inc:num->num->t->t) skip n (Tvar tv) = (Tvar tv)) /\
   ((deBruijn_inc:num->num->t->t) skip n (Tvar_db m) =
      (if m < skip then
       Tvar_db m else
       Tvar_db (m + n))) /\
   ((deBruijn_inc:num->num->t->t) skip n (Tapp ts tn) = (Tapp (MAP
     (deBruijn_inc skip n) ts) tn))`;;

(* skip the lowest given indices and replace the next (LENGTH ts) with
   the given types and reduce all the higher ones *)
let deBruijn_subst_def = cake_define
  `((deBruijn_subst:num->t list->t->t) skip ts (Tvar tv) = (Tvar tv)) /\
   ((deBruijn_subst:num->t list->t->t) skip ts (Tvar_db n) =
      (if ~(n < skip) /\ (n < (LENGTH ts + skip)) then
       EL (n - skip) ts else if ~(n < skip) then
       Tvar_db (n - LENGTH ts) else
       Tvar_db n)) /\
   ((deBruijn_subst:num->t list->t->t) skip ts (Tapp ts' tn) =
      (Tapp (MAP (deBruijn_subst skip ts) ts') tn))`;;

(* Type environments *)
let tenv_val_exp_INDUCT,tenv_val_exp_RECURSION = define_datatype
  "tenv_val_exp = typeSystem_Empty | typeSystem_Bind_tvar (num) \
   (tenv_val_exp) | typeSystem_Bind_name (mlstring) (num) (t) \
   (tenv_val_exp)";;


(*val bind_tvar : nat -> tenv_val_exp -> tenv_val_exp*)
let bind_tvar_def = cake_define
  `((bind_tvar:num->tenv_val_exp->tenv_val_exp) tvs tenvE = (if tvs =
  (0:num) then tenvE else typeSystem_Bind_tvar tvs tenvE))`;;


(*val opt_bind_name : maybe varN -> nat -> t -> tenv_val_exp ->
   tenv_val_exp*)
let opt_bind_name_def = cake_define
  `((opt_bind_name:mlstring option->num->t->tenv_val_exp->tenv_val_exp)
  n tvs t tenvE =
     ((match n with
        NONE -> tenvE | SOME n' -> typeSystem_Bind_name n' tvs t
          tenvE)))`;;


(*val tveLookup : varN -> nat -> tenv_val_exp -> maybe (nat * t)*)
let tveLookup_def = cake_define
  `((tveLookup:mlstring->num->tenv_val_exp->(num#t) option) n inc
  typeSystem_Empty = NONE) /\
   ((tveLookup:mlstring->num->tenv_val_exp->(num#t) option) n inc
     (typeSystem_Bind_tvar tvs tenvE) = (tveLookup n (inc + tvs) tenvE))
     /\
   ((tveLookup:mlstring->num->tenv_val_exp->(num#t) option) n inc
     (typeSystem_Bind_name n' tvs t tenvE) =
      (if n' = n then
       SOME (tvs,deBruijn_inc tvs inc t) else
       tveLookup n inc tenvE))`;;


new_type_abbrev("tenv_abbrev",`: (mlstring,mlstring,mlstring
   list#t)namespace`);;
new_type_abbrev("tenv_ctor",`: (mlstring,mlstring,mlstring list#t
   list#num)namespace`);;
new_type_abbrev("tenv_val",`: (mlstring,mlstring,num#t)namespace`);;

let type_env_FIELDS = define_record "type_env"
  ["v","(mlstring,mlstring,num#t)namespace";
   "c","(mlstring,mlstring,mlstring list#t list#num)namespace";
   "t","(mlstring,mlstring,mlstring list#t)namespace"];;


(*val extend_dec_tenv : type_env -> type_env -> type_env*)
let extend_dec_tenv_def = cake_define
  `((extend_dec_tenv:type_env->type_env->type_env) tenv' tenv =
     (mk_? (nsAppend (?_v tenv') (?_v tenv)) (nsAppend (?_c tenv')
       (?_c tenv)) (nsAppend (type_env_t tenv') (type_env_t tenv))))`;;


(*val lookup_varE : id modN varN -> tenv_val_exp -> maybe (nat * t)*)
let lookup_varE_def = cake_define
  `((lookup_varE:(mlstring,mlstring)id->tenv_val_exp->(num#t) option) id
  tenvE =
     ((match id with
      Short x -> tveLookup x ((0:num)) tenvE | _1 -> NONE)))`;;


(*val lookup_var : id modN varN -> tenv_val_exp -> type_env -> maybe
   (nat * t)*)
let lookup_var_def = cake_define
  `((lookup_var:(mlstring,mlstring)id->tenv_val_exp->type_env->(num#t)
  option) id tenvE tenv =
     ((match lookup_varE id tenvE with
      SOME x -> SOME x | NONE -> nsLookup (?_v tenv) id)))`;;


(*val num_tvs : tenv_val_exp -> nat*)
let num_tvs_def = cake_define
  `((num_tvs:tenv_val_exp->num) typeSystem_Empty = ((0:num))) /\
   ((num_tvs:tenv_val_exp->num) (typeSystem_Bind_tvar tvs tenvE) =
     (tvs + num_tvs tenvE)) /\
   ((num_tvs:tenv_val_exp->num) (typeSystem_Bind_name n tvs t
     tenvE) = (num_tvs tenvE))`;;


(*val bind_var_list : nat -> list (varN * t) -> tenv_val_exp ->
   tenv_val_exp*)
let bind_var_list_def = cake_define
  `((bind_var_list:num->(mlstring#t) list->tenv_val_exp->tenv_val_exp)
  tvs [] tenvE = tenvE) /\
   ((bind_var_list:num->(mlstring#t)
     list->tenv_val_exp->tenv_val_exp) tvs ((n,t) :: binds) tenvE =
    (typeSystem_Bind_name n tvs t (bind_var_list tvs binds
      tenvE)))`;;


(* A pattern matches values of a certain type and extends the type
   environment
 * with the pattern's binders. The number is the maximum deBruijn type
   variable
 * allowed. *)
(*val type_p : nat -> type_env -> pat -> t -> list (varN * t) -> bool*)

(* An expression has a type *)
(*val type_e : type_env -> tenv_val_exp -> exp -> t -> bool*)

(* A list of expressions has a list of types *)
(*val type_es : type_env -> tenv_val_exp -> list exp -> list t -> bool*)

(* Type a mutually recursive bundle of functions.  Unlike pattern
   typing, the
 * resulting environment does not extend the input environment, but just
 * represents the functions *)
(*val type_funs : type_env -> tenv_val_exp -> list (varN * varN * exp)
   -> list (varN * t) -> bool*)

(* Check a declaration and update the top-level environments
 * The arguments are in order:
 * - whether to do extra checks
 * - the type environment
 * - the declaration
 * - the set of type identity stamps defined here
 * - the environment of new stuff declared here *)

let t_of_def = cake_define
  `t_of ast_BoolT = Tbool /\
   t_of ast_IntT = Tint /\
   t_of ast_CharT = Tchar /\
   t_of ast_StrT = Tstring /\
   t_of (ast_WordT ast_W8) = Tword8 /\
   t_of (ast_WordT ast_W64) = Tword64 /\
   t_of ast_Float64T = Tdouble`;;

let supported_test_def = cake_define
  `supported_test x1 ty =
      match x1 with
        (EQUAL) -> T
      | (ast_Compare _2) -> MEM ty [ast_IntT; ast_CharT; ast_WordT
        ast_W8; ast_Float64T; ast_StrT]
      | _3 -> (ty = ast_StrT)`;;

let supported_arith_def = cake_define
  `supported_arith a x2 =
        match x2 with
          ast_IntT ->
        if MEM a [ast_Add; ast_Sub; ast_Mul; ast_Div; ast_Mod] then
          SOME (2:num) else NONE
        | ast_Float64T ->
        if MEM a [ast_Abs; ast_Neg; ast_Sqrt] then SOME 1 else
        if MEM a [ast_Add; ast_Sub; ast_Mul; ast_Div] then SOME 2
          else
        if MEM a [ast_FMA] then SOME 3 else NONE
        | (ast_WordT _4) ->
        if MEM a [ast_Add; ast_Sub; ast_And; ast_Or; ast_Xor] then
          SOME 2 else NONE
        | ast_BoolT ->
        if MEM a [ast_Not] then SOME 1 else NONE
        | (ty:prim_type) -> NONE`;;

let supported_conversion_def = cake_define
  `supported_conversion x1 x2 =
        match (x1,x2) with
          ((ast_WordT ast_W8),ast_IntT) -> T
        | ((ast_WordT ast_W64),ast_IntT) -> T
        | (ast_IntT,(ast_WordT ast_W8)) -> T
        | (ast_IntT,(ast_WordT ast_W64)) -> T
        | (ast_CharT,ast_IntT) -> T
        | (ast_IntT,ast_CharT) -> T
        | (ast_CharT,(ast_WordT ast_W8)) -> T
        | ((ast_WordT ast_W8),ast_CharT) -> T
        | (ast_Float64T,(ast_WordT ast_W64)) -> T
        | ((ast_WordT ast_W64),ast_Float64T) -> T
        | ((from_ty:prim_type),(to_ty:prim_type)) -> F`;;

(* Check that the operator can have type (t1 -> ... -> tn -> t) *)
(*val type_op : op -> list t -> t -> bool*)
let type_op_def = cake_define
  `(type_op:ast_op->t list->t->bool) ast_op ts t =
     (match (ast_op,ts) with
        (ast_Opapp,[t1; t2]) -> t1 = Tfn t2 t | (ast_Shift ast_W8 _5
          _6,[t1]) -> (t1 = Tword8) /\ (t = Tword8) | (ast_Shift ast_W64
          _7 _8,[t1]) -> (t1 = Tword64) /\ (t = Tword64) |
          (ast_Equality,[t1; t2]) -> (t1 = t2) /\ (t = Tbool) |
          (ast_Arith a ty,ts) -> EVERY (\arg. arg = t_of ty) ts /\ (t =
          t_of ty) /\
                            supported_arith a ty = SOME (LENGTH ts) |
                              (ast_FromTo ty1 ty2,[t1]) -> (t1 = t_of
                              ty1) /\ (t = t_of ty2) /\
                              supported_conversion ty1 ty2 |
                                (ast_Test test ty,[t1; t2]) -> (t1 = t2)
                                /\ (t = Tbool) /\ (t1 = t_of ty) /\
                              supported_test test ty |
                                (ast_Opassign,[t1; t2]) -> (t1 = Tref
                                t2) /\ (t = Ttup []) | (ast_Opref,[t1])
                                -> t = Tref t1 | (ast_Opderef,[t1]) ->
                                t1 = Tref t | (ast_Aw8alloc,[t1; t2]) ->
                                (t1 = Tint) /\ (t2 = Tword8) /\ (t =
                                Tword8array) | (ast_Aw8sub,[t1; t2]) ->
                                (t1 = Tword8array) /\ (t2 = Tint) /\ (t
                                = Tword8) | (ast_Aw8length,[t1]) -> (t1
                                = Tword8array) /\ (t = Tint) |
                                (ast_Aw8update,[t1; t2; t3]) -> (t1 =
                                Tword8array) /\ (t2 = Tint) /\ (t3 =
                                Tword8) /\ (t = Ttup []) |
                                (ast_CopyStrStr,[t1; t2; t3]) -> (t1 =
                                Tstring) /\ (t2 = Tint) /\ (t3 = Tint)
                                /\ (t = Tstring) | (ast_CopyStrAw8,[t1;
                                t2; t3; t4; t5]) ->
        (t1 = Tstring) /\ (t2 = Tint) /\ (t3 = Tint) /\ (t4 =
          Tword8array) /\ (t5 = Tint) /\ (t = Ttup []) |
          (ast_CopyAw8Str,[t1; t2; t3]) -> (t1 = Tword8array) /\ (t2 =
          Tint) /\ (t3 = Tint) /\ (t = Tstring) | (ast_CopyAw8Aw8,[t1;
          t2; t3; t4; t5]) ->
        (t1 = Tword8array) /\ (t2 = Tint) /\ (t3 = Tint) /\ (t4 =
          Tword8array) /\ (t5 = Tint) /\ (t = Ttup []) |
          (ast_Implode,[t1]) -> (t1 = Tlist Tchar) /\ (t = Tstring) |
          (ast_Explode,[t1]) -> (t1 = Tstring) /\ (t = Tlist Tchar) |
          (ast_Strsub,[t1; t2]) -> (t1 = Tstring) /\ (t2 = Tint) /\
          (t = Tchar) | (ast_Strlen,[t1]) -> (t1 = Tstring) /\ (t =
          Tint) | (ast_Strcat,[t1]) -> (t1 = Tlist Tstring) /\ (t =
          Tstring) | (ast_VfromList,[Tapp [t1] ctor]) -> (ctor =
          Tlist_num) /\ (t = Tvector t1) | (ast_Vsub,[t1; t2]) -> (t2
          = Tint) /\ (Tvector t = t1) | (ast_Vlength,[Tapp [t1]
          ctor]) -> (ctor = Tvector_num) /\ (t = Tint) |
          (ast_Aalloc,[t1; t2]) -> (t1 = Tint) /\ (t = Tarray t2) |
          (ast_AallocEmpty,[t1]) -> (t1 = Ttup []) /\ (?t2. t =
          Tarray t2) | (ast_Asub,[t1; t2]) -> (t2 = Tint) /\ (Tarray
          t = t1) | (ast_Alength,[Tapp [t1] ctor]) -> (ctor =
          Tarray_num) /\ (t = Tint) | (ast_Aupdate,[t1; t2; t3]) ->
          (t1 = Tarray t3) /\ (t2 = Tint) /\ (t = Ttup []) |
          (ast_ConfigGC,[t1; t2]) -> (t1 = Tint) /\ (t2 = Tint) /\ (t
          = Ttup []) | (ast_FFI n,[t1; t2]) -> (t1 = Tstring) /\ (t2
          = Tword8array) /\ (t = Ttup []) | (ast_ListAppend,[Tapp
          [t1] ctor; t2]) -> (ctor = Tlist_num) /\ (t2 = Tapp [t1]
          ctor) /\ (t = t2) | _9 -> F)`;;

let check_type_names_def = cake_define
  `((check_type_names:(mlstring,mlstring,mlstring
  list#t)namespace->ast_t->bool) tenvT (Atvar tv) =
      T) /\
   ((check_type_names:(mlstring,mlstring,mlstring
     list#t)namespace->ast_t->bool) tenvT (Attup ts) =
      (EVERY (check_type_names tenvT) ts)) /\
   ((check_type_names:(mlstring,mlstring,mlstring
     list#t)namespace->ast_t->bool) tenvT (Atfun t1 t2) =
      (check_type_names tenvT t1 /\ check_type_names tenvT t2)) /\
   ((check_type_names:(mlstring,mlstring,mlstring
     list#t)namespace->ast_t->bool) tenvT (Atapp ts tn) =
      ((match nsLookup tenvT tn with
       SOME (tvs,_10) -> LENGTH tvs = LENGTH ts | NONE -> F) /\
     EVERY (check_type_names tenvT) ts))`;;

(* Substitution of type names for the type they abbreviate *)
let type_name_subst_def = cake_define
  `((type_name_subst:(mlstring,mlstring,mlstring
  list#t)namespace->ast_t->t) tenvT (Atvar tv) = (Tvar tv)) /\
   ((type_name_subst:(mlstring,mlstring,mlstring
     list#t)namespace->ast_t->t) tenvT (Attup ts) =
      (Ttup (MAP (type_name_subst tenvT) ts))) /\
   ((type_name_subst:(mlstring,mlstring,mlstring
     list#t)namespace->ast_t->t) tenvT (Atfun t1 t2) =
      (Tfn (type_name_subst tenvT t1) (type_name_subst tenvT t2))) /\
   ((type_name_subst:(mlstring,mlstring,mlstring
     list#t)namespace->ast_t->t) tenvT (Atapp ts tc) =
      (let args = (MAP (type_name_subst tenvT) ts) in
     (match nsLookup tenvT tc with
       SOME (tvs,t) -> type_subst (alist_to_fmap (ZIP (tvs,args)))
         t | NONE -> Ttup args)))`;;

(* Check that a type definition defines no already defined types or
   duplicate
 * constructors, and that the free type variables of each constructor
   argument
 * type are included in the type's type parameters. Also check that all
   of the
 * types mentioned are in scope. *)
(*val check_ctor_tenv : tenv_abbrev -> list (list tvarN * typeN * list
   (conN * list ast_t)) -> bool*)
let check_ctor_tenv_def = cake_define
  `((check_ctor_tenv:(mlstring,mlstring,mlstring
  list#t)namespace->(mlstring list#mlstring#(mlstring#ast_t list) list)
  list->bool) tenvT [] = T) /\
  ((check_ctor_tenv:(mlstring,mlstring,mlstring
  list#t)namespace->(mlstring list#mlstring#(mlstring#ast_t list) list)
  list->bool) tenvT ((tvs,tn,ctors) :: tds) =
     (check_dup_ctors (tvs,tn,ctors) /\
    ALL_DISTINCT tvs /\
    EVERY
      (\(cn,ts). EVERY (check_freevars_ast tvs) ts /\ EVERY
        (check_type_names tenvT) ts)
      ctors /\
    ~(MEM tn (MAP (\p.
    (match (p) with ((_11,tn,_12)) -> tn)) tds)) /\
    check_ctor_tenv tenvT tds))`;;


(*val build_ctor_tenv : tenv_abbrev -> list (list tvarN * typeN * list
   (conN * list ast_t)) -> list nat -> tenv_ctor*)
let build_ctor_tenv_def = cake_define
  `build_ctor_tenv tenvT x2 x3 =
        match (x2,x3) with
          ([],[]) -> (alist_to_ns [])
        | (((tvs,tn,ctors) :: tds),(id :: ids)) ->
      (nsAppend
       (build_ctor_tenv tenvT tds ids)
       (alist_to_ns
         (REVERSE
           (MAP
             (\(cn,ts). (cn,(tvs,MAP (type_name_subst tenvT) ts,id)))
             ctors))))
        | (_13,_14) -> (alist_to_ns [])`;;


(* For the value restriction on let-based polymorphism *)
let is_value_def = cake_define
  `is_value x1 =
        match x1 with
          (ast_Lit _15) -> T
        | (ast_Con _16 es) -> (EVERY is_value es)
        | (ast_Var _17) -> T
        | (ast_Fun _18 _19) -> T
        | (ast_Tannot e _20) -> (is_value e)
        | (ast_Lannot e _21) -> (is_value e)
        | _22 -> F`;;

let type_p = cake_inductive
  `(!tvs tenv t.
   (check_freevars tvs [] t) ==>
   type_p tvs tenv ast_Pany t []) /\
   (!tvs tenv n t.
   (check_freevars tvs [] t) ==>
   type_p tvs tenv (ast_Pvar n) t [(n,t)]) /\
   (!tvs tenv n.
   T ==>
   type_p tvs tenv (ast_Plit (ast_IntLit n)) Tint []) /\
   (!tvs tenv c.
   T ==>
   type_p tvs tenv (ast_Plit (ast_Char c)) Tchar []) /\
   (!tvs tenv s.
   T ==>
   type_p tvs tenv (ast_Plit (ast_StrLit s)) Tstring []) /\
   (!tvs tenv w.
   T ==>
   type_p tvs tenv (ast_Plit (ast_Word8 w)) Tword8 []) /\
   (!tvs tenv w.
   T ==>
   type_p tvs tenv (ast_Plit (ast_Word64 w)) Tword64 []) /\
   (!tvs tenv cn ps ts tvs' tn ts' bindings.
   (EVERY (check_freevars tvs []) ts' /\
   (LENGTH ts' = LENGTH tvs') /\
   type_ps tvs tenv ps (MAP (type_subst (alist_to_fmap (ZIP
     (tvs',ts')))) ts) bindings /\
   (nsLookup (?_c tenv) cn = SOME (tvs',ts,tn))) ==>
   type_p tvs tenv (ast_Pcon (SOME cn) ps) (Tapp ts' tn) bindings) /\
   (!tvs tenv ps ts bindings.
   (type_ps tvs tenv ps ts bindings) ==>
   type_p tvs tenv (ast_Pcon NONE ps) (Ttup ts) bindings) /\
   (!tvs tenv p t bindings.
   (type_p tvs tenv p t bindings) ==>
   type_p tvs tenv (ast_Pref p) (Tref t) bindings) /\
   (!tvs tenv ast_pat semanticPrimitives_v t bindings.
   (type_p tvs tenv ast_pat t bindings) ==>
   type_p tvs tenv (ast_Pas ast_pat semanticPrimitives_v) t (bindings
     ++ [(semanticPrimitives_v,t)])) /\
   (!tvs tenv p t bindings.
   (check_freevars_ast [] t /\
   check_type_names (type_env_t tenv) t /\
   type_p tvs tenv p (type_name_subst (type_env_t tenv) t) bindings)
     ==>
   type_p tvs tenv (ast_Ptannot p t) (type_name_subst (type_env_t
     tenv) t) bindings) /\
   (!tvs tenv.
   T ==>
   type_ps tvs tenv [] [] []) /\ (!tvs tenv p ps t ts bindings
     bindings'.
   (type_p tvs tenv p t bindings /\
   type_ps tvs tenv ps ts bindings') ==>
   type_ps tvs tenv (p :: ps) (t :: ts) (bindings' ++ bindings))`;;

let type_e = cake_inductive
  `(!tenv tenvE n.
   T ==>
   type_e tenv tenvE (ast_Lit (ast_IntLit n)) Tint) /\
   (!tenv tenvE c.
   T ==>
   type_e tenv tenvE (ast_Lit (ast_Char c)) Tchar) /\
   (!tenv tenvE s.
   T ==>
   type_e tenv tenvE (ast_Lit (ast_StrLit s)) Tstring) /\
   (!tenv tenvE w.
   T ==>
   type_e tenv tenvE (ast_Lit (ast_Word8 w)) Tword8) /\
   (!tenv tenvE w.
   T ==>
   type_e tenv tenvE (ast_Lit (ast_Word64 w)) Tword64) /\
   (!tenv tenvE w.
   T ==>
   type_e tenv tenvE (ast_Lit (ast_Float64 w)) Tdouble) /\
   (!tenv tenvE e t.
   (check_freevars (num_tvs tenvE) [] t /\
   type_e tenv tenvE e Texn) ==>
   type_e tenv tenvE (ast_Raise e) t) /\
   (!tenv tenvE e pes t.
   (type_e tenv tenvE e t /\ ~(pes = []) /\
   (!((p,e) :: LIST_TO_SET pes). ?bindings.
      ALL_DISTINCT (ast_pat_bindings p) /\
      type_p (num_tvs tenvE) tenv p Texn bindings /\
      type_e tenv (bind_var_list ((0:num)) bindings tenvE) e t)) ==>
   type_e tenv tenvE (ast_Handle e pes) t) /\
   (!tenv tenvE cn es tvs tn ts' ts.
   (EVERY (check_freevars (num_tvs tenvE) []) ts' /\
   (LENGTH tvs = LENGTH ts') /\
   type_es tenv tenvE es (MAP (type_subst (alist_to_fmap (ZIP
     (tvs,ts')))) ts) /\
   (nsLookup (?_c tenv) cn = SOME (tvs,ts,tn))) ==>
   type_e tenv tenvE (ast_Con (SOME cn) es) (Tapp ts' tn)) /\
   (!tenv tenvE es ts.
   (type_es tenv tenvE es ts) ==>
   type_e tenv tenvE (ast_Con NONE es) (Ttup ts)) /\
   (!tenv tenvE n t targs tvs.
   ((tvs = LENGTH targs) /\
   EVERY (check_freevars (num_tvs tenvE) []) targs /\
   (lookup_var n tenvE tenv = SOME (tvs,t))) ==>
   type_e tenv tenvE (ast_Var n) (deBruijn_subst ((0:num)) targs t))
     /\
   (!tenv tenvE n e t1 t2.
   (check_freevars (num_tvs tenvE) [] t1 /\
   type_e tenv (typeSystem_Bind_name n ((0:num)) t1 tenvE) e t2) ==>
   type_e tenv tenvE (ast_Fun n e) (Tfn t1 t2)) /\
   (!tenv tenvE ast_op es ts t.
   (type_es tenv tenvE es ts /\
   type_op ast_op ts t /\
   check_freevars (num_tvs tenvE) [] t) ==>
   type_e tenv tenvE (ast_App ast_op es) t) /\
   (!tenv tenvE l e1 e2.
   (type_e tenv tenvE e1 Tbool /\
   type_e tenv tenvE e2 Tbool) ==>
   type_e tenv tenvE (ast_Log l e1 e2) Tbool) /\
   (!tenv tenvE e1 e2 e3 t.
   (type_e tenv tenvE e1 Tbool /\
   type_e tenv tenvE e2 t /\
   type_e tenv tenvE e3 t) ==>
   type_e tenv tenvE (ast_If e1 e2 e3) t) /\
   (!tenv tenvE e pes t1 t2.
   (type_e tenv tenvE e t1 /\ ~(pes = []) /\
   (!((p,e) :: LIST_TO_SET pes). ?bindings.
      ALL_DISTINCT (ast_pat_bindings p) /\
      type_p (num_tvs tenvE) tenv p t1 bindings /\
      type_e tenv (bind_var_list ((0:num)) bindings tenvE) e t2)) ==>
   type_e tenv tenvE (ast_Mat e pes) t2) /\
   (!tenv tenvE n e1 e2 t1 t2.
   (type_e tenv tenvE e1 t1 /\
   type_e tenv (opt_bind_name n ((0:num)) t1 tenvE) e2 t2) ==>
   type_e tenv tenvE (ast_Let n e1 e2) t2) /\
   (!tenv tenvE funs e t bindings.
   (type_funs tenv (bind_var_list ((0:num)) bindings tenvE) funs
     bindings /\
   type_e tenv (bind_var_list ((0:num)) bindings tenvE) e t) ==>
   type_e tenv tenvE (ast_Letrec funs e) t) /\
   (!tenv tenvE e t.
   (check_freevars_ast [] t /\
   check_type_names (type_env_t tenv) t /\
   type_e tenv tenvE e (type_name_subst (type_env_t tenv) t)) ==>
   type_e tenv tenvE (ast_Tannot e t) (type_name_subst (type_env_t
     tenv) t)) /\
   (!tenv tenvE e l t.
   (type_e tenv tenvE e t) ==>
   type_e tenv tenvE (ast_Lannot e l) t) /\
   (!tenv tenvE.
   T ==>
   type_es tenv tenvE [] []) /\
   (!tenv tenvE e es t ts.
   (type_e tenv tenvE e t /\
   type_es tenv tenvE es ts) ==>
   type_es tenv tenvE (e :: es) (t :: ts)) /\
   (!tenv tenvE.
   T ==>
   type_funs tenv tenvE [] []) /\ (!tenv tenvE fn n e funs bindings
     t1 t2.
   (check_freevars (num_tvs tenvE) [] (Tfn t1 t2) /\
   type_e tenv (typeSystem_Bind_name n ((0:num)) t1 tenvE) e t2 /\
   type_funs tenv tenvE funs bindings /\
   (ALOOKUP bindings fn = NONE)) ==>
   type_funs tenv tenvE ((fn,n,e) :: funs) ((fn,Tfn t1 t2) ::
     bindings))`;;

(*val tenv_add_tvs : nat -> alist varN t -> alist varN (nat * t)*)
let tenv_add_tvs_def = cake_define
  `((tenv_add_tvs:num->(mlstring#t) list->(mlstring#num#t) list) tvs
  bindings =
     (MAP (\(n,t). (n,(tvs,t))) bindings))`;;


(*val type_pe_determ : type_env -> tenv_val_exp -> pat -> exp -> bool*)
let type_pe_determ_def = cake_define
  `((type_pe_determ:type_env->tenv_val_exp->ast_pat->ast_exp->bool) tenv
  tenvE p e =
     (!t1 tenv1 t2 tenv2.
      (type_p ((0:num)) tenv p t1 tenv1 /\ type_e tenv tenvE e t1 /\
      type_p ((0:num)) tenv p t2 tenv2 /\ type_e tenv tenvE e t2) ==>
      (tenv1 = tenv2)))`;;


(*val tscheme_inst : (nat * t) -> (nat * t) -> bool*)
let tscheme_inst_def = cake_define
  `((tscheme_inst:num#t->num#t->bool) (tvs_spec,t_spec)
  (tvs_impl,t_impl) =
     (?subst.
      (LENGTH subst = tvs_impl) /\
      check_freevars tvs_impl [] t_impl /\
      EVERY (check_freevars tvs_spec []) subst /\
      (deBruijn_subst ((0:num)) subst t_impl = t_spec)))`;;


let tenvLift_def = cake_define
  `((tenvLift:mlstring->type_env->type_env) mn tenv =
     (mk_? (nsLift mn (?_v tenv)) (nsLift mn (?_c tenv)) (nsLift
       mn (type_env_t tenv))))`;;


let type_d = cake_inductive
  `(!extra_checks tvs tenv p e t bindings locs.
   (is_value e /\
   ALL_DISTINCT (ast_pat_bindings p) /\
   type_p tvs tenv p t bindings /\
   type_e tenv (bind_tvar tvs typeSystem_Empty) e t /\
   (extra_checks ==>
     (!tvs' bindings' t'.
       (type_p tvs' tenv p t' bindings' /\
       type_e tenv (bind_tvar tvs' typeSystem_Empty) e t') ==>
         EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
           (MAP SND (tenv_add_tvs tvs bindings))))) ==>
   type_d extra_checks tenv (Dlet locs p e)
     {}
     (mk_? (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
       nsEmpty)) /\
   (!extra_checks tenv p e t bindings locs.
   (
   (extra_checks ==> (~(is_value e) /\ type_pe_determ tenv
     typeSystem_Empty p e)) /\
   ALL_DISTINCT (ast_pat_bindings p) /\
   type_p ((0:num)) tenv p t bindings /\
   type_e tenv typeSystem_Empty e t) ==>
   type_d extra_checks tenv (Dlet locs p e)
     {} (mk_? (alist_to_ns (tenv_add_tvs ((0:num)) bindings)) nsEmpty
       nsEmpty)) /\
   (!extra_checks tenv funs bindings tvs locs.
   (type_funs tenv (bind_var_list ((0:num)) bindings (bind_tvar tvs
     typeSystem_Empty)) funs bindings /\
   (extra_checks ==>
     (!tvs' bindings'.
       type_funs tenv (bind_var_list ((0:num)) bindings' (bind_tvar
         tvs' typeSystem_Empty)) funs bindings' ==>
         EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
           (MAP SND (tenv_add_tvs tvs bindings))))) ==>
   type_d extra_checks tenv (Dletrec locs funs)
     {} (mk_? (alist_to_ns (tenv_add_tvs tvs bindings)) nsEmpty
       nsEmpty)) /\
   (!extra_checks tenv tdefs type_identities tenvT locs.
   (ALL_DISTINCT type_identities /\
   DISJOINT (LIST_TO_SET type_identities)
            (LIST_TO_SET (Tlist_num :: (Tbool_num ::
              prim_type_nums))) /\
   check_ctor_tenv (nsAppend tenvT (type_env_t tenv)) tdefs /\
   (LENGTH type_identities = LENGTH tdefs) /\
   (tenvT = alist_to_ns (MAP2
                         (\(tvs,tn,ctors) i.
                           (tn,(tvs,Tapp (MAP Tvar tvs) i)))
                         tdefs type_identities))) ==>
   type_d extra_checks tenv (Dtype locs tdefs)
     (LIST_TO_SET type_identities)
     (mk_? nsEmpty (build_ctor_tenv (nsAppend tenvT (type_env_t
       tenv)) tdefs type_identities) tenvT)) /\
   (!extra_checks tenv tvs tn t locs.
   (check_freevars_ast tvs t /\
   check_type_names (type_env_t tenv) t /\
   ALL_DISTINCT tvs) ==>
   type_d extra_checks tenv (Dtabbrev locs tvs tn t)
     {}
     (mk_? nsEmpty nsEmpty (nsSing tn (tvs,type_name_subst
       (type_env_t tenv) t)))) /\
   (!extra_checks tenv cn ts locs.
   (EVERY (check_freevars_ast []) ts /\
   EVERY (check_type_names (type_env_t tenv)) ts) ==>
   type_d extra_checks tenv (Dexn locs cn ts)
     {}
     (mk_? nsEmpty (nsSing cn ([],MAP (type_name_subst (type_env_t
       tenv)) ts,Texn_num)) nsEmpty)) /\
   (!extra_checks tenv mn ds decls tenv'.
   (type_ds extra_checks tenv ds decls tenv') ==>
   type_d extra_checks tenv (Dmod mn ds) decls (tenvLift mn tenv'))
     /\
   (!extra_checks tenv lds ds tenv1 tenv2 decls1 decls2.
   (type_ds extra_checks tenv lds decls1 tenv1 /\
   type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2
     /\
   DISJOINT decls1 decls2) ==>
   type_d extra_checks tenv (Dlocal lds ds) (decls1 UNION decls2)
     tenv2) /\
   (!extra_checks tenv.
   T ==>
   type_ds extra_checks tenv []
     {}
     (mk_? nsEmpty nsEmpty nsEmpty)) /\ (!extra_checks tenv d ds
       tenv1 tenv2 decls1 decls2.
   (type_d extra_checks tenv d decls1 tenv1 /\
   type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2
     /\
   DISJOINT decls1 decls2) ==>
   type_ds extra_checks tenv (d :: ds)
     (decls1 UNION decls2) (extend_dec_tenv tenv2 tenv1))`;;

(*
indreln [type_specs : list modN -> tenv_abbrev -> specs -> decls ->
  type_env -> bool]

empty : forall mn tenvT.
true
==>
type_specs mn tenvT []
  empty_decls <| v = nsEmpty; c = nsEmpty; t = nsEmpty |>

and

sval : forall mn tenvT x t specs tenv fvs decls subst.
check_freevars 0 fvs t &&
check_type_names tenvT t &&
type_specs mn tenvT specs decls tenv &&
subst = alistToFmap (List_extra.zipSameLength fvs (List.map Tvar_db
  (genlist (fun x -> x) (List.length fvs))))
==>
type_specs mn tenvT (Sval x t :: specs)
  decls
  (extend_dec_tenv tenv
    <| v = nsSing x (List.length fvs, type_subst subst (type_name_subst
      tenvT t));
       c = nsEmpty;
       t = nsEmpty |>)

and

stype : forall mn tenvT tenv td specs decls' decls tenvT'.
tenvT' = alist_to_ns (List.map (fun (tvs,tn,ctors) -> (tn, (tvs, Tapp
  (List.map Tvar tvs) (TC_name (mk_id mn tn))))) td) &&
check_ctor_tenv (nsAppend tenvT' tenvT) td &&
type_specs mn (nsAppend tenvT' tenvT) specs decls tenv &&
decls' = <| defined_mods = {};
            defined_types = Set.fromList (List.map (fun (tvs,tn,ctors)
              -> (mk_id mn tn)) td);
            defined_exns = {} |>
==>
type_specs mn tenvT (Stype td :: specs)
  (union_decls decls decls')
  (extend_dec_tenv tenv
   <| v = nsEmpty;
      c = build_ctor_tenv mn (nsAppend tenvT' tenvT) td;
      t = tenvT' |>)

and

stabbrev : forall mn tenvT tenvT' tvs tn t specs decls tenv.
List.allDistinct tvs &&
check_freevars 0 tvs t &&
check_type_names tenvT t &&
tenvT' = nsSing tn (tvs,type_name_subst tenvT t) &&
type_specs mn (nsAppend tenvT' tenvT) specs decls tenv
==>
type_specs mn tenvT (Stabbrev tvs tn t :: specs)
  decls (extend_dec_tenv tenv <| v = nsEmpty; c = nsEmpty; t = tenvT'
    |>)

and

sexn : forall mn tenvT tenv cn ts specs decls.
check_exn_tenv mn cn ts &&
type_specs mn tenvT specs decls tenv &&
List.all (check_type_names tenvT) ts
==>
type_specs mn tenvT (Sexn cn ts :: specs)
  (union_decls decls <| defined_mods = {}; defined_types = {};
    defined_exns = {mk_id mn cn} |>)
  (extend_dec_tenv tenv
   <| v = nsEmpty;
      c = nsSing cn ([], List.map (type_name_subst tenvT) ts, TypeExn
        (mk_id mn cn));
      t = nsEmpty |>)

and

stype_opq : forall mn tenvT tenv tn specs tvs decls tenvT'.
List.allDistinct tvs &&
tenvT' = nsSing tn (tvs, Tapp (List.map Tvar tvs) (TC_name (mk_id mn
  tn))) &&
type_specs mn (nsAppend tenvT' tenvT) specs decls tenv
==>
type_specs mn tenvT (Stype_opq tvs tn :: specs)
  (union_decls decls <| defined_mods = {}; defined_types = {mk_id mn
    tn}; defined_exns = {} |>)
  (extend_dec_tenv tenv <| v = nsEmpty; c = nsEmpty; t = tenvT' |>)

val weak_decls : decls -> decls -> bool
let weak_decls decls_impl decls_spec =
  decls_impl.defined_mods = decls_spec.defined_mods &&
  decls_spec.defined_types subset decls_impl.defined_types &&
  decls_spec.defined_exns subset decls_impl.defined_exns
   *)

(*
val weak_tenvT : id modN typeN -> (list tvarN * t) -> (list tvarN * t)
  -> bool
let weak_tenvT n (tvs_spec, t_spec) (tvs_impl, t_impl) =
  (* For simplicity, we reject matches that differ only by renaming of
     bound type variables *)
  tvs_spec = tvs_impl &&
  (t_spec = t_impl ||
   (* The specified type is opaque *)
   t_spec = Tapp (List.map Tvar tvs_spec) (TC_name n))
   *)

let tscheme_inst2_def = cake_define
  `((tscheme_inst2:'a->num#t->num#t->bool) _23 ts1 ts2 =
  (tscheme_inst ts1 ts2))`;;


(*val weak_tenv : type_env -> type_env -> bool*)
let weak_tenv_def = cake_define
  `((weak_tenv:type_env->type_env->bool) tenv_impl tenv_spec =
     (nsSub tscheme_inst2 (?_v tenv_spec) (?_v tenv_impl) /\
    nsSub (\i x y. (match (i,x,y) with (_24,x,y) -> x = y)) (?_c
      tenv_spec) (?_c tenv_impl)))`;;
(* &&
  nsSub weak_tenvT tenv_spec.t tenv_impl.t*)

(*
indreln [check_signature : list modN -> tenv_abbrev -> decls -> type_env
  -> maybe specs -> decls -> type_env -> bool]

none : forall mn tenvT decls tenv.
true
==>
check_signature mn tenvT decls tenv Nothing decls tenv

and

some : forall mn specs tenv_impl tenv_spec decls_impl decls_spec tenvT.
weak_tenv tenv_impl tenv_spec &&
weak_decls decls_impl decls_spec &&
type_specs mn tenvT specs decls_spec tenv_spec
==>
check_signature mn tenvT decls_impl tenv_impl (Just specs) decls_spec
  tenv_spec

let tenvLift mn tenv =
  <| v = nsLift mn tenv.v; c = nsLift mn tenv.c; t = nsLift mn tenv.t;
    |>

indreln [type_top : bool -> decls -> type_env -> top -> decls ->
  type_env -> bool]

tdec : forall extra_checks tenv d tenv' decls decls'.
type_d extra_checks [] decls tenv d decls' tenv'
==>
type_top extra_checks decls tenv (Tdec d) decls' tenv'

and

tmod : forall extra_checks tenv mn spec ds tenv_impl tenv_spec decls
  decls_impl decls_spec.
not ([mn] IN decls.defined_mods) &&
type_ds extra_checks [mn] decls tenv ds decls_impl tenv_impl &&
check_signature [mn] tenv.t decls_impl tenv_impl spec decls_spec
  tenv_spec
==>
type_top extra_checks decls tenv (Tmod mn spec ds)
  (union_decls <| defined_mods = {[mn]}; defined_types = {};
    defined_exns = {} |> decls_spec)
  (tenvLift mn tenv_spec)

indreln [type_prog : bool -> decls -> type_env -> list top -> decls ->
  type_env -> bool]

empty : forall extra_checks tenv decls.
true
==>
type_prog extra_checks decls tenv [] empty_decls <| v = nsEmpty; c =
  nsEmpty; t = nsEmpty |>

and

cons : forall extra_checks tenv top tops tenv1 tenv2 decls decls1
  decls2.
type_top extra_checks decls tenv top decls1 tenv1 &&
type_prog extra_checks (union_decls decls1 decls) (extend_dec_tenv tenv1
  tenv) tops decls2 tenv2
==>
type_prog extra_checks decls tenv (top :: tops)
  (union_decls decls2 decls1) (extend_dec_tenv tenv2 tenv1)
  *)
