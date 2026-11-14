(* ======================================================== *)
(*  typeSoundInvariants: ported from HOL4's
    semantics/proofs/typeSoundInvariantsScript.sml
    A proof theory, with 18 definitions, 1 datatype and no theorems.
    Needed by 12 files of the port.  *)
(* ======================================================== *)

(*
  A type system for values, and
  the invariants that are used for type soundness.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "typeSoundInvariants"
  ["ast"; "namespace"; "namespaceProps"; "semanticPrimitives";
   "typeSystem"];;

let store_t_INDUCT,store_t_RECURSION = define_datatype
  "store_t =
     Ref_t t
   | W8array_t
   | Varray_t t";;

(* Store typing *)
new_type_abbrev("tenv_store",`:(num,store_t)fmap`);;

(* Check that the type names map to valid types *)
let tenv_abbrev_ok_def = new_definition
  `tenv_abbrev_ok tenvT <=> nsAll (\id' (tvs,t). check_freevars 0 tvs
  t) tenvT`;;

let tenv_ctor_ok_def = new_definition
  `tenv_ctor_ok tenvC <=> nsAll (\id' (tvs,ts,tn). ALL
  (check_freevars 0 tvs) ts) tenvC`;;

let tenv_val_ok_def = new_definition
  `tenv_val_ok tenvV <=> nsAll (\id' (tvs,t). check_freevars tvs []
  t) tenvV`;;

let tenv_ok_def = new_definition
  `tenv_ok tenv <=>
     tenv_val_ok (type_env_v tenv) /\
     tenv_ctor_ok (type_env_c tenv) /\
     tenv_abbrev_ok (type_env_t tenv)`;;

let tenv_val_exp_ok_def,tenv_val_exp_ok_ind = define_rec
  [`tenv_val_exp_ok (typeSystem_Empty:tenv_val_exp) <=> T`;
   `tenv_val_exp_ok (typeSystem_Bind_tvar n tenv) <=> tenv_val_exp_ok
    tenv`;
   `tenv_val_exp_ok (typeSystem_Bind_name x tvs t tenv) <=>
        check_freevars (tvs + num_tvs tenv) [] t /\
        tenv_val_exp_ok tenv`];;

(* Global constructor type environments keyed by constructor name and type
 * stamp. Contains the type variables, the type of the arguments, and
 * the identity of the type. *)
new_type_abbrev("ctMap",`:(stamp,tvarN list#t list#type_ident)fmap`);;

let ctMap_ok_def = new_definition
  `ctMap_ok ctMap <=>
     // No free variables in the range
     FEVERY (\(stamp,(tvs,ts,_1)). ALL (check_freevars 0 tvs) ts)
       ctMap /\
     (
      // Exceptions have type exception, and no type variables
      !ex tvs ts ti. FLOOKUP ctMap (ExnStamp ex) = SOME (tvs,ts,ti)
        ==>
       tvs = [] /\ ti = Texn_num) /\
     (
      // Primitive, non-constructor types are not mapped
      !cn x tvs ts ti. FLOOKUP ctMap (TypeStamp cn x) = SOME
        (tvs,ts,ti) ==>
       ~(MEM ti prim_type_nums)) /\
     (
      // If type identities are equal then the stamps are from the same type
      !stamp1 tvs1 ts1 ti stamp2 tvs2 ts2.
       FLOOKUP ctMap stamp1 = SOME (tvs1,ts1,ti) /\
       FLOOKUP ctMap stamp2 = SOME (tvs2,ts2,ti) ==>
       same_type stamp1 stamp2)`;;

(* Check that a constructor type environment is consistent with a runtime type
 * enviroment, using the full type keyed constructor type environment to ensure
 * that the correct types are used. *)
let type_ctor_def = new_definition
  `type_ctor ctMap _2 (n,stamp) (tvs,ts,ti) <=>
     FLOOKUP ctMap stamp = SOME (tvs,ts,ti) /\
     LENGTH ts = n`;;

let add_tenvE_def,add_tenvE_ind = define_rec
  [`add_tenvE (typeSystem_Empty:tenv_val_exp) tenvV = tenvV`;
   `add_tenvE (typeSystem_Bind_tvar _3 tenvE) tenvV = add_tenvE tenvE
    tenvV`;
   `add_tenvE (typeSystem_Bind_name x tvs t tenvE) tenvV = nsBind x
    (tvs,t) (add_tenvE tenvE tenvV)`];;

let type_v = cake_inductive
  `(!tvs ctMap tenvS n.
     type_v tvs ctMap tenvS (semanticPrimitives_Litv (ast_IntLit n))
       Tint) /\
   (!tvs ctMap tenvS c.
     type_v tvs ctMap tenvS (semanticPrimitives_Litv (ast_Char c))
       Tchar) /\
   (!tvs ctMap tenvS s.
     type_v tvs ctMap tenvS (semanticPrimitives_Litv (ast_StrLit s))
       Tstring) /\
   (!tvs ctMap tenvS w.
     type_v tvs ctMap tenvS (semanticPrimitives_Litv (ast_Word8 w))
       Tword8) /\
   (!tvs ctMap tenvS w.
     type_v tvs ctMap tenvS (semanticPrimitives_Litv (ast_Word64 w))
       Tword64) /\
   (!tvs ctMap tenvS w.
     type_v tvs ctMap tenvS (semanticPrimitives_Litv (ast_Float64 w))
       Tdouble) /\
   (!tvs ctMap tenvS vs tvs' stamp ts' ts ti.
     ALL (check_freevars tvs []) ts' /\
     LENGTH tvs' = LENGTH ts' /\
     ALL2 (type_v tvs ctMap tenvS)
       vs (MAP (type_subst (FUPDATE_LIST FEMPTY (REVERSE (ZIP tvs'
         ts')))) ts) /\
     FLOOKUP ctMap stamp = SOME (tvs',ts,ti) ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Conv (SOME stamp) vs)
       (Tapp ts' ti)) /\
   (!tvs ctMap tenvS vs ts.
     ALL2 (type_v tvs ctMap tenvS) vs ts ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Conv NONE vs) (Ttup
       ts)) /\
   (!tvs ctMap tenvS env tenv tenvE n e t1 t2.
     tenv_ok tenv /\
     tenv_val_exp_ok tenvE /\
     num_tvs tenvE = 0 /\
     nsAll2 (type_ctor ctMap) (sem_env_c env) (type_env_c tenv) /\
     nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v
       env) (add_tenvE tenvE (type_env_v tenv)) /\
     check_freevars tvs [] t1 /\
     type_e tenv (typeSystem_Bind_name n 0 t1 (bind_tvar tvs tenvE))
       e t2 ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Closure env n e) (Tfn
       t1 t2)) /\
   (!tvs ctMap tenvS env funs n t tenv tenvE bindings.
     tenv_ok tenv /\
     tenv_val_exp_ok tenvE /\
     num_tvs tenvE = 0 /\
     nsAll2 (type_ctor ctMap) (sem_env_c env) (type_env_c tenv) /\
     nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v
       env) (add_tenvE tenvE (type_env_v tenv)) /\
     type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE))
       funs bindings /\
     ALOOKUP bindings n = SOME t /\
     ALL_DISTINCT (MAP FST funs) /\
     MEM n (MAP FST funs) ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Recclosure env funs
       n) t) /\
   (!tvs ctMap tenvS n t.
     check_freevars 0 [] t /\
     FLOOKUP tenvS n = SOME (Ref_t t) ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Loc T n) (Tref t)) /\
   (!tvs ctMap tenvS n.
     FLOOKUP tenvS n = SOME W8array_t ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Loc T n) Tword8array)
       /\
   (!tvs ctMap tenvS n t.
     check_freevars 0 [] t /\
     FLOOKUP tenvS n = SOME (Varray_t t) ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Loc T n) (Tarray t))
       /\
   (!tvs ctMap tenvS vs t.
     check_freevars 0 [] t /\
     ALL (\v. type_v tvs ctMap tenvS v t) vs ==>
     type_v tvs ctMap tenvS (semanticPrimitives_Vectorv vs)
       (Tvector t))`;;

let type_sv_def = new_definition
  `type_sv ctMap tenvS x3 x4 =
        match (x3,x4) with
          (semanticPrimitives_Refv v,Ref_t t) -> type_v 0 ctMap tenvS
            v t
        | ((semanticPrimitives_W8array v),W8array_t) -> T
        | ((semanticPrimitives_Varray vs),(Varray_t t)) ->
       ALL (\v. type_v 0 ctMap tenvS v t) vs
        | (_4,_5) -> F`;;


(* The type of the store *)
let type_s_def = new_definition
  `type_s ctMap envS tenvS <=>
     (!l.
       ((?st. FLOOKUP tenvS l = SOME st) <=> (?v. store_lookup l envS
         = SOME v)) /\
       (!st sv.
         FLOOKUP tenvS l = SOME st /\ store_lookup l envS = SOME sv
           ==>
         type_sv ctMap tenvS sv st))`;;

(* The global constructor type environment has the primitive exceptions in it *)
let ctMap_has_exns_def = new_definition
  `ctMap_has_exns ctMap <=>
     FLOOKUP ctMap bind_stamp = SOME ([],[],Texn_num) /\
     FLOOKUP ctMap chr_stamp = SOME ([],[],Texn_num) /\
     FLOOKUP ctMap div_stamp = SOME ([],[],Texn_num) /\
     FLOOKUP ctMap subscript_stamp = SOME ([],[],Texn_num)`;;

(* The global constructor type environment has the list primitives in it *)
let ctMap_has_lists_def = new_definition
  `ctMap_has_lists ctMap <=>
     FLOOKUP ctMap (TypeStamp (implode "[]") list_type_num) = SOME
       ([(implode "'a")],[],Tlist_num) /\
     FLOOKUP ctMap (TypeStamp (implode "::") list_type_num) =
       SOME ([(implode "'a")],[Tvar (implode "'a"); Tlist (Tvar
         (implode "'a"))],Tlist_num) /\
     (!cn. ~(cn = (implode "::")) /\ ~(cn = (implode "[]")) ==>
       FLOOKUP ctMap (TypeStamp cn list_type_num) = NONE)`;;

(* The global constructor type environment has the bool primitives in it *)
let ctMap_has_bools_def = new_definition
  `ctMap_has_bools ctMap <=>
     FLOOKUP ctMap (TypeStamp (implode "True") bool_type_num) = SOME
       ([],[],Tbool_num) /\
     FLOOKUP ctMap (TypeStamp (implode "False") bool_type_num) = SOME
       ([],[],Tbool_num) /\
     (!cn. ~(cn = (implode "True")) /\ ~(cn = (implode "False"))
       ==> FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)`;;

let good_ctMap_def = new_definition
  `good_ctMap ctMap <=>
     ctMap_ok ctMap /\
     ctMap_has_bools ctMap /\
     ctMap_has_exns ctMap /\
     ctMap_has_lists ctMap`;;

(* HOL4 typeSoundInvariantsScript.sml:206-227: code that the source
   has in a comment *)

let consistent_ctMap_def = new_definition
  `consistent_ctMap st type_ids ctMap <=>
     (DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap))) /\
     (!cn id'.
       (TypeStamp cn id' IN FDOM ctMap ==> id' <
         semanticPrimitives_state_next_type_stamp st) /\
       (ExnStamp id' IN FDOM ctMap ==> id' <
         semanticPrimitives_state_next_exn_stamp st))`;;

(* HOL4 typeSoundInvariantsScript.sml:237-241: code that the source
   has in a comment *)

let type_all_env_def = new_definition
  `type_all_env ctMap tenvS env tenv <=>
     nsAll2 (type_ctor ctMap) (sem_env_c env) (type_env_c tenv) /\
     nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v
       env) (type_env_v tenv)`;;

let type_sound_invariant_def = new_definition
  `type_sound_invariant st env ctMap tenvS type_idents tenv <=>
     tenv_ok tenv /\
     good_ctMap ctMap /\
     consistent_ctMap st type_idents ctMap /\
     type_all_env ctMap tenvS env tenv /\
     type_s ctMap (semanticPrimitives_state_refs st) tenvS`;;

(* and the interface *)
let _ = unhide_overloads ();;
