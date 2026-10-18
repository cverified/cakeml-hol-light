(* ======================================================== *)
(*  typeSysProps: ported from HOL4's
    semantics/proofs/typeSysPropsScript.sml  *)
(* ======================================================== *)

(*
  Theorems about the type system.
*)

needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/proofs/namespaceProps.ml";;
needs "semantics/proofs/semanticPrimitivesProps.ml";;
needs "semantics/proofs/typeSoundInvariants.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* HOL4 typeSysPropsScript.sml:14: ML code, not ported *)
(* HOL4 typeSysPropsScript.sml:15-20: code that the source has in a
   comment *)

(* HOL4 typeSysPropsScript.sml:22-37: ML code, not ported *)

(* ----------- Basic stuff ----------- *)

(* HOL4 typeSysPropsScript.sml:48-78: code that the source has in a
   comment *)

let type_pes_def = cake_define
  `type_pes tvs tvs' tenv tenvE pes t1 t2 <=>
     (RES_FORALL (set_of_list pes) (\(p,e).
       ?bindings.
         ALL_DISTINCT (ast_pat_bindings p) /\
         type_p tvs tenv p t1 bindings /\
         type_e tenv (bind_var_list tvs' bindings tenvE) e t2))`;;

(* ---------- check_freevars ---------- *)

(* ---------- type_subst ---------- *)

(* ---------- deBruijn_inc ---------- *)

(* ---------- deBruijn_subst ---------- *)

(* ---------- tenv_abbrev stuff ---------- *)

(* ---------- tenv_ctor stuff ----------*)

(* ---------- tenv_val_exp stuff ---------- *)

let deBruijn_subst_tenvE_def = cake_define_list
  [`deBruijn_subst_tenvE targs (typeSystem_Empty:tenv_val_exp) =
  (typeSystem_Empty:tenv_val_exp)`;
   `deBruijn_subst_tenvE targs (typeSystem_Bind_tvar tvs env) =
      typeSystem_Bind_tvar tvs (deBruijn_subst_tenvE targs env)`;
   `deBruijn_subst_tenvE targs (typeSystem_Bind_name x tvs t env) =
      typeSystem_Bind_name x tvs (deBruijn_subst (tvs + num_tvs env)
                              (MAP (deBruijn_inc 0 (tvs + num_tvs
                                env)) targs)
                              t)
           (deBruijn_subst_tenvE targs env)`];;

let db_merge_def = cake_define_list
  [`db_merge (typeSystem_Empty:tenv_val_exp) e = e`;
   `db_merge (typeSystem_Bind_tvar tvs e1) e2 = typeSystem_Bind_tvar
  tvs (db_merge e1 e2)`;
   `db_merge (typeSystem_Bind_name x tvs t e1) e2 =
  typeSystem_Bind_name x tvs t (db_merge e1 e2)`];;

(* ---------- type_op ---------- *)

(* HOL4 typeSysPropsScript.sml:909-917: ML code, not ported *)

(* ---------- type_p ---------- *)

(* ---------- type_e, type_es, type_funs ---------- *)

(* Recursive functions have function type *)

(* Recursive functions can be looked up in the execution environment. *)

(* Functions in the type environment can be found *)

(* No duplicate function definitions in a single let rec *)


(* HOL4 typeSysPropsScript.sml:1654-1685: code that the source has in
   a comment *)

(* ---------- ctMap stuff ---------- *)


let type_def_to_ctMap_def = cake_define_list
  [`type_def_to_ctMap tenvT next_stamp [] [] = []`;
   `type_def_to_ctMap tenvT next_stamp ((tvs,tn,ctors) :: tds) (id' ::
  ids) =
        type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
        REVERSE
          (MAP (\(cn,ts).
            (TypeStamp cn next_stamp,(tvs,MAP (type_name_subst
              tenvT) ts,id')))
            ctors)`];;


(* HOL4 typeSysPropsScript.sml:1893-1982: code that the source has in
   a comment *)

(* HOL4 typeSysPropsScript.sml:1997-2054: code that the source has in
   a comment *)

(* ---------- consistent_decls ---------- *)

(* HOL4 typeSysPropsScript.sml:2088-2130: code that the source has in
   a comment *)

(* ---------- type_v  ---------- *)

(* HOL4 typeSysPropsScript.sml:2254-2259: ML code, not ported *)

(* HOL4 typeSysPropsScript.sml:2407-2421: code that the source has in
   a comment *)

(* ---------- type_d ---------- *)

(* HOL4 typeSysPropsScript.sml:2554-2572: code that the source has in
   a comment *)

(* ---------- type_ds ---------- *)

(* HOL4 typeSysPropsScript.sml:2595-2617: code that the source has in
   a comment *)

(* HOL4 typeSysPropsScript.sml:2619-2720: code that the source has in
   a comment *)

(* ---------- type_specs ---------- *)

(* HOL4 typeSysPropsScript.sml:2724-2843: code that the source has in
   a comment *)

(* ---------------- type_top, type_prog ---------- *)
(* HOL4 typeSysPropsScript.sml:2846-3039: code that the source has in
   a comment *)
(* HOL4 typeSysPropsScript.sml:3040-3382: code that the source has in
   a comment *)

(* HOL4 typeSysPropsScript.sml:3384-3408: code that the source has in
   a comment *)
