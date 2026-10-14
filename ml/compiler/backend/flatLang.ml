(* ======================================================== *)
(*  flatLang: ported from HOL4's
    compiler/backend/flatLangScript.sml  *)
(* ======================================================== *)

(*
  The first intermediate language flatLang. It removes modules and
  resolves all global scoping. Each value definition gets allocated a
  slot in a global variable store, and each type and exception gets a
  unique global identifier. It removes andalso and orelse and
  replaces them with if, and removes the AallocEmpty primitive op and
  replaces it with an alloc call with 0.

  The AST of flatLang differs from the source language by having two
  variable reference forms, one to reference local bindings (still by
  name) and one to reference global bindings (by index). At the top
  level, modules and let recs are gone. Top-level lets and letrecs no
  longer bind names (or have patterns). Constructor names are replaced
  with numbers, and type and exception definitions record the arities
  of the constructors rather than the types. Type annotations are
  also gone.
*)

needs "compiler/backend/backend_common.ml";;
needs "semantics/ast.ml";;

(* Most ops are inherited from ast$op via the Src wrapper.
 * GlobalVar ops, TagLenEq, LenEq, El, and Id are flatLang-specific. *)
let flatLang_op_INDUCT,flatLang_op_RECURSION = define_datatype
  "flatLang_op = flatLang_Src (ast_op) | flatLang_GlobalVarAlloc \
   (num) | flatLang_GlobalVarInit (num) | flatLang_GlobalVarLookup \
   (num) | flatLang_TagLenEq (num) (num) | flatLang_LenEq (num) | \
   flatLang_El (num) | flatLang_Id";;

new_type_abbrev("ctor_id",`: num`);;
(* NONE represents the exception type *)
new_type_abbrev("type_id",`: num option`);;
new_type_abbrev("type_group_id",`: (num#(num#num) list) option`);;

let flatLang_pat_INDUCT,flatLang_pat_RECURSION = define_datatype
  "flatLang_pat = flatLang_Pany | flatLang_Pvar (mlstring) | \
   flatLang_Plit (lit) | flatLang_Pcon ((num#(num#(num#num) list) \
   option) option) (flatLang_pat list) | flatLang_Pas (flatLang_pat) \
   (mlstring) | flatLang_Pref (flatLang_pat)";;

let pat_bindings_def = cake_define
  `(flatLang_pat_bindings flatLang_Pany = []) /\
   (flatLang_pat_bindings (flatLang_Pvar n) = [n]) /\
   (flatLang_pat_bindings (flatLang_Plit l) = []) /\
   (flatLang_pat_bindings (flatLang_Pcon _1 ps) =
     flatLang_pats_bindings ps) /\
   (flatLang_pat_bindings (flatLang_Pas p i) = flatLang_pat_bindings
     p ++ [i]) /\
   (flatLang_pat_bindings (flatLang_Pref p) = flatLang_pat_bindings
     p) /\
   (flatLang_pats_bindings [] = []) /\
   (flatLang_pats_bindings (p :: ps) = flatLang_pats_bindings ps
     ++ flatLang_pat_bindings p)`;;

let flatLang_exp_INDUCT,flatLang_exp_RECURSION = define_datatype
  "flatLang_exp = flatLang_Raise (tra) (flatLang_exp) | \
   flatLang_Handle (tra) (flatLang_exp) ((flatLang_pat#flatLang_exp) \
   list) | flatLang_Lit (tra) (lit) | flatLang_Con (tra) ((num#num \
   option) option) (flatLang_exp list) | flatLang_Var_local (tra) \
   (mlstring) | flatLang_Fun (mlstring) (mlstring) (flatLang_exp) | \
   flatLang_App (tra) (flatLang_op) (flatLang_exp list) | flatLang_If \
   (tra) (flatLang_exp) (flatLang_exp) (flatLang_exp) | flatLang_Mat \
   (tra) (flatLang_exp) ((flatLang_pat#flatLang_exp) list) | \
   flatLang_Let (tra) (mlstring option) (flatLang_exp) (flatLang_exp) \
   | flatLang_Letrec (mlstring) ((mlstring#mlstring#flatLang_exp) \
   list) (flatLang_exp)";;

(* HOL4 ML code, not ported:
val exp_size_def = definition"exp_size_def";
*)

let bool_id_def = cake_define
  `bool_id = 0`;;

let Bool_def = cake_define
  `flatLang_Bool t b = flatLang_Con t (SOME (bool_to_tag b,SOME
  bool_id)) []`;;

let SmartIf_def = cake_define
  `SmartIf t e p q =
     (match e with
       flatLang_Con _2 (SOME (tag,SOME id)) [] ->
         (if id = bool_id then
           if tag = true_tag then p else if tag = false_tag then q
             else flatLang_If t e p q else flatLang_If t e p q) | _3
             -> flatLang_If t e p q)`;;
