(* ======================================================== *)
(*  flatLang: ported from HOL4's
    compiler/backend/flatLangScript.sml
    A definition theory, with 4 definitions, 3 datatypes and 8
    theorems.  Needed by 12 files of the port.  *)
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
hol4_overload "Src" "flatLang_Src";;
hol4_overload "GlobalVarAlloc" "flatLang_GlobalVarAlloc";;
hol4_overload "GlobalVarInit" "flatLang_GlobalVarInit";;
hol4_overload "GlobalVarLookup" "flatLang_GlobalVarLookup";;
hol4_overload "TagLenEq" "flatLang_TagLenEq";;
hol4_overload "LenEq" "flatLang_LenEq";;
hol4_overload "El" "flatLang_El";;
hol4_overload "Id" "flatLang_Id";;

new_type_abbrev("ctor_id",`: num`);;
(* NONE represents the exception type *)
new_type_abbrev("type_id",`: num option`);;
new_type_abbrev("type_group_id",`: (num#(num#num) list) option`);;

let flatLang_pat_INDUCT,flatLang_pat_RECURSION = define_datatype
  "flatLang_pat = flatLang_Pany | flatLang_Pvar (mlstring) | \
   flatLang_Plit (lit) | flatLang_Pcon ((num#(num#(num#num) list) \
   option) option) (flatLang_pat list) | flatLang_Pas (flatLang_pat) \
   (mlstring) | flatLang_Pref (flatLang_pat)";;
hol4_overload "Pany" "flatLang_Pany";;
hol4_overload "Pvar" "flatLang_Pvar";;
hol4_overload "Plit" "flatLang_Plit";;
hol4_overload "Pcon" "flatLang_Pcon";;
hol4_overload "Pas" "flatLang_Pas";;
hol4_overload "Pref" "flatLang_Pref";;

let pat_bindings_def = cake_define_list
  [`flatLang_pat_bindings (Pany:flatLang_pat) = []`;
   `flatLang_pat_bindings (Pvar n:flatLang_pat) = [n]`;
   `flatLang_pat_bindings (Plit l:flatLang_pat) = []`;
   `flatLang_pat_bindings (Pcon _2 ps:flatLang_pat) =
  flatLang_pats_bindings ps`;
   `flatLang_pat_bindings (Pas p i:flatLang_pat) =
  flatLang_pat_bindings p ++ [i]`;
   `flatLang_pat_bindings (Pref p:flatLang_pat) =
  flatLang_pat_bindings p`;
   `flatLang_pats_bindings [] = []`;
   `flatLang_pats_bindings (p :: ps) = flatLang_pats_bindings ps ++
  flatLang_pat_bindings p`];;
hol4_overload "pat_bindings" "flatLang_pat_bindings";;
hol4_overload "pats_bindings" "flatLang_pats_bindings";;

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
hol4_overload "Raise" "flatLang_Raise";;
hol4_overload "Handle" "flatLang_Handle";;
hol4_overload "Lit" "flatLang_Lit";;
hol4_overload "Con" "flatLang_Con";;
hol4_overload "Var_local" "flatLang_Var_local";;
hol4_overload "Fun" "flatLang_Fun";;
hol4_overload "App" "flatLang_App";;
hol4_overload "If" "flatLang_If";;
hol4_overload "Mat" "flatLang_Mat";;
hol4_overload "Let" "flatLang_Let";;
hol4_overload "Letrec" "flatLang_Letrec";;

(* HOL4 flatLangScript.sml:86: ML code, not ported *)

let exp6_size_APPEND = cake_theorem "exp6_size_APPEND[simp]"
  (fun () ->
    `exp6_size (e ++ e2) = exp6_size e + exp6_size e2`)
  CHEAT_TAC;;

let exp6_size_REVERSE = cake_theorem "exp6_size_REVERSE[simp]"
  (fun () ->
    `exp6_size (REVERSE es) = exp6_size es`)
  CHEAT_TAC;;

let exp6_size = cake_theorem "exp6_size"
  (fun () ->
    `exp6_size xs = LENGTH xs + SUM (MAP flatLang_exp_size xs)`)
  CHEAT_TAC;;

let exp1_size = cake_theorem "exp1_size"
  (fun () ->
    `exp1_size xs = LENGTH xs + SUM (MAP exp2_size xs)`)
  CHEAT_TAC;;

let exp3_size = cake_theorem "exp3_size"
  (fun () ->
    `exp3_size xs = LENGTH xs + SUM (MAP exp5_size xs)`)
  CHEAT_TAC;;

let exp_size_MAP = cake_theorem "exp_size_MAP"
  (fun () ->
    `(!xs. exp6_size (MAP SND xs) < exp3_size xs + 1) /\
     (!xs. exp6_size (MAP (SND o SND) xs) < exp1_size xs + 1)`)
  CHEAT_TAC;;

let exp_size_MEM = cake_theorem "exp_size_MEM"
  (fun () ->
    `(!xs x. MEM x xs ==> flatLang_exp_size x < exp6_size xs) /\
     (!xs x. MEM x xs ==> flatLang_exp_size (SND (SND x)) <
       exp1_size xs) /\
     (!xs x. MEM x xs ==> flatLang_exp_size (SND x) < exp3_size
       xs)`)
  CHEAT_TAC;;

let bool_id_def = cake_define
  `bool_id = 0`;;

let bool_def = cake_define
  `flatLang_Bool t b = Con t (SOME (bool_to_tag b,SOME bool_id)) []`;;
hol4_overload "Bool" "flatLang_Bool";;

let SmartIf_def = cake_define
  `SmartIf t e p q =
     (match e with
       Con _3 (SOME (tag,SOME id')) [] ->
         (if id' = bool_id then
           if tag = true_tag then p else if tag = false_tag then q
             else If t e p q else If t e p q) | _4 -> If t e p q)`;;

let SmartIf_PMATCH = cake_theorem "SmartIf_PMATCH"
  (fun () ->
    `!t e p q.
       SmartIf t e p q =
         (match e with
           Con _5 (SOME (tag,SOME id')) [] ->
             (if id' = bool_id then
               if tag = true_tag then p else if tag = false_tag
                 then q else If t e p q else If t e p q) | _6 -> If t
                 e p q)`)
  CHEAT_TAC;;
