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

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "flatLang"
  ["ast"; "backend_common"];;

let _ = do_list hide_constant ["id"; "pmatch"];;

(* Most ops are inherited from ast$op via the Src wrapper.
 * GlobalVar ops, TagLenEq, LenEq, El, and Id are flatLang-specific. *)
let flatLang_op_INDUCT,flatLang_op_RECURSION = define_datatype
  "flatLang_op = flatLang_Src (ast_op) | \
   // Allocate the given number of new global variables\n\
   flatLang_GlobalVarAlloc (num) | \
   // Initialise given global variable\n\
   flatLang_GlobalVarInit (num) | \
   // Get the value of the given global variable\n\
   flatLang_GlobalVarLookup (num) | \
   // for pattern match compilation\n\
   flatLang_TagLenEq (num) (num) | flatLang_LenEq (num) | flatLang_El \
   (num) | \
   // No-op step for a single value\n\
   flatLang_Id";;

new_type_abbrev("ctor_id",`: num`);;
(* NONE represents the exception type *)
new_type_abbrev("type_id",`: num option`);;
new_type_abbrev("type_group_id",`: (num#(num#num) list) option`);;

let flatLang_pat_INDUCT,flatLang_pat_RECURSION = define_datatype
  "flatLang_pat = flatLang_Pany | flatLang_Pvar (mlstring) | \
   flatLang_Plit (lit) | flatLang_Pcon ((num#(num#(num#num) list) \
   option) option) (flatLang_pat list) | flatLang_Pas (flatLang_pat) \
   (mlstring) | flatLang_Pref (flatLang_pat)";;

let flatLang_pat_bindings_def,flatLang_pat_bindings_ind =
  define_mutual_rec
  [`flatLang_pat_bindings (flatLang_Pany:flatLang_pat) = []`;
   `flatLang_pat_bindings (flatLang_Pvar n:flatLang_pat) = [n]`;
   `flatLang_pat_bindings (flatLang_Plit l:flatLang_pat) = []`;
   `flatLang_pat_bindings (flatLang_Pcon _2 ps:flatLang_pat) =
  flatLang_pats_bindings ps`;
   `flatLang_pat_bindings (flatLang_Pas p i:flatLang_pat) = APPEND
  (flatLang_pat_bindings p) [i]`;
   `flatLang_pat_bindings (flatLang_Pref p:flatLang_pat) =
  flatLang_pat_bindings p`;
   `flatLang_pats_bindings [] = []`;
   `flatLang_pats_bindings (CONS p ps) = APPEND
  (flatLang_pats_bindings ps) (flatLang_pat_bindings p)`];;

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

(* HOL4 flatLangScript.sml:86: ML code, not ported *)

(* HOL4 flatLangScript.sml:88-92: a theorem whose statement the port
   cannot state yet: exp6_size_APPEND *)

(* HOL4 flatLangScript.sml:94-98: a theorem whose statement the port
   cannot state yet: exp6_size_REVERSE *)

(* HOL4 flatLangScript.sml:100-104: a theorem whose statement the
   port cannot state yet: exp6_size *)

(* HOL4 flatLangScript.sml:106-110: a theorem whose statement the
   port cannot state yet: exp1_size *)

(* HOL4 flatLangScript.sml:112-116: a theorem whose statement the
   port cannot state yet: exp3_size *)

(* HOL4 flatLangScript.sml:118-130: a theorem whose statement the
   port cannot state yet: exp_size_MAP *)

(* HOL4 flatLangScript.sml:132-149: a theorem whose statement the
   port cannot state yet: exp_size_MEM *)

let bool_id_def = new_definition
  `bool_id = 0`;;

let flatLang_Bool_def = new_definition
  `flatLang_Bool t b = flatLang_Con t (SOME (bool_to_tag b,SOME
  bool_id)) []`;;

let SmartIf_def = new_definition
  `SmartIf t e p q =
     (match e with
       flatLang_Con _3 (SOME (tag,SOME id')) [] ->
         (if id' = bool_id then
           if tag = true_tag then p else if tag = false_tag then q
             else flatLang_If t e p q else flatLang_If t e p q) | _4
             -> flatLang_If t e p q)`;;

let SmartIf_PMATCH = prove
 (`!t e p q.
     SmartIf t e p q =
       (match e with
         flatLang_Con _5 (SOME (tag,SOME id')) [] ->
           (if id' = bool_id then
             if tag = true_tag then p else if tag = false_tag then
               q else flatLang_If t e p q else flatLang_If t e p q) |
               _6 -> flatLang_If t e p q)`,
  CHEAT_TAC);;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id";
   "pmatch"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
