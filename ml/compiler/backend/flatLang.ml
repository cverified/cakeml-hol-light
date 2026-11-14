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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "flatLang"
  ["ast"; "backend_common"];;

let _ = do_list hide_constant ["id"; "pmatch"];;

(* Most ops are inherited from ast$op via the Src wrapper.
 * GlobalVar ops, TagLenEq, LenEq, El, and Id are flatLang-specific. *)
let flatLang_op_INDUCT,flatLang_op_RECURSION = define_datatype
  "flatLang_op =
     flatLang_Src ast_op
     // Allocate the given number of new global variables
   | flatLang_GlobalVarAlloc num
     // Initialise given global variable
   | flatLang_GlobalVarInit num
     // Get the value of the given global variable
   | flatLang_GlobalVarLookup num
     // for pattern match compilation
   | flatLang_TagLenEq num num
   | flatLang_LenEq num
   | flatLang_El num
     // No-op step for a single value
   | flatLang_Id";;

new_type_abbrev("ctor_id",`:num`);;
(* NONE represents the exception type *)
new_type_abbrev("type_id",`:num option`);;
new_type_abbrev("type_group_id",`:(num#(ctor_id#num) list) option`);;

let flatLang_pat_INDUCT,flatLang_pat_RECURSION = define_datatype
  "flatLang_pat =
     flatLang_Pany
   | flatLang_Pvar varN
   | flatLang_Plit lit
   | flatLang_Pcon ((ctor_id#type_group_id) option) (flatLang_pat list)
   | flatLang_Pas flatLang_pat varN
   | flatLang_Pref flatLang_pat";;

let flatLang_pat_bindings_def,flatLang_pat_bindings_ind = define_rec
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
  "flatLang_exp =
     flatLang_Raise tra flatLang_exp
   | flatLang_Handle tra flatLang_exp ((flatLang_pat#flatLang_exp) list)
   | flatLang_Lit tra lit
   | flatLang_Con tra ((ctor_id#type_id) option) (flatLang_exp list)
   | flatLang_Var_local tra varN
   | flatLang_Fun varN varN flatLang_exp
   | flatLang_App tra flatLang_op (flatLang_exp list)
   | flatLang_If tra flatLang_exp flatLang_exp flatLang_exp
   | flatLang_Mat tra flatLang_exp ((flatLang_pat#flatLang_exp) list)
   | flatLang_Let tra (varN option) flatLang_exp flatLang_exp
   | flatLang_Letrec varN ((varN#varN#flatLang_exp) list)
     flatLang_exp";;

(* HOL4 flatLangScript.sml:86: ML code, not ported *)

let _ = size_thms "flatLang_exp";;
let exp6_size_APPEND = prove
 (`list_size flatLang_exp_size (APPEND e e2) = list_size
  flatLang_exp_size e + list_size flatLang_exp_size e2`,
  CHEAT_TAC);;
add_simp exp6_size_APPEND;;

let exp6_size_REVERSE = prove
 (`list_size flatLang_exp_size (REVERSE es) = list_size
  flatLang_exp_size es`,
  CHEAT_TAC);;
add_simp exp6_size_REVERSE;;

let exp6_size = prove
 (`list_size flatLang_exp_size xs = LENGTH xs + SUM (MAP
  flatLang_exp_size xs)`,
  CHEAT_TAC);;

let _ = size_thms "mlstring";;
let exp1_size = prove
 (`list_size (pair_size mlstring_size
              (pair_size mlstring_size flatLang_exp_size)) xs =
                LENGTH xs + SUM (MAP (pair_size mlstring_size
                (pair_size mlstring_size flatLang_exp_size)) xs)`,
  CHEAT_TAC);;

let _ = size_thms "flatLang_pat";;
let exp3_size = prove
 (`list_size (pair_size flatLang_pat_size flatLang_exp_size) xs =
  LENGTH xs + SUM (MAP (pair_size flatLang_pat_size flatLang_exp_size)
  xs)`,
  CHEAT_TAC);;

let exp_size_MAP = prove
 (`(!xs. list_size flatLang_exp_size (MAP SND xs) < list_size (pair_size
  flatLang_pat_size flatLang_exp_size) xs + 1) /\
   (!xs. list_size flatLang_exp_size (MAP (SND o SND) xs) < list_size
     (pair_size mlstring_size
             (pair_size mlstring_size flatLang_exp_size)) xs + 1)`,
  CHEAT_TAC);;

let exp_size_MEM = prove
 (`(!xs x. MEM x xs ==> flatLang_exp_size x < list_size
  flatLang_exp_size xs) /\
   (!xs x. MEM x xs ==> flatLang_exp_size (SND (SND x)) < list_size
     (pair_size mlstring_size
             (pair_size mlstring_size flatLang_exp_size)) xs) /\
   (!xs x. MEM x xs ==> flatLang_exp_size (SND x) < list_size
     (pair_size flatLang_pat_size flatLang_exp_size) xs)`,
  CHEAT_TAC);;

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

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id";
   "pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
