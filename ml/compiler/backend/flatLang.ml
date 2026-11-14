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
let flat_op_INDUCT,flat_op_RECURSION = define_datatype
  "flat_op =
     flat_Src ast_op
     // Allocate the given number of new global variables
   | flat_GlobalVarAlloc num
     // Initialise given global variable
   | flat_GlobalVarInit num
     // Get the value of the given global variable
   | flat_GlobalVarLookup num
     // for pattern match compilation
   | flat_TagLenEq num num
   | flat_LenEq num
   | flat_El num
     // No-op step for a single value
   | flat_Id";;

new_type_abbrev("ctor_id",`:num`);;
(* NONE represents the exception type *)
new_type_abbrev("type_id",`:num option`);;
new_type_abbrev("type_group_id",`:(num#(ctor_id#num) list) option`);;

let flat_pat_INDUCT,flat_pat_RECURSION = define_datatype
  "flat_pat =
     flat_Pany
   | flat_Pvar varN
   | flat_Plit lit
   | flat_Pcon ((ctor_id#type_group_id) option) (flat_pat list)
   | flat_Pas flat_pat varN
   | flat_Pref flat_pat";;

let flat_pat_bindings_def,flat_pat_bindings_ind = define_rec
  `(flat_pat_bindings flat_Pany = []) /\
   (flat_pat_bindings (flat_Pvar n) = [n]) /\
   (flat_pat_bindings (flat_Plit l) = []) /\
   (flat_pat_bindings (flat_Pcon _ ps) = flat_pats_bindings ps) /\
   (flat_pat_bindings (flat_Pas p i) = APPEND (flat_pat_bindings p) [i]) /\
   (flat_pat_bindings (flat_Pref p) = flat_pat_bindings p) /\
   (flat_pats_bindings [] = []) /\
   (flat_pats_bindings (CONS p ps) = APPEND (flat_pats_bindings ps)
    (flat_pat_bindings p))`;;

let flat_exp_INDUCT,flat_exp_RECURSION = define_datatype
  "flat_exp =
     flat_Raise tra flat_exp
   | flat_Handle tra flat_exp ((flat_pat#flat_exp) list)
   | flat_Lit tra lit
   | flat_Con tra ((ctor_id#type_id) option) (flat_exp list)
   | flat_Var_local tra varN
   | flat_Fun varN varN flat_exp
   | flat_App tra flat_op (flat_exp list)
   | flat_If tra flat_exp flat_exp flat_exp
   | flat_Mat tra flat_exp ((flat_pat#flat_exp) list)
   | flat_Let tra (varN option) flat_exp flat_exp
   | flat_Letrec varN ((varN#varN#flat_exp) list) flat_exp";;

(* HOL4 flatLangScript.sml:86: ML code, not ported *)

let exp6_size_APPEND = prove
 (`list_size flat_exp_size (APPEND e e2) = list_size flat_exp_size e +
  list_size flat_exp_size e2`,
  CHEAT_TAC);;
add_simp exp6_size_APPEND;;

let exp6_size_REVERSE = prove
 (`list_size flat_exp_size (REVERSE es) = list_size flat_exp_size es`,
  CHEAT_TAC);;
add_simp exp6_size_REVERSE;;

let exp6_size = prove
 (`list_size flat_exp_size xs = LENGTH xs + SUM (MAP flat_exp_size xs)`,
  CHEAT_TAC);;

let exp1_size = prove
 (`list_size (pair_size mlstring_size
              (pair_size mlstring_size flat_exp_size)) xs = LENGTH xs +
                SUM (MAP (pair_size mlstring_size (pair_size mlstring_size
                flat_exp_size)) xs)`,
  CHEAT_TAC);;

let exp3_size = prove
 (`list_size (pair_size flat_pat_size flat_exp_size) xs = LENGTH xs + SUM
  (MAP (pair_size flat_pat_size flat_exp_size) xs)`,
  CHEAT_TAC);;

let exp_size_MAP = prove
 (`(!xs. list_size flat_exp_size (MAP SND xs) < list_size (pair_size
  flat_pat_size flat_exp_size) xs + 1) /\
   (!xs. list_size flat_exp_size (MAP (SND o SND) xs) < list_size (pair_size
     mlstring_size
             (pair_size mlstring_size flat_exp_size)) xs + 1)`,
  CHEAT_TAC);;

let exp_size_MEM = prove
 (`(!xs x. MEM x xs ==> flat_exp_size x < list_size flat_exp_size xs) /\
   (!xs x. MEM x xs ==> flat_exp_size (SND (SND x)) < list_size (pair_size
     mlstring_size
             (pair_size mlstring_size flat_exp_size)) xs) /\
   (!xs x. MEM x xs ==> flat_exp_size (SND x) < list_size (pair_size
     flat_pat_size flat_exp_size) xs)`,
  CHEAT_TAC);;

let bool_id_def = new_definition
  `bool_id = 0`;;

let flat_Bool_def = new_definition
  `flat_Bool t b = flat_Con t (SOME (bool_to_tag b,SOME bool_id)) []`;;

let SmartIf_def = new_definition
  `SmartIf t e p q =
     match e with
       flat_Con _ (SOME (tag,SOME id')) [] ->
         if id' = bool_id then
           if tag = true_tag then p
           else if tag = false_tag then q
           else flat_If t e p q
         else flat_If t e p q
     | _ -> flat_If t e p q`;;

let SmartIf_PMATCH = prove
 (`!t e p q.
     SmartIf t e p q =
       match e with
         flat_Con _ (SOME (tag,SOME id')) [] ->
           if id' = bool_id then
             if tag = true_tag then p
             else if tag = false_tag then q
             else flat_If t e p q
           else flat_If t e p q
       | _ -> flat_If t e p q`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["id";
   "pmatch"];;

(* and the interface *)
let _ = unhide_overloads ();;
