(* ======================================================== *)
(*  mlbasicsProg: ported from HOL4's
    basis/mlbasicsProgScript.sml
    A definition theory, with 6 definitions and 2 theorems.  Needed
    by IntProg.ml and SexpProg.ml.  *)
(* ======================================================== *)

(*
  Translates a variety of basic constructs.

  In particular, we vind various built-in functions to function names that
  the parser expects, e.g. the parser generates a call to a function called "+"
  when it parses 1+2.
*)

needs "basis/StringProg.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/pattern_matching/pattern_semantics.ml";;
needs "lib/location.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/namespace.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "mlbasicsProg"
  ["StringProg"; "cf"; "ml_prog"; "ml_translator"; "semanticPrimitives"];;

(* HOL4 mlbasicsProgScript.sml:14: ML code, not ported *)

let mlbasicsProg_mk_binop_def = new_definition
  `mlbasicsProg_mk_binop name prim = Dlet unknown_loc (ast_Pvar name)
     (ast_Fun (implode "x") (ast_Fun (implode "y") (ast_App prim [ast_Var
       (Short (implode "x")); ast_Var (Short (implode "y"))])))`;;

let mk_unop_def = new_definition
  `mk_unop name prim = Dlet unknown_loc (ast_Pvar name)
     (ast_Fun (implode "x") (ast_App prim [ast_Var (Short (implode
       "x"))]))`;;

(* no longer necessary
(* list, bool, and option come from the primitive types in
 * semantics/primTypesTheory *)
val _ = append_prog
  ``[Tdec (Dtabbrev unknown_loc [] "int" (Tapp [] TC_int));
     Tdec (Dtabbrev unknown_loc [] "unit" (Tapp [] TC_tup));
     Tdec (Dtabbrev unknown_loc [] "string" (Tapp [] TC_string));
     Tdec (Dtabbrev unknown_loc ["'a"] "ref" (Tapp [Tvar "'a"] TC_ref));
     Tdec (Dtabbrev unknown_loc ["'a"] "vector" (Tapp [Tvar "'a"] TC_vector));
     Tdec (Dtabbrev unknown_loc ["'a"] "array" (Tapp [Tvar "'a"] TC_array));
     Tdec (Dtabbrev unknown_loc [] "exn" (Tapp [] TC_exn));
     Tdec (Dtabbrev unknown_loc [] "word" (Tapp [] TC_word64));
     Tdec (Dtabbrev unknown_loc [] "char" (Tapp [] TC_char))]``
*)

(* HOL4 mlbasicsProgScript.sml:41-51: the ML values that the definitions
   below antiquote *)


(* other basics that parser targets -- CF verified *)

(* HOL4 mlbasicsProgScript.sml:56-59: the ML values that the definitions
   below antiquote *)

(* HOL4 mlbasicsProgScript.sml:61-64: ML code, not ported *)

(* HOL4 mlbasicsProgScript.sml:66-71: a proof *)

(* HOL4 mlbasicsProgScript.sml:73-80: code that the source has in a comment *)

(* HOL4 mlbasicsProgScript.sml:82-87: a theorem whose statement the port
   cannot state yet: deref_spec *)

(* HOL4 mlbasicsProgScript.sml:89-95: a theorem whose statement the port
   cannot state yet: assign_spec *)

let bool_toString_def = new_definition
  `bool_toString b = if b then (implode "True") else (implode "False")`;;

let bool_fromString_def = new_definition
  `bool_fromString s = if s = (implode "True") then SOME T else if s =
  (implode "False") then SOME F else NONE`;;

(* HOL4 mlbasicsProgScript.sml:107-117: the ML values that the definitions
   below antiquote *)

let pair_toString_def = new_definition
  `pair_toString f1 f2 (x,y) =
     mlvector_concat [(implode "(");
             f1 x;
             (implode ", ");
             f2 y;
             (implode ")")]`;;

(* HOL4 mlbasicsProgScript.sml:128-135: ML code, not ported *)


(* HOL4 mlbasicsProgScript.sml:138-140: ML code, not ported *)

(* HOL4 mlbasicsProgScript.sml:142: the ML values that the definitions below
   antiquote *)

let fail_exn_def = new_definition
  `Fail_exn s v = (?sv. v = semanticPrimitives_Conv (SOME ((implode
  "Fail"))) [sv] /\ STRING_TYPE s sv)`;;

(* and the interface *)
let _ = unhide_overloads ();;
