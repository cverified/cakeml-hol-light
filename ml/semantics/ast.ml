(* ======================================================== *)
(*  ast: ported from HOL4's
    semantics/astScript.sml
    A definition theory, with 6 definitions, 16 datatypes and no
    theorems.  Needed by 78 files of the port.  *)
(* ======================================================== *)

(*
  Definition of CakeML abstract syntax (AST).
*)

needs "basis/pure/mlstring.ml";;
needs "lib/location.ml";;
needs "semantics/namespace.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "ast"
  ["mlstring"; "namespace"];;
(* HOL4 ancestors outside the port: integer words string *)

(* Literal constants *)
let lit_INDUCT,lit_RECURSION = define_datatype
  "lit =
     ast_IntLit int
   | ast_Char char
   | ast_StrLit mlstring
   | ast_Word8 word8
   | ast_Word64 word64
   | ast_Float64 word64";;

let ast_shift_INDUCT,ast_shift_RECURSION = define_datatype
  "ast_shift =
     Lsl
   | Lsr
   | Asr
   | Ror";;

let ast_arith_INDUCT,ast_arith_RECURSION = define_datatype
  "ast_arith =
     ast_Add
   | ast_Sub
   | ast_Mul
   | ast_Div
   | ast_Mod
   | ast_Neg
   | ast_And
   | ast_Xor
   | ast_Or
   | ast_Not
   | ast_Abs
   | ast_Sqrt
   | ast_FMA";;

(* Module names *)
new_type_abbrev("modN",`:mlstring`);;

(* Variable names *)
new_type_abbrev("varN",`:mlstring`);;

(* Constructor names (from datatype definitions) *)
new_type_abbrev("conN",`:mlstring`);;

(* Type names *)
new_type_abbrev("typeN",`:mlstring`);;

(* Type variable names *)
new_type_abbrev("tvarN",`:mlstring`);;

let word_size_INDUCT,word_size_RECURSION = define_datatype
  "word_size =
     ast_W8
   | ast_W64";;

let thunk_mode_INDUCT,thunk_mode_RECURSION = define_datatype
  "thunk_mode =
     Evaluated
   | NotEvaluated";;

let ast_thunk_op_INDUCT,ast_thunk_op_RECURSION = define_datatype
  "ast_thunk_op =
     AllocThunk thunk_mode
   | UpdateThunk thunk_mode
   | ForceThunk";;

let opb_INDUCT,opb_RECURSION = define_datatype
  "opb =
     ast_Lt
   | ast_Gt
   | ast_Leq
   | ast_Geq";;

let test_INDUCT,test_RECURSION = define_datatype
  "test =
     ast_Equal
   | ast_Compare opb
   | ast_AltCompare opb";;

let prim_type_INDUCT,prim_type_RECURSION = define_datatype
  "prim_type =
     ast_BoolT
   | ast_IntT
   | ast_CharT
   | ast_StrT
   | ast_WordT word_size
   | ast_Float64T";;

let ast_op_INDUCT,ast_op_RECURSION = define_datatype
  "ast_op =
     // primitive operations for the primitive types: +, -, and, sqrt, etc.
     ast_Arith ast_arith prim_type
     // conversions between primitive types: char<->int, word<->double, word<->int
   | ast_FromTo prim_type prim_type
     // Operations on words
   | ast_Shift word_size ast_shift num
   | ast_Equality
   | ast_Test test prim_type
     // Function application
   | ast_Opapp
     // Reference operations
   | ast_Opassign
   | ast_Opref
   | ast_Opderef
     // Word8Array operations
   | ast_Aw8alloc
   | ast_Aw8sub
   | ast_Aw8length
   | ast_Aw8update
     // string/bytearray conversions
   | ast_CopyStrStr
   | ast_CopyStrAw8
   | ast_CopyAw8Str
   | ast_CopyAw8Aw8
   | ast_XorAw8Str_unsafe
     // String operations
   | ast_Implode
   | ast_Explode
   | ast_Strsub
   | ast_Strlen
   | ast_Strcat
     // Vector operations
   | ast_VfromList
   | ast_Vsub
   | ast_Vlength
     // Array operations
   | ast_Aalloc
   | ast_AallocEmpty
   | ast_AallocFixed
   | ast_Asub
   | ast_Alength
   | ast_Aupdate
     // Unsafe vector/array accesses
   | ast_Vsub_unsafe
   | ast_Asub_unsafe
   | ast_Aupdate_unsafe
   | ast_Aw8sub_unsafe
   | ast_Aw8update_unsafe
     // thunk operations
   | ast_ThunkOp ast_thunk_op
     // List operations
   | ast_ListAppend
     // Configure the GC
   | ast_ConfigGC
     // Call a given foreign function
   | ast_FFI mlstring
     // Evaluate new code in a given env
   | ast_Eval
     // Get the identifier of an env object
   | ast_Env_id";;

(* Define operator classes, that allow to group their behavior later *)
let op_class_INDUCT,op_class_RECURSION = define_datatype
  "op_class =
     ast_EvalOp
     // Eval primitive
   | ast_FunApp
     // function application
   | ast_Force
     // forcing a thunk
   | ast_Simple
     // arithmetic operation, no finite-precision/reals
  ";;

let getOpClass_def = new_definition
  `getOpClass op =
   (match op with ast_Opapp -> ast_FunApp | ast_Eval -> ast_EvalOp
     | ast_ThunkOp t -> (if t = ForceThunk then ast_Force else
     ast_Simple) | _1 -> ast_Simple)`;;
add_simp getOpClass_def;;

(* Types used in type annotations *)
let ast_t_INDUCT,ast_t_RECURSION = define_datatype
  "ast_t =
     // Type variables that the user writes down ('a, 'b, etc.)
     Atvar tvarN
     // Function type
   | Atfun ast_t ast_t
     // Tuple type
   | Attup (ast_t list)
     // Type constructor applications.
     // 0-ary type applications represent unparameterised types (e.g., num or string)
   | Atapp (ast_t list) ((modN,typeN)namespace_id)";;

(* Patterns *)
let ast_pat_INDUCT,ast_pat_RECURSION = define_datatype
  "ast_pat =
     ast_Pany
   | ast_Pvar varN
   | ast_Plit lit
     // Constructor applications.
     // A Nothing constructor indicates a tuple pattern.
   | ast_Pcon (((modN,conN)namespace_id) option) (ast_pat list)
   | ast_Pref ast_pat
     // Pattern alias.
   | ast_Pas ast_pat varN
   | ast_Ptannot ast_pat ast_t";;

(* Short circuiting logical operations *)
let lop_INDUCT,lop_RECURSION = define_datatype
  "lop =
     Andalso
   | Orelse";;

(* Expressions *)
let ast_exp_INDUCT,ast_exp_RECURSION = define_datatype
  "ast_exp =
     ast_Raise ast_exp
   | ast_Handle ast_exp ((ast_pat#ast_exp) list)
   | ast_Lit lit
     // Constructor application.
     // A Nothing constructor indicates a tuple pattern.
   | ast_Con (((modN,conN)namespace_id) option) (ast_exp list)
   | ast_Var ((modN,varN)namespace_id)
   | ast_Fun varN ast_exp
     // Application a primitive operator to arguments.
     // Includes function application.
   | ast_App ast_op (ast_exp list)
     // Logical operations (and, or)
   | ast_Log lop ast_exp ast_exp
   | ast_If ast_exp ast_exp ast_exp
     // Pattern matching
   | ast_Mat ast_exp ((ast_pat#ast_exp) list)
     // A let expression
     // A Nothing value for the binding indicates that this is a
     // sequencing expression, that is: (e1; e2).
   | ast_Let (varN option) ast_exp ast_exp
     // Local definition (potentially) mutually recursive
     // functions.
     // The first varN is the function's name, and the second varN
     // is its parameter.
   | ast_Letrec ((varN#varN#ast_exp) list) ast_exp
   | ast_Tannot ast_exp ast_t
     // Location annotated expressions, not expected in source programs
   | ast_Lannot ast_exp locs";;

new_type_abbrev("type_def",`:(tvarN list#typeN#(conN#ast_t list)
   list) list`);;

(* Declarations *)
let dec_INDUCT,dec_RECURSION = define_datatype
  "dec =
     // Top-level bindings
     // * The pattern allows several names to be bound at once
     Dlet locs ast_pat ast_exp
     // Mutually recursive function definition
   | Dletrec locs ((varN#varN#ast_exp) list)
     // Type definition
     // Defines several data types, each which has several
     // named variants, which can in turn have several arguments.
   | Dtype locs type_def
     // Type abbreviations
   | Dtabbrev locs (tvarN list) typeN ast_t
     // New exceptions
   | Dexn locs conN (ast_t list)
     // Module
   | Dmod modN (dec list)
     // Local: local part, visible part
   | Dlocal (dec list) (dec list)
     // Store current lexical env in an env value
   | Denv tvarN";;

(* Computes the bindings of a pattern *)
let pat_bindings_def,pat_bindings_ind = define_rec
  [`ast_pat_bindings (ast_Pany:ast_pat) = []`;
   `ast_pat_bindings (ast_Pvar n:ast_pat) = [n]`;
   `ast_pat_bindings (ast_Plit l:ast_pat) = []`;
   `ast_pat_bindings (ast_Pcon v0 ps:ast_pat) = ast_pats_bindings ps`;
   `ast_pat_bindings (ast_Pref p:ast_pat) = ast_pat_bindings p`;
   `ast_pat_bindings (ast_Pas p i:ast_pat) = APPEND (ast_pat_bindings
    p) [i]`;
   `ast_pat_bindings (ast_Ptannot p v1) = ast_pat_bindings p`;
   `ast_pats_bindings [] = []`;
   `ast_pats_bindings (CONS p ps) = APPEND (ast_pats_bindings ps)
    (ast_pat_bindings p)`];;

let every_exp_def,every_exp_ind = define_shaped_rec
  "nested"
  [`every_exp p (ast_Raise e:ast_exp) <=>
                 p ((ast_Raise e:ast_exp)) /\ every_exp p e`;
   `every_exp p (ast_Handle e pes:ast_exp) <=>
                 p ((ast_Handle e pes:ast_exp)) /\ every_exp p e
                     /\ ALL (\(pat,e). every_exp p e) pes`;
   `every_exp p (ast_Lit l) <=>
                 p (ast_Lit l)`;
   `every_exp p (ast_Con cn es:ast_exp) <=>
                 p ((ast_Con cn es:ast_exp)) /\ ALL (every_exp p)
                     es`;
   `every_exp p (ast_Var v:ast_exp) <=>
                 p ((ast_Var v:ast_exp))`;
   `every_exp p (ast_Fun x e:ast_exp) <=>
                 p ((ast_Fun x e:ast_exp)) /\ every_exp p e`;
   `every_exp p (ast_App op es:ast_exp) <=>
                 p ((ast_App op es:ast_exp)) /\ ALL (every_exp p)
                     es`;
   `every_exp p (ast_Log lop e1 e2) <=>
                 p (ast_Log lop e1 e2) /\ every_exp p e1 /\
                     every_exp p e2`;
   `every_exp p (ast_If e1 e2 e3:ast_exp) <=>
                 p ((ast_If e1 e2 e3:ast_exp)) /\ every_exp p e1
                     /\ every_exp p e2 /\ every_exp p e3`;
   `every_exp p (ast_Mat e pes:ast_exp) <=>
                 p ((ast_Mat e pes:ast_exp)) /\ every_exp p e /\
                     ALL (\(pat,e). every_exp p e) pes`;
   `every_exp p (ast_Let x e1 e2:ast_exp) <=>
                 p ((ast_Let x e1 e2:ast_exp)) /\ every_exp p e1
                     /\ every_exp p e2`;
   `every_exp p (ast_Tannot e a) <=>
                 p (ast_Tannot e a) /\ every_exp p e`;
   `every_exp p (ast_Lannot e a) <=>
                 p (ast_Lannot e a) /\ every_exp p e`;
   `every_exp p (ast_Letrec funs e:ast_exp) <=>
                 p ((ast_Letrec funs e:ast_exp)) /\ every_exp p
                     e /\ ALL (\(n,v,e). every_exp p e) funs`];;
add_simp every_exp_def;;

let seqs_def,seqs_ind = define_rec
  [`ast_Seqs [] = ast_Con NONE []`;
   `ast_Seqs (CONS x xs) = ast_Let NONE x (ast_Seqs xs)`];;

let apps_def,apps_ind = define_rec
  [`Apps f [] = f`;
   `Apps f (CONS x xs) = Apps (ast_App ast_Opapp [f; x]) xs`];;

let funs_def,funs_ind = define_rec
  [`Funs [] e = e`;
   `Funs (CONS x xs) e = ast_Fun x (Funs xs e)`];;
