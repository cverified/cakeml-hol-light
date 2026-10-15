(* ======================================================== *)
(*  ast: ported from HOL4's
    semantics/astScript.sml  *)
(* ======================================================== *)

(*
  Definition of CakeML abstract syntax (AST).
*)

needs "basis/pure/mlstring.ml";;
needs "lib/location.ml";;
needs "semantics/namespace.ml";;
(* HOL4 ancestors outside the port: integer words string *)

(* Literal constants *)
let lit_INDUCT,lit_RECURSION = define_datatype
  "lit = ast_IntLit (int) | ast_Char (char) | ast_StrLit (mlstring) | \
   ast_Word8 (word8) | ast_Word64 (word64) | ast_Float64 (word64)";;
hol4_overload "IntLit" "ast_IntLit";;
hol4_overload "Char" "ast_Char";;
hol4_overload "StrLit" "ast_StrLit";;
hol4_overload "Word8" "ast_Word8";;
hol4_overload "Word64" "ast_Word64";;
hol4_overload "Float64" "ast_Float64";;

let ast_shift_INDUCT,ast_shift_RECURSION = define_datatype
  "ast_shift = Lsl | Lsr | Asr | Ror";;

let ast_arith_INDUCT,ast_arith_RECURSION = define_datatype
  "ast_arith = ast_Add | ast_Sub | ast_Mul | ast_Div | ast_Mod | \
   ast_Neg | ast_And | ast_Xor | ast_Or | ast_Not | ast_Abs | \
   ast_Sqrt | ast_FMA";;
hol4_overload "Add" "ast_Add";;
hol4_overload "Sub" "ast_Sub";;
hol4_overload "Mul" "ast_Mul";;
hol4_overload "Div" "ast_Div";;
hol4_overload "Mod" "ast_Mod";;
hol4_overload "Neg" "ast_Neg";;
hol4_overload "And" "ast_And";;
hol4_overload "Xor" "ast_Xor";;
hol4_overload "Or" "ast_Or";;
hol4_overload "Not" "ast_Not";;
hol4_overload "Abs" "ast_Abs";;
hol4_overload "Sqrt" "ast_Sqrt";;
hol4_overload "FMA" "ast_FMA";;

(* Module names *)
new_type_abbrev("modN",`: mlstring`);;

(* Variable names *)
new_type_abbrev("varN",`: mlstring`);;

(* Constructor names (from datatype definitions) *)
new_type_abbrev("conN",`: mlstring`);;

(* Type names *)
new_type_abbrev("typeN",`: mlstring`);;

(* Type variable names *)
new_type_abbrev("tvarN",`: mlstring`);;

let word_size_INDUCT,word_size_RECURSION = define_datatype
  "word_size = ast_W8 | ast_W64";;
hol4_overload "W8" "ast_W8";;
hol4_overload "W64" "ast_W64";;

let thunk_mode_INDUCT,thunk_mode_RECURSION = define_datatype
  "thunk_mode = Evaluated | NotEvaluated";;

let ast_thunk_op_INDUCT,ast_thunk_op_RECURSION = define_datatype
  "ast_thunk_op = AllocThunk (thunk_mode) | UpdateThunk (thunk_mode) \
   | ForceThunk";;

let opb_INDUCT,opb_RECURSION = define_datatype
  "opb = ast_Lt | ast_Gt | ast_Leq | ast_Geq";;
hol4_overload "Lt" "ast_Lt";;
hol4_overload "Gt" "ast_Gt";;
hol4_overload "Leq" "ast_Leq";;
hol4_overload "Geq" "ast_Geq";;

let test_INDUCT,test_RECURSION = define_datatype
  "test = ast_Equal | ast_Compare (opb) | ast_AltCompare (opb)";;
hol4_overload "Equal" "ast_Equal";;
hol4_overload "Compare" "ast_Compare";;
hol4_overload "AltCompare" "ast_AltCompare";;

let prim_type_INDUCT,prim_type_RECURSION = define_datatype
  "prim_type = ast_BoolT | ast_IntT | ast_CharT | ast_StrT | \
   ast_WordT (word_size) | ast_Float64T";;
hol4_overload "BoolT" "ast_BoolT";;
hol4_overload "IntT" "ast_IntT";;
hol4_overload "CharT" "ast_CharT";;
hol4_overload "StrT" "ast_StrT";;
hol4_overload "WordT" "ast_WordT";;
hol4_overload "Float64T" "ast_Float64T";;

let ast_op_INDUCT,ast_op_RECURSION = define_datatype
  "ast_op = ast_Arith (ast_arith) (prim_type) | ast_FromTo \
   (prim_type) (prim_type) | ast_Shift (word_size) (ast_shift) (num) \
   | ast_Equality | ast_Test (test) (prim_type) | ast_Opapp | \
   ast_Opassign | ast_Opref | ast_Opderef | ast_Aw8alloc | ast_Aw8sub \
   | ast_Aw8length | ast_Aw8update | ast_CopyStrStr | ast_CopyStrAw8 \
   | ast_CopyAw8Str | ast_CopyAw8Aw8 | ast_XorAw8Str_unsafe | \
   ast_Implode | ast_Explode | ast_Strsub | ast_Strlen | ast_Strcat | \
   ast_VfromList | ast_Vsub | ast_Vlength | ast_Aalloc | \
   ast_AallocEmpty | ast_AallocFixed | ast_Asub | ast_Alength | \
   ast_Aupdate | ast_Vsub_unsafe | ast_Asub_unsafe | \
   ast_Aupdate_unsafe | ast_Aw8sub_unsafe | ast_Aw8update_unsafe | \
   ast_ThunkOp (ast_thunk_op) | ast_ListAppend | ast_ConfigGC | \
   ast_FFI (mlstring) | ast_Eval | ast_Env_id";;
hol4_overload "Arith" "ast_Arith";;
hol4_overload "FromTo" "ast_FromTo";;
hol4_overload "Shift" "ast_Shift";;
hol4_overload "Equality" "ast_Equality";;
hol4_overload "Test" "ast_Test";;
hol4_overload "Opapp" "ast_Opapp";;
hol4_overload "Opassign" "ast_Opassign";;
hol4_overload "Opref" "ast_Opref";;
hol4_overload "Opderef" "ast_Opderef";;
hol4_overload "Aw8alloc" "ast_Aw8alloc";;
hol4_overload "Aw8sub" "ast_Aw8sub";;
hol4_overload "Aw8length" "ast_Aw8length";;
hol4_overload "Aw8update" "ast_Aw8update";;
hol4_overload "CopyStrStr" "ast_CopyStrStr";;
hol4_overload "CopyStrAw8" "ast_CopyStrAw8";;
hol4_overload "CopyAw8Str" "ast_CopyAw8Str";;
hol4_overload "CopyAw8Aw8" "ast_CopyAw8Aw8";;
hol4_overload "XorAw8Str_unsafe" "ast_XorAw8Str_unsafe";;
hol4_overload "Implode" "ast_Implode";;
hol4_overload "Explode" "ast_Explode";;
hol4_overload "Strsub" "ast_Strsub";;
hol4_overload "Strlen" "ast_Strlen";;
hol4_overload "Strcat" "ast_Strcat";;
hol4_overload "VfromList" "ast_VfromList";;
hol4_overload "Vsub" "ast_Vsub";;
hol4_overload "Vlength" "ast_Vlength";;
hol4_overload "Aalloc" "ast_Aalloc";;
hol4_overload "AallocEmpty" "ast_AallocEmpty";;
hol4_overload "AallocFixed" "ast_AallocFixed";;
hol4_overload "Asub" "ast_Asub";;
hol4_overload "Alength" "ast_Alength";;
hol4_overload "Aupdate" "ast_Aupdate";;
hol4_overload "Vsub_unsafe" "ast_Vsub_unsafe";;
hol4_overload "Asub_unsafe" "ast_Asub_unsafe";;
hol4_overload "Aupdate_unsafe" "ast_Aupdate_unsafe";;
hol4_overload "Aw8sub_unsafe" "ast_Aw8sub_unsafe";;
hol4_overload "Aw8update_unsafe" "ast_Aw8update_unsafe";;
hol4_overload "ThunkOp" "ast_ThunkOp";;
hol4_overload "ListAppend" "ast_ListAppend";;
hol4_overload "ConfigGC" "ast_ConfigGC";;
hol4_overload "FFI" "ast_FFI";;
hol4_overload "Eval" "ast_Eval";;
hol4_overload "Env_id" "ast_Env_id";;

(* Define operator classes, that allow to group their behavior later *)
let op_class_INDUCT,op_class_RECURSION = define_datatype
  "op_class = ast_EvalOp | ast_FunApp | ast_Force | ast_Simple";;
hol4_overload "EvalOp" "ast_EvalOp";;
hol4_overload "FunApp" "ast_FunApp";;
hol4_overload "Force" "ast_Force";;
hol4_overload "Simple" "ast_Simple";;

let getOpClass_def = cake_define
  `getOpClass op =
   (match op with ast_Opapp -> ast_FunApp | ast_Eval -> ast_EvalOp
     | ast_ThunkOp t -> (if t = ForceThunk then ast_Force else
     ast_Simple) | _1 -> ast_Simple)`;;

(* Types used in type annotations *)
let ast_t_INDUCT,ast_t_RECURSION = define_datatype
  "ast_t = Atvar (mlstring) | Atfun (ast_t) (ast_t) | Attup (ast_t \
   list) | Atapp (ast_t list) ((mlstring,mlstring)namespace_id)";;

(* Patterns *)
let ast_pat_INDUCT,ast_pat_RECURSION = define_datatype
  "ast_pat = ast_Pany | ast_Pvar (mlstring) | ast_Plit (lit) | \
   ast_Pcon (((mlstring,mlstring)namespace_id) option) (ast_pat list) \
   | ast_Pref (ast_pat) | ast_Pas (ast_pat) (mlstring) | ast_Ptannot \
   (ast_pat) (ast_t)";;
hol4_overload "Pany" "ast_Pany";;
hol4_overload "Pvar" "ast_Pvar";;
hol4_overload "Plit" "ast_Plit";;
hol4_overload "Pcon" "ast_Pcon";;
hol4_overload "Pref" "ast_Pref";;
hol4_overload "Pas" "ast_Pas";;
hol4_overload "Ptannot" "ast_Ptannot";;

(* Short circuiting logical operations *)
let lop_INDUCT,lop_RECURSION = define_datatype
  "lop = Andalso | Orelse";;

(* Expressions *)
let ast_exp_INDUCT,ast_exp_RECURSION = define_datatype
  "ast_exp = ast_Raise (ast_exp) | ast_Handle (ast_exp) \
   ((ast_pat#ast_exp) list) | ast_Lit (lit) | ast_Con \
   (((mlstring,mlstring)namespace_id) option) (ast_exp list) | \
   ast_Var ((mlstring,mlstring)namespace_id) | ast_Fun (mlstring) \
   (ast_exp) | ast_App (ast_op) (ast_exp list) | ast_Log (lop) \
   (ast_exp) (ast_exp) | ast_If (ast_exp) (ast_exp) (ast_exp) | \
   ast_Mat (ast_exp) ((ast_pat#ast_exp) list) | ast_Let (mlstring \
   option) (ast_exp) (ast_exp) | ast_Letrec \
   ((mlstring#mlstring#ast_exp) list) (ast_exp) | ast_Tannot \
   (ast_exp) (ast_t) | ast_Lannot (ast_exp) (locs)";;
hol4_overload "Raise" "ast_Raise";;
hol4_overload "Handle" "ast_Handle";;
hol4_overload "Lit" "ast_Lit";;
hol4_overload "Con" "ast_Con";;
hol4_overload "Var" "ast_Var";;
hol4_overload "Fun" "ast_Fun";;
hol4_overload "App" "ast_App";;
hol4_overload "Log" "ast_Log";;
hol4_overload "If" "ast_If";;
hol4_overload "Mat" "ast_Mat";;
hol4_overload "Let" "ast_Let";;
hol4_overload "Letrec" "ast_Letrec";;
hol4_overload "Tannot" "ast_Tannot";;
hol4_overload "Lannot" "ast_Lannot";;

new_type_abbrev("type_def",`: (mlstring list#mlstring#(mlstring#ast_t
   list) list) list`);;

(* Declarations *)
let dec_INDUCT,dec_RECURSION = define_datatype
  "dec = Dlet (locs) (ast_pat) (ast_exp) | Dletrec (locs) \
   ((mlstring#mlstring#ast_exp) list) | Dtype (locs) ((mlstring \
   list#mlstring#(mlstring#ast_t list) list) list) | Dtabbrev (locs) \
   (mlstring list) (mlstring) (ast_t) | Dexn (locs) (mlstring) (ast_t \
   list) | Dmod (mlstring) (dec list) | Dlocal (dec list) (dec list) \
   | Denv (mlstring)";;

(* Computes the bindings of a pattern *)
let pat_bindings_def = cake_define_list
  [`ast_pat_bindings ast_Pany = []`;
   `ast_pat_bindings (ast_Pvar n) = [n]`;
   `ast_pat_bindings (ast_Plit l) = []`;
   `ast_pat_bindings (ast_Pcon v0 ps) = ast_pats_bindings ps`;
   `ast_pat_bindings (ast_Pref p) = ast_pat_bindings p`;
   `ast_pat_bindings (ast_Pas p i) = ast_pat_bindings p ++ [i]`;
   `ast_pat_bindings (ast_Ptannot p v1) = ast_pat_bindings p`;
   `ast_pats_bindings [] = []`;
   `ast_pats_bindings (p :: ps) = ast_pats_bindings ps ++
  ast_pat_bindings p`];;
hol4_overload "pat_bindings" "ast_pat_bindings";;
hol4_overload "pats_bindings" "ast_pats_bindings";;

let every_exp_def = cake_define_list
  [`every_exp p (ast_Raise e) <=>
                 p (ast_Raise e) /\ every_exp p e`;
   `every_exp p (ast_Handle e pes) <=>
                 p (ast_Handle e pes) /\ every_exp p e /\ EVERY
                   (\(pat,e). every_exp p e) pes`;
   `every_exp p (ast_Lit l) <=>
                 p (ast_Lit l)`;
   `every_exp p (ast_Con cn es) <=>
                 p (ast_Con cn es) /\ EVERY (every_exp p) es`;
   `every_exp p (ast_Var v) <=>
                 p (ast_Var v)`;
   `every_exp p (ast_Fun x e) <=>
                 p (ast_Fun x e) /\ every_exp p e`;
   `every_exp p (ast_App op es) <=>
                 p (ast_App op es) /\ EVERY (every_exp p) es`;
   `every_exp p (ast_Log lop e1 e2) <=>
                 p (ast_Log lop e1 e2) /\ every_exp p e1 /\
                   every_exp p e2`;
   `every_exp p (ast_If e1 e2 e3) <=>
                 p (ast_If e1 e2 e3) /\ every_exp p e1 /\
                   every_exp p e2 /\ every_exp p e3`;
   `every_exp p (ast_Mat e pes) <=>
                 p (ast_Mat e pes) /\ every_exp p e /\ EVERY
                   (\(pat,e). every_exp p e) pes`;
   `every_exp p (ast_Let x e1 e2) <=>
                 p (ast_Let x e1 e2) /\ every_exp p e1 /\
                   every_exp p e2`;
   `every_exp p (ast_Tannot e a) <=>
                 p (ast_Tannot e a) /\ every_exp p e`;
   `every_exp p (ast_Lannot e a) <=>
                 p (ast_Lannot e a) /\ every_exp p e`;
   `every_exp p (ast_Letrec funs e) <=>
                 p (ast_Letrec funs e) /\ every_exp p e /\ EVERY
                   (\(n,v,e). every_exp p e) funs`];;

let seqs_def = cake_define_list
  [`ast_Seqs [] = ast_Con NONE []`;
   `ast_Seqs (x :: xs) = ast_Let NONE x (ast_Seqs xs)`];;
hol4_overload "Seqs" "ast_Seqs";;

let apps_def = cake_define_list
  [`Apps f [] = f`;
   `Apps f (x :: xs) = Apps (ast_App ast_Opapp [f; x]) xs`];;

let funs_def = cake_define_list
  [`Funs [] e = e`;
   `Funs (x :: xs) e = ast_Fun x (Funs xs e)`];;
