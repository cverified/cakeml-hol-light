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

let ast_shift_INDUCT,ast_shift_RECURSION = define_datatype
  "ast_shift = Lsl | Lsr | Asr | Ror";;

let ast_arith_INDUCT,ast_arith_RECURSION = define_datatype
  "ast_arith = ast_Add | ast_Sub | ast_Mul | ast_Div | ast_Mod | \
   ast_Neg | ast_And | ast_Xor | ast_Or | ast_Not | ast_Abs | \
   ast_Sqrt | ast_FMA";;

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

let thunk_mode_INDUCT,thunk_mode_RECURSION = define_datatype
  "thunk_mode = Evaluated | NotEvaluated";;

let ast_thunk_op_INDUCT,ast_thunk_op_RECURSION = define_datatype
  "ast_thunk_op = AllocThunk (thunk_mode) | UpdateThunk (thunk_mode) \
   | ForceThunk";;

let opb_INDUCT,opb_RECURSION = define_datatype
  "opb = ast_Lt | ast_Gt | ast_Leq | ast_Geq";;

let test_INDUCT,test_RECURSION = define_datatype
  "test = ast_Equal | ast_Compare (opb) | ast_AltCompare (opb)";;

let prim_type_INDUCT,prim_type_RECURSION = define_datatype
  "prim_type = ast_BoolT | ast_IntT | ast_CharT | ast_StrT | \
   ast_WordT (word_size) | ast_Float64T";;

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

(* Define operator classes, that allow to group their behavior later *)
let op_class_INDUCT,op_class_RECURSION = define_datatype
  "op_class = ast_EvalOp | ast_FunApp | ast_Force | ast_Simple";;

let getOpClass_def = cake_define
  `getOpClass ast_op =
   (match ast_op with ast_Opapp -> ast_FunApp | ast_Eval ->
     ast_EvalOp | ast_ThunkOp t -> (if t = ForceThunk then ast_Force
     else ast_Simple) | _1 -> ast_Simple)`;;

(* Types used in type annotations *)
let ast_t_INDUCT,ast_t_RECURSION = define_datatype
  "ast_t = Atvar (mlstring) | Atfun (ast_t) (ast_t) | Attup (ast_t \
   list) | Atapp (ast_t list) ((mlstring,mlstring)id)";;

(* Patterns *)
let ast_pat_INDUCT,ast_pat_RECURSION = define_datatype
  "ast_pat = ast_Pany | ast_Pvar (mlstring) | ast_Plit (lit) | \
   ast_Pcon (((mlstring,mlstring)id) option) (ast_pat list) | \
   ast_Pref (ast_pat) | ast_Pas (ast_pat) (mlstring) | ast_Ptannot \
   (ast_pat) (ast_t)";;

(* Short circuiting logical operations *)
let lop_INDUCT,lop_RECURSION = define_datatype
  "lop = Andalso | Orelse";;

(* Expressions *)
let ast_exp_INDUCT,ast_exp_RECURSION = define_datatype
  "ast_exp = ast_Raise (ast_exp) | ast_Handle (ast_exp) \
   ((ast_pat#ast_exp) list) | ast_Lit (lit) | ast_Con \
   (((mlstring,mlstring)id) option) (ast_exp list) | ast_Var \
   ((mlstring,mlstring)id) | ast_Fun (mlstring) (ast_exp) | ast_App \
   (ast_op) (ast_exp list) | ast_Log (lop) (ast_exp) (ast_exp) | \
   ast_If (ast_exp) (ast_exp) (ast_exp) | ast_Mat (ast_exp) \
   ((ast_pat#ast_exp) list) | ast_Let (mlstring option) (ast_exp) \
   (ast_exp) | ast_Letrec ((mlstring#mlstring#ast_exp) list) \
   (ast_exp) | ast_Tannot (ast_exp) (ast_t) | ast_Lannot (ast_exp) \
   (locs)";;

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
let pat_bindings_def = cake_define
  `ast_pat_bindings ast_Pany = [] /\
   ast_pat_bindings (ast_Pvar n) = [n] /\
   ast_pat_bindings (ast_Plit l) = [] /\
   ast_pat_bindings (ast_Pcon v0 ps) = ast_pats_bindings ps /\
   ast_pat_bindings (ast_Pref p) = ast_pat_bindings p /\
   ast_pat_bindings (ast_Pas p i) = ast_pat_bindings p ++ [i] /\
   ast_pat_bindings (ast_Ptannot p v1) = ast_pat_bindings p /\
   ast_pats_bindings [] = [] /\
   ast_pats_bindings (p :: ps) = ast_pats_bindings ps ++
     ast_pat_bindings p`;;

let every_exp_def = cake_define
  `(every_exp p (ast_Raise e) <=>
              p (ast_Raise e) /\ every_exp p e) /\
   (every_exp p (ast_Handle e pes) <=>
              p (ast_Handle e pes) /\ every_exp p e /\ EVERY
                (\(ast_pat,e). every_exp p e) pes) /\
   (every_exp p (ast_Lit l) <=>
              p (ast_Lit l)) /\
   (every_exp p (ast_Con cn es) <=>
              p (ast_Con cn es) /\ EVERY (every_exp p) es) /\
   (every_exp p (ast_Var v) <=>
              p (ast_Var v)) /\
   (every_exp p (ast_Fun x e) <=>
              p (ast_Fun x e) /\ every_exp p e) /\
   (every_exp p (ast_App ast_op es) <=>
              p (ast_App ast_op es) /\ EVERY (every_exp p) es) /\
   (every_exp p (ast_Log lop e1 e2) <=>
              p (ast_Log lop e1 e2) /\ every_exp p e1 /\ every_exp p
                e2) /\
   (every_exp p (ast_If e1 e2 e3) <=>
              p (ast_If e1 e2 e3) /\ every_exp p e1 /\ every_exp p e2
                /\ every_exp p e3) /\
   (every_exp p (ast_Mat e pes) <=>
              p (ast_Mat e pes) /\ every_exp p e /\ EVERY
                (\(ast_pat,e). every_exp p e) pes) /\
   (every_exp p (ast_Let x e1 e2) <=>
              p (ast_Let x e1 e2) /\ every_exp p e1 /\ every_exp p
                e2) /\
   (every_exp p (ast_Tannot e a) <=>
              p (ast_Tannot e a) /\ every_exp p e) /\
   (every_exp p (ast_Lannot e a) <=>
              p (ast_Lannot e a) /\ every_exp p e) /\
   (every_exp p (ast_Letrec funs e) <=>
              p (ast_Letrec funs e) /\ every_exp p e /\ EVERY
                (\(n,v,e). every_exp p e) funs)`;;

let Seqs_def = cake_define
  `ast_Seqs [] = ast_Con NONE [] /\
   ast_Seqs (x :: xs) = ast_Let NONE x (ast_Seqs xs)`;;

let Apps_def = cake_define
  `Apps f' [] = f' /\
   Apps f' (x :: xs) = Apps (ast_App ast_Opapp [f'; x]) xs`;;

let Funs_def = cake_define
  `Funs [] e = e /\
   Funs (x :: xs) e = ast_Fun x (Funs xs e)`;;
