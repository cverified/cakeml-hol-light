(* ======================================================== *)
(*  panLang: ported from HOL4's
    pancake/panLangScript.sml
    A definition theory, with 24 definitions, 10 datatypes and 2
    theorems.  Needed by compiler.ml, evaluateProps.ml and infer.ml.  *)
(* ======================================================== *)

(*
  Abstract syntax for Pancake language.
  Pancake is an imperative language with
  instructions for conditionals, While loop,
  memory load and store, functions,
  and foreign function calls.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
(* for overloading the shift operation *)
needs "compiler/encoders/asm/asm.ml";;
(* for binop and cmp *)

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "panLang"
  ["asm"; "backend_common"; "mlstring"];;


(* for overloading the shift operation *)

new_type_abbrev("panLang_shift",`:ast_shift`);;

new_type_abbrev("stcname",`:mlstring`);;

new_type_abbrev("fldname",`:mlstring`);;

new_type_abbrev("varname",`:mlstring`);;

new_type_abbrev("funname",`:mlstring`);;

new_type_abbrev("eid",`:mlstring`);;

new_type_abbrev("decname",`:mlstring`);;

new_type_abbrev("index",`:num`);;

let shape_INDUCT,shape_RECURSION = define_datatype
  "shape =
     One
   | Comb (shape list)
   | Named stcname";;

let panop_INDUCT,panop_RECURSION = define_datatype
  "panop =
     // Div |
     panLang_Mul
     // | Mod
  ";;

let varkind_INDUCT,varkind_RECURSION = define_datatype
  "varkind =
     panLang_Local
   | panLang_Global";;

let panLang_exp_INDUCT,panLang_exp_RECURSION = define_datatype
  "panLang_exp =
     panLang_Const ('a word)
   | panLang_Var varkind varname
   | panLang_RStruct (panLang_exp list)
   | panLang_RField index panLang_exp
   | panLang_NStruct stcname ((fldname#panLang_exp) list)
   | panLang_NField fldname panLang_exp
   | panLang_Load shape panLang_exp
     // exp: start addr of value with given shape
   | panLang_Load32 panLang_exp
   | panLang_LoadByte panLang_exp
   | panLang_Op binop (panLang_exp list)
   | panLang_Panop panop (panLang_exp list)
   | panLang_Cmp cmp panLang_exp panLang_exp
   | panLang_Shift panLang_shift panLang_exp panLang_exp
   | panLang_BaseAddr
   | panLang_TopAddr
   | panLang_BytesInWord";;

let opsize_INDUCT,opsize_RECURSION = define_datatype
  "opsize =
     Op8
   | OpW
   | Op32
   | Op16";;

let primop_INDUCT,primop_RECURSION = define_datatype
  "primop =
     panLang_AddCarry";;

let panLang_prog_INDUCT,panLang_prog_RECURSION = define_datatype
  "panLang_prog =
     panLang_Skip
   | panLang_Dec varname shape ('a panLang_exp) panLang_prog
   | panLang_Assign varkind varname ('a panLang_exp)
     // dest, source
   | panLang_Primitive varname primop (('a panLang_exp) list)
     // Primitives directly target constructs in wordLang.
   | panLang_Store ('a panLang_exp) ('a panLang_exp)
     // dest, source
   | panLang_Store32 ('a panLang_exp) ('a panLang_exp)
     // dest, source
   | panLang_StoreByte ('a panLang_exp) ('a panLang_exp)
     // dest, source
   | panLang_Seq panLang_prog panLang_prog
   | panLang_If ('a panLang_exp) panLang_prog panLang_prog
   | panLang_While ('a panLang_exp) panLang_prog
   | panLang_Break
   | panLang_Continue
   | panLang_Call (((varkind#varname) option#(eid#varname#panLang_prog)
       option) option) funname (('a panLang_exp) list)
   | panLang_DecCall varname shape funname (('a panLang_exp) list)
       panLang_prog
   | panLang_ExtCall funname ('a panLang_exp) ('a panLang_exp) ('a
       panLang_exp) ('a panLang_exp)
     // FFI name, conf_ptr, conf_len, array_ptr, array_len
   | panLang_Raise eid ('a panLang_exp)
   | panLang_Return ('a panLang_exp)
   | panLang_ShMemLoad opsize varkind varname ('a panLang_exp)
   | panLang_ShMemStore opsize ('a panLang_exp) ('a panLang_exp)
   | panLang_Tick
   | panLang_Annot mlstring mlstring";;

let fun_decl_FIELDS = define_record "fun_decl"
  ["name","mlstring";
   "inline","bool";
   "export","bool";
   "params","(mlstring#shape) list";
   "body","'a panLang_prog";
   "return","shape"];;

let decl_INDUCT,decl_RECURSION = define_datatype
  "decl =
     Function ('a fun_decl)
   | Decl shape mlstring ('a panLang_exp)
   | ExnDecl eid shape
   | Name stcname ((fldname#shape) list)";;

let struct_info_FIELDS = define_record "struct_info"
  ["fields","(mlstring#shape) list";
   "size","num"];;

(* HOL4 panLangScript.sml:127: the overload TailCall, which the port
   expands *)
(* HOL4 panLangScript.sml:128: the overload AssignCall, which the
   port expands *)
(* HOL4 panLangScript.sml:129: the overload StandAloneCall, which the
   port expands *)

(* HOL4 panLangScript.sml:131-137: a theorem whose statement the port
   cannot state yet: MEM_IMP_shape_size *)

let is_wf_shape_def,is_wf_shape_ind = define_shaped_rec
  "nested"
  [`is_wf_shape ctxt One = T`;
   `is_wf_shape ctxt (Comb shs) = ALL (is_wf_shape ctxt) shs`;
   `is_wf_shape ctxt (Named nm) =
      (match ALOOKUP ctxt nm with SOME flds -> T | NONE -> F)`];;

let is_wf_flds_def,is_wf_flds_ind = define_rec
  [`is_wf_flds ctxt [] = T`;
   `is_wf_flds ctxt (CONS (fld,sh) flds) =
      (is_wf_shape ctxt sh /\ is_wf_flds ctxt flds)`];;

let is_wf_ctxt_def,is_wf_ctxt_ind = define_rec
  [`is_wf_ctxt [] = T`;
   `is_wf_ctxt (CONS (nm,info) ctxt') = (
      (ALOOKUP ctxt' nm = NONE) /\
      (is_wf_flds ctxt' (struct_info_fields info)) /\
      (is_wf_ctxt ctxt'))`];;

(* For passes with Nameds *)
let size_of_sh_with_ctxt_def,size_of_sh_with_ctxt_ind =
  define_shaped_rec
  "nested"
  [`size_of_sh_with_ctxt ctxt One = 1`;
   `size_of_sh_with_ctxt ctxt (Comb shapes) = SUM (MAP
    (size_of_sh_with_ctxt ctxt) shapes)`;
   `size_of_sh_with_ctxt ctxt (Named name) =
      (match ALOOKUP ctxt name with SOME info ->
          struct_info_size info | NONE -> 1)
    // should not happen`];;

(* For passes after Nameds are compiled away eg pan_to_crep *)
let size_of_shape_def,size_of_shape_ind = define_shaped_rec
  "nested"
  [`size_of_shape One = 1`;
   `size_of_shape (Comb shapes) = SUM (MAP size_of_shape shapes)`;
   `size_of_shape (Named name) = 1
    // should not happen`];;

let _ = size_thms "shape";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let shape_to_str_def,shape_to_str_ind = define_wf
  `MEASURE (\x0. shape_size x0)`
  [`shape_to_str One = implode "1"`;
   `shape_to_str (Comb []) = implode "{}"`;
   `// should never happen
    shape_to_str (Comb (CONS x xs)) =
      mlstring_concat (APPEND (CONS (implode "{") (CONS
          (shape_to_str x)
              (MAP (\x. (\x y. strcat x y) (implode ",") x) (MAP
                  shape_to_str xs))))
              [implode "}"])`;
   `shape_to_str (Named nm) = nm`];;

let shape_val_def,shape_val_ind = define_rec
  [`shape_val One = panLang_Const (n2w 0)`;
   `shape_val (Comb shapes) = panLang_RStruct (shape_vals shapes)`;
   `shape_val (Named nm) = panLang_Const (n2w 0)`;
   `// should never happen
    shape_vals [] = []`;
   `shape_vals (CONS sh shs) = CONS (shape_val sh) (shape_vals shs)`];;

(* HOL4 panLangScript.sml:198-208: a theorem whose statement the port
   cannot state yet: MEM_IMP_exp_size *)


let nested_seq_def,nested_seq_ind = define_rec
  [`nested_seq [] = panLang_Skip`;
   `nested_seq (CONS e es) = panLang_Seq e (nested_seq es)`];;

let with_shape_def,with_shape_ind = define_rec
  [`with_shape [] _1 = []`;
   `with_shape (CONS sh shs) e = CONS (TAKE (size_of_shape sh) e)
    (with_shape shs (DROP (size_of_shape sh) e))`];;

let exp_ids_def,exp_ids_ind = define_shaped_rec
  "match"
  [`exp_ids x1 =
        match x1 with
          panLang_Skip -> ([]:mlstring list)
        | (panLang_Raise e _2) -> [e]
        | (panLang_Dec _3 _4 _5 p) -> exp_ids p
        | (panLang_Seq p q) -> APPEND (exp_ids p) (exp_ids q)
        | (panLang_If _6 p q) -> APPEND (exp_ids p) (exp_ids q)
        | (panLang_While _7 p) -> exp_ids p
        | (panLang_Call (SOME (_8,(SOME (e,_9,ep)))) _10 _11) ->
          CONS e (exp_ids ep)
        | (panLang_DecCall _12 _13 _14 _15 p) -> exp_ids p
        | _16 -> []`];;

let is_decl_def = new_definition
  `is_decl x1 =
      match x1 with
        Decl sh v e -> T
      | _17 -> F`;;

let is_exn_decl_def = new_definition
  `is_exn_decl x1 =
      match x1 with
        ExnDecl eid sh -> T
      | _18 -> F`;;

let is_name_def = new_definition
  `is_name x1 =
      match x1 with
        Name _19 _20 -> T
      | _21 -> F`;;

let size_of_eids_def = new_definition
  `size_of_eids prog = LENGTH (FILTER is_exn_decl prog)`;;

let var_exp_def,var_exp_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`var_exp (panLang_Const w) = ([]:mlstring list)`;
   `var_exp (panLang_Var panLang_Local v) = (([v]):mlstring list)`;
   `var_exp (panLang_Var panLang_Global v) = (([]):mlstring list)`;
   `var_exp (panLang_RStruct es) = ((FLAT (MAP var_exp es)):mlstring
    list)`;
   `var_exp (panLang_RField i e) = ((var_exp e):mlstring list)`;
   `var_exp (panLang_NStruct sn fes) = ((FLAT (MAP var_exp (MAP SND
    fes))):mlstring list)`;
   `var_exp (panLang_NField fld e) = ((var_exp e):mlstring list)`;
   `var_exp (panLang_Load sh e) = ((var_exp e):mlstring list)`;
   `var_exp (panLang_Load32 e) = ((var_exp e):mlstring list)`;
   `var_exp (panLang_LoadByte e) = ((var_exp e):mlstring list)`;
   `var_exp (panLang_Op bop es) = ((FLAT (MAP var_exp es)):mlstring
    list)`;
   `var_exp (panLang_Panop op es) = ((FLAT (MAP var_exp es)):mlstring
    list)`;
   `var_exp (panLang_Cmp c e1 e2) = ((APPEND (var_exp e1) (var_exp
    e2)):mlstring list)`;
   `var_exp (panLang_Shift sh e1 e2) = ((APPEND (var_exp e1) (var_exp
    e2)):mlstring list)`;
   `var_exp panLang_BaseAddr = (([]):mlstring list)`;
   `var_exp panLang_TopAddr = (([]):mlstring list)`;
   `var_exp panLang_BytesInWord = (([]):mlstring list)`];;

let global_var_exp_def,global_var_exp_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`global_var_exp (panLang_Const w) = ([]:mlstring list)`;
   `global_var_exp (panLang_Var panLang_Local v) = (([]):mlstring
    list)`;
   `global_var_exp (panLang_Var panLang_Global v) = (([v]):mlstring
    list)`;
   `global_var_exp (panLang_RStruct es) = ((FLAT (MAP global_var_exp
    es)):mlstring list)`;
   `global_var_exp (panLang_RField i e) = ((global_var_exp
    e):mlstring list)`;
   `global_var_exp (panLang_NStruct sn fes) = ((FLAT (MAP
    (global_var_exp o SND) fes)):mlstring list)`;
   `global_var_exp (panLang_NField fld e) = ((global_var_exp
    e):mlstring list)`;
   `global_var_exp (panLang_Load sh e) = ((global_var_exp e):mlstring
    list)`;
   `global_var_exp (panLang_LoadByte e) = ((global_var_exp
    e):mlstring list)`;
   `global_var_exp (panLang_Op bop es) = ((FLAT (MAP global_var_exp
    es)):mlstring list)`;
   `global_var_exp (panLang_Panop op es) = ((FLAT (MAP global_var_exp
    es)):mlstring list)`;
   `global_var_exp (panLang_Cmp c e1 e2) = ((APPEND (global_var_exp
    e1) (global_var_exp e2)):mlstring list)`;
   `global_var_exp (panLang_Shift sh e1 e2) = ((APPEND
    (global_var_exp e1) (global_var_exp e2)):mlstring list)`];;

let load_op_def = define_cases
  [`load_op Op8 = asm_Load8 /\
   load_op Op16 = asm_Load16 /\
   load_op OpW = panLang_Load /\
   load_op Op32 = panLang_Load32`];;

let store_op_def = define_cases
  [`store_op Op8 = asm_Store8 /\
   store_op Op16 = asm_Store16 /\
   store_op OpW = panLang_Store /\
   store_op Op32 = panLang_Store32`];;

let is_function_def = new_definition
  `is_function x1 =
      match x1 with
        Function _22 -> T
      | _23 -> F`;;

let _ = size_thms "decl";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let functions_def,functions_ind = define_wf
  `MEASURE (\x0. list_size (decl_size (\x. 0)) x0)`
  [`functions [] = []`;
   `functions (CONS (Function fi) fs) = CONS (fun_decl_name
    fi,fun_decl_params fi,fun_decl_body fi,fun_decl_return fi)
    (functions fs)`;
   `functions (CONS (Decl _24 _25 _26) fs) = functions fs`;
   `functions (CONS (ExnDecl _27 _28) fs) = functions fs`;
   `functions (CONS (Name _29 _30) fs) = functions fs`];;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let exceptions_def,exceptions_ind = define_wf
  `MEASURE (\x0. list_size (decl_size (\x. 0)) x0)`
  [`exceptions [] = []`;
   `exceptions (CONS (Function fi) fs) = exceptions fs`;
   `exceptions (CONS (Decl _31 _32 _33) fs) = exceptions fs`;
   `exceptions (CONS (ExnDecl eid sh) fs) = CONS (eid,sh) (exceptions
    fs)`;
   `exceptions (CONS (Name _34 _35) fs) = exceptions fs`];;

let fun_ids_def,fun_ids_ind = define_shaped_rec
  "match"
  [`fun_ids x1 =
        match x1 with
          panLang_Dec _39 _40 _41 p -> fun_ids p
        | (panLang_Seq p q) -> APPEND (fun_ids p) (fun_ids q)
        | (panLang_If _42 p q) -> APPEND (fun_ids p) (fun_ids q)
        | (panLang_While _43 p) -> fun_ids p
        | (panLang_Call (SOME (_44,(SOME (_45,_46,ep)))) nm _47) ->
          CONS nm (fun_ids ep)
        | (panLang_Call _48 nm _49) -> [nm]
        | (panLang_DecCall _50 _51 nm _52 p) -> CONS nm (fun_ids p)
        | _53 -> []`];;

let free_var_ids_def,free_var_ids_ind = define_shaped_rec
  "match"
  [`free_var_ids x1 =
        match x1 with
          panLang_Dec vn sh e p -> APPEND (var_exp e) (FILTER ((\x
            y. ~(x = y)) vn) (free_var_ids p))
        | (panLang_Seq p q) -> APPEND (free_var_ids p) (free_var_ids
          q)
        | (panLang_If g p q) -> APPEND (APPEND (var_exp g)
          (free_var_ids p)) (free_var_ids q)
        | (panLang_While g p) -> APPEND (var_exp g) (free_var_ids p)
        | (panLang_Assign vk v e) ->
      (if vk = panLang_Local then CONS v (var_exp e) else
        var_exp e)
        | (panLang_Primitive v pop es) -> CONS v (FLAT (MAP var_exp
          es))
        | (panLang_Store e1 e2) -> APPEND (var_exp e1) (var_exp e2)
        | (panLang_Store32 e1 e2) -> APPEND (var_exp e1) (var_exp
          e2)
        | (panLang_StoreByte e1 e2) -> APPEND (var_exp e1) (var_exp
          e2)
        | (panLang_Raise eid e) -> var_exp e
        | (panLang_Return e) -> var_exp e
        | (panLang_ExtCall fn e1 e2 e3 e4) -> APPEND (APPEND (APPEND
          (var_exp e1) (var_exp e2)) (var_exp e3)) (var_exp e4)
        | (panLang_ShMemLoad os vk v e) ->
      (if vk = panLang_Local then CONS v (var_exp e) else
        var_exp e)
        | (panLang_ShMemStore os e1 e2) -> APPEND (var_exp e1)
          (var_exp e2)
        | (panLang_Call (SOME (NONE,SOME (_54,vn,ep))) _55 args) ->
          APPEND (CONS vn (free_var_ids ep))
      (FLAT (MAP var_exp args))
        | (panLang_Call (SOME (SOME (vk,vn),SOME (_56,en,ep))) _57
          args) -> APPEND (APPEND (if vk = panLang_Local then [vn] else
          []) (CONS en (free_var_ids ep)))
      (FLAT (MAP var_exp args))
        | (panLang_Call (SOME (SOME (vk,vn),NONE)) _58 args) ->
          APPEND (if vk = panLang_Local then [vn] else [])
      (FLAT (MAP var_exp args))
        | (panLang_Call (SOME (NONE,NONE)) _59 args) ->
      FLAT (MAP var_exp args)
        | (panLang_Call NONE _60 args) -> FLAT (MAP var_exp args)
        | (panLang_DecCall vn _61 _62 args p) -> APPEND (CONS vn
          (free_var_ids p)) (FLAT (MAP var_exp args))
        | _63 -> []`];;

let inlinable_def = new_definition
  `inlinable x1 =
      match x1 with
        Function fi -> fun_decl_inline fi
      | _64 -> F`;;

(* and the interface *)
let _ = unhide_overloads ();;
