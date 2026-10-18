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
needs "compiler/encoders/asm/asm.ml";;
(* HOL4 ancestors outside the port: (* for binop and cmp *) (* for
   overloading the shift operation *) *)


(* for overloading the shift operation *)

new_type_abbrev("panLang_shift",`: ast_shift`);;

new_type_abbrev("stcname",`: mlstring`);;

new_type_abbrev("fldname",`: mlstring`);;

new_type_abbrev("varname",`: mlstring`);;

new_type_abbrev("funname",`: mlstring`);;

new_type_abbrev("eid",`: mlstring`);;

new_type_abbrev("decname",`: mlstring`);;

new_type_abbrev("index",`: num`);;

let shape_INDUCT,shape_RECURSION = define_datatype
  "shape = One | Comb (shape list) | Named (mlstring)";;

let panop_INDUCT,panop_RECURSION = define_datatype
  "panop = panLang_Mul";;
hol4_overload "Mul" "panLang_Mul";;

let varkind_INDUCT,varkind_RECURSION = define_datatype
  "varkind = panLang_Local | panLang_Global";;
hol4_overload "Local" "panLang_Local";;
hol4_overload "Global" "panLang_Global";;

let panLang_exp_INDUCT,panLang_exp_RECURSION = define_datatype
  "panLang_exp = panLang_Const ('a word) | panLang_Var (varkind) \
   (mlstring) | panLang_RStruct (panLang_exp list) | panLang_RField \
   (num) (panLang_exp) | panLang_NStruct (mlstring) \
   ((mlstring#panLang_exp) list) | panLang_NField (mlstring) \
   (panLang_exp) | panLang_Load (shape) (panLang_exp) | \
   panLang_Load32 (panLang_exp) | panLang_LoadByte (panLang_exp) | \
   panLang_Op (binop) (panLang_exp list) | panLang_Panop (panop) \
   (panLang_exp list) | panLang_Cmp (cmp) (panLang_exp) (panLang_exp) \
   | panLang_Shift (ast_shift) (panLang_exp) (panLang_exp) | \
   panLang_BaseAddr | panLang_TopAddr | panLang_BytesInWord";;
hol4_overload "Const" "panLang_Const";;
hol4_overload "Var" "panLang_Var";;
hol4_overload "RStruct" "panLang_RStruct";;
hol4_overload "RField" "panLang_RField";;
hol4_overload "NStruct" "panLang_NStruct";;
hol4_overload "NField" "panLang_NField";;
hol4_overload "Load" "panLang_Load";;
hol4_overload "Load32" "panLang_Load32";;
hol4_overload "LoadByte" "panLang_LoadByte";;
hol4_overload "Op" "panLang_Op";;
hol4_overload "Panop" "panLang_Panop";;
hol4_overload "Cmp" "panLang_Cmp";;
hol4_overload "Shift" "panLang_Shift";;
hol4_overload "BaseAddr" "panLang_BaseAddr";;
hol4_overload "TopAddr" "panLang_TopAddr";;
hol4_overload "BytesInWord" "panLang_BytesInWord";;

let opsize_INDUCT,opsize_RECURSION = define_datatype
  "opsize = Op8 | OpW | Op32 | Op16";;

let primop_INDUCT,primop_RECURSION = define_datatype
  "primop = panLang_AddCarry";;
hol4_overload "AddCarry" "panLang_AddCarry";;

let panLang_prog_INDUCT,panLang_prog_RECURSION = define_datatype
  "panLang_prog = panLang_Skip | panLang_Dec (mlstring) (shape) ('a \
   panLang_exp) (panLang_prog) | panLang_Assign (varkind) (mlstring) \
   ('a panLang_exp) | panLang_Primitive (mlstring) (primop) (('a \
   panLang_exp) list) | panLang_Store ('a panLang_exp) ('a \
   panLang_exp) | panLang_Store32 ('a panLang_exp) ('a panLang_exp) | \
   panLang_StoreByte ('a panLang_exp) ('a panLang_exp) | panLang_Seq \
   (panLang_prog) (panLang_prog) | panLang_If ('a panLang_exp) \
   (panLang_prog) (panLang_prog) | panLang_While ('a panLang_exp) \
   (panLang_prog) | panLang_Break | panLang_Continue | panLang_Call \
   (((varkind#mlstring) option#(mlstring#mlstring#panLang_prog) \
   option) option) (mlstring) (('a panLang_exp) list) | \
   panLang_DecCall (mlstring) (shape) (mlstring) (('a panLang_exp) \
   list) (panLang_prog) | panLang_ExtCall (mlstring) ('a panLang_exp) \
   ('a panLang_exp) ('a panLang_exp) ('a panLang_exp) | panLang_Raise \
   (mlstring) ('a panLang_exp) | panLang_Return ('a panLang_exp) | \
   panLang_ShMemLoad (opsize) (varkind) (mlstring) ('a panLang_exp) | \
   panLang_ShMemStore (opsize) ('a panLang_exp) ('a panLang_exp) | \
   panLang_Tick | panLang_Annot (mlstring) (mlstring)";;
hol4_overload "Skip" "panLang_Skip";;
hol4_overload "Dec" "panLang_Dec";;
hol4_overload "Assign" "panLang_Assign";;
hol4_overload "Primitive" "panLang_Primitive";;
hol4_overload "Store" "panLang_Store";;
hol4_overload "Store32" "panLang_Store32";;
hol4_overload "StoreByte" "panLang_StoreByte";;
hol4_overload "Seq" "panLang_Seq";;
hol4_overload "If" "panLang_If";;
hol4_overload "While" "panLang_While";;
hol4_overload "Break" "panLang_Break";;
hol4_overload "Continue" "panLang_Continue";;
hol4_overload "Call" "panLang_Call";;
hol4_overload "DecCall" "panLang_DecCall";;
hol4_overload "ExtCall" "panLang_ExtCall";;
hol4_overload "Raise" "panLang_Raise";;
hol4_overload "Return" "panLang_Return";;
hol4_overload "ShMemLoad" "panLang_ShMemLoad";;
hol4_overload "ShMemStore" "panLang_ShMemStore";;
hol4_overload "Tick" "panLang_Tick";;
hol4_overload "Annot" "panLang_Annot";;

let fun_decl_FIELDS = define_record "fun_decl"
  ["name","mlstring";
   "inline","bool";
   "export","bool";
   "params","(mlstring#shape) list";
   "body","'a panLang_prog";
   "return","shape"];;

let decl_INDUCT,decl_RECURSION = define_datatype
  "decl = Function ('a fun_decl) | Decl (shape) (mlstring) ('a \
   panLang_exp) | ExnDecl (mlstring) (shape) | Name (mlstring) \
   ((mlstring#shape) list)";;

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

let is_wf_shape_def = cake_define_list
  [`is_wf_shape ctxt One = T`;
   `is_wf_shape ctxt (Comb shs) = EVERY (is_wf_shape ctxt) shs`;
   `is_wf_shape ctxt (Named nm) =
      (match ALOOKUP ctxt nm with SOME flds -> T | NONE -> F)`];;

let is_wf_flds_def = cake_define_list
  [`is_wf_flds ctxt [] = T`;
   `is_wf_flds ctxt ((fld,sh) :: flds) =
      (is_wf_shape ctxt sh /\ is_wf_flds ctxt flds)`];;

let is_wf_ctxt_def = cake_define_list
  [`is_wf_ctxt [] = T`;
   `is_wf_ctxt ((nm,info) :: ctxt') = (
      (ALOOKUP ctxt' nm = NONE) /\
      (is_wf_flds ctxt' (struct_info_fields info)) /\
      (is_wf_ctxt ctxt'))`];;

(* For passes with Nameds *)
let _ = size_thms "struct_info";;
let size_of_sh_with_ctxt_def = cake_define_list
  [`size_of_sh_with_ctxt ctxt One = 1`;
   `size_of_sh_with_ctxt ctxt (Comb shapes) = SUM (MAP
  (size_of_sh_with_ctxt ctxt) shapes)`;
   `size_of_sh_with_ctxt ctxt (Named name) =
      (match ALOOKUP ctxt name with SOME info ->
        struct_info_size info | NONE -> 1)`];;

(* For passes after Nameds are compiled away eg pan_to_crep *)
let size_of_shape_def = cake_define_list
  [`size_of_shape One = 1`;
   `size_of_shape (Comb shapes) = SUM (MAP size_of_shape shapes)`;
   `size_of_shape (Named name) = 1`];;

let shape_to_str_def = cake_define_list
  [`shape_to_str One = implode "1"`;
   `shape_to_str (Comb []) = implode "{}"`;
   `shape_to_str (Comb (x :: xs)) =
      mlstring_concat ((implode "{" :: shape_to_str x ::
              MAP (\x. (\x y. strcat x y) (implode ",") x) (MAP
                shape_to_str xs)) ++
              [implode "}"])`;
   `shape_to_str (Named nm) = nm`];;

let shape_val_def = cake_define_list
  [`shape_val One = Const (n2w 0)`;
   `shape_val (Comb shapes) = panLang_RStruct (shape_vals shapes)`;
   `shape_val (Named nm) = Const (n2w 0)`;
   `shape_vals [] = []`;
   `shape_vals (sh :: shs) = shape_val sh :: shape_vals shs`];;

(* HOL4 panLangScript.sml:198-208: a theorem whose statement the port
   cannot state yet: MEM_IMP_exp_size *)


let nested_seq_def = cake_define_list
  [`nested_seq [] = Skip`;
   `nested_seq (e :: es) = panLang_Seq e (nested_seq es)`];;

let with_shape_def = cake_define_list
  [`with_shape [] _1 = []`;
   `with_shape (sh :: shs) e =
         TAKE (size_of_shape sh) e :: with_shape shs (DROP
           (size_of_shape sh) e)`];;

let exp_ids_def = cake_define
  `exp_ids x1 =
        match x1 with
          panLang_Skip -> ([]:mlstring list)
        | (Raise e _2) -> [e]
        | (panLang_Dec _3 _4 _5 p) -> exp_ids p
        | (panLang_Seq p q) -> exp_ids p ++ exp_ids q
        | (If _6 p q) -> exp_ids p ++ exp_ids q
        | (panLang_While _7 p) -> exp_ids p
        | (Call (SOME (_8,(SOME (e,_9,ep)))) _10 _11) -> e :: exp_ids
          ep
        | (panLang_DecCall _12 _13 _14 _15 p) -> exp_ids p
        | _16 -> []`;;

let is_decl_def = cake_define
  `is_decl x1 =
      match x1 with
        Decl sh v e -> T
      | _17 -> F`;;

let is_exn_decl_def = cake_define
  `is_exn_decl x1 =
      match x1 with
        ExnDecl eid sh -> T
      | _18 -> F`;;

let is_name_def = cake_define
  `is_name x1 =
      match x1 with
        Name _19 _20 -> T
      | _21 -> F`;;

let size_of_eids_def = cake_define
  `size_of_eids prog = LENGTH (FILTER is_exn_decl prog)`;;

let _ = size_thms "panLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 panLangScript.sml:271-276: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let var_exp_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\e. panLang_exp_size ARB e)`)
  CHEAT_TAC
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
   `var_exp (panLang_Cmp c e1 e2) = ((var_exp e1 ++ var_exp
  e2):mlstring list)`;
   `var_exp (panLang_Shift sh e1 e2) = ((var_exp e1 ++ var_exp
  e2):mlstring list)`;
   `var_exp panLang_BaseAddr = (([]):mlstring list)`;
   `var_exp panLang_TopAddr = (([]):mlstring list)`;
   `var_exp panLang_BytesInWord = (([]):mlstring list)`];;

let _ = size_thms "panLang_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 panLangScript.sml:292-298: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let global_var_exp_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\e. panLang_exp_size ARB e)`)
  CHEAT_TAC
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
   `global_var_exp (panLang_Cmp c e1 e2) = ((global_var_exp e1 ++
  global_var_exp e2):mlstring list)`;
   `global_var_exp (panLang_Shift sh e1 e2) = ((global_var_exp e1
  ++ global_var_exp e2):mlstring list)`];;

let load_op_def = cake_define
  `load_op Op8 = asm_Load8 /\
   load_op Op16 = asm_Load16 /\
   load_op OpW = Load /\
   load_op Op32 = Load32`;;

let store_op_def = cake_define
  `store_op Op8 = asm_Store8 /\
   store_op Op16 = asm_Store16 /\
   store_op OpW = Store /\
   store_op Op32 = Store32`;;

let is_function_def = cake_define
  `is_function x1 =
      match x1 with
        Function _22 -> T
      | _23 -> F`;;

let functions_def = cake_define_list
  [`functions [] = []`;
   `functions (Function fi :: fs) =
    (fun_decl_name fi,fun_decl_params fi,fun_decl_body
      fi,fun_decl_return fi) :: functions fs`;
   `functions (Decl _24 _25 _26 :: fs) = functions fs`;
   `functions (ExnDecl _27 _28 :: fs) = functions fs`;
   `functions (Name _29 _30 :: fs) = functions fs`];;

let exceptions_def = cake_define_list
  [`exceptions [] = []`;
   `exceptions (Function fi :: fs) = exceptions fs`;
   `exceptions (Decl _31 _32 _33 :: fs) = exceptions fs`;
   `exceptions (ExnDecl eid sh :: fs) = (eid,sh) :: exceptions fs`;
   `exceptions (Name _34 _35 :: fs) = exceptions fs`];;

let fun_ids_def = cake_define
  `fun_ids x1 =
        match x1 with
          panLang_Dec _39 _40 _41 p -> fun_ids p
        | (panLang_Seq p q) -> fun_ids p ++ fun_ids q
        | (If _42 p q) -> fun_ids p ++ fun_ids q
        | (panLang_While _43 p) -> fun_ids p
        | (Call (SOME (_44,(SOME (_45,_46,ep)))) nm _47) -> nm ::
          fun_ids ep
        | (Call _48 nm _49) -> [nm]
        | (panLang_DecCall _50 _51 nm _52 p) -> nm :: fun_ids p
        | _53 -> []`;;

let free_var_ids_def = cake_define
  `free_var_ids x1 =
        match x1 with
          panLang_Dec vn sh e p -> var_exp e ++ FILTER ((\x y. ~(x =
            y)) vn) (free_var_ids p)
        | (panLang_Seq p q) -> free_var_ids p ++ free_var_ids q
        | (If g p q) -> var_exp g ++ free_var_ids p ++ free_var_ids q
        | (panLang_While g p) -> var_exp g ++ free_var_ids p
        | (panLang_Assign vk v e) ->
      (if vk = panLang_Local then
        v :: var_exp e else
        var_exp e)
        | (panLang_Primitive v pop es) ->
      v :: FLAT (MAP var_exp es)
        | (Store e1 e2) -> var_exp e1 ++ var_exp e2
        | (Store32 e1 e2) -> var_exp e1 ++ var_exp e2
        | (panLang_StoreByte e1 e2) -> var_exp e1 ++ var_exp e2
        | (Raise eid e) -> var_exp e
        | (panLang_Return e) -> var_exp e
        | (panLang_ExtCall fn e1 e2 e3 e4) -> var_exp e1 ++ var_exp
          e2 ++ var_exp e3 ++ var_exp e4
        | (panLang_ShMemLoad os vk v e) ->
      (if vk = panLang_Local then
        v :: var_exp e else
        var_exp e)
        | (panLang_ShMemStore os e1 e2) -> var_exp e1 ++ var_exp e2
        | (panLang_Call (SOME (NONE,SOME (_54,vn,ep))) _55 args) -> (
      vn :: free_var_ids ep) ++
      FLAT (MAP var_exp args)
        | (panLang_Call (SOME (SOME (vk,vn),SOME (_56,en,ep))) _57
          args) ->
      (if vk = panLang_Local then [vn] else []) ++ (
      en :: free_var_ids ep) ++
      FLAT (MAP var_exp args)
        | (panLang_Call (SOME (SOME (vk,vn),NONE)) _58 args) ->
      (if vk = panLang_Local then [vn] else []) ++
      FLAT (MAP var_exp args)
        | (panLang_Call (SOME (NONE,NONE)) _59 args) ->
      FLAT (MAP var_exp args)
        | (panLang_Call NONE _60 args) -> FLAT (MAP var_exp args)
        | (panLang_DecCall vn _61 _62 args p) -> (vn :: free_var_ids
          p) ++ FLAT (MAP var_exp args)
        | _63 -> []`;;

let inlinable_def = cake_define
  `inlinable x1 =
      match x1 with
        Function fi -> fun_decl_inline fi
      | _64 -> F`;;
