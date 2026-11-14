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

new_type_abbrev("pan_shift",`:ast_shift`);;

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
     pan_Mul
     // | Mod
  ";;

let varkind_INDUCT,varkind_RECURSION = define_datatype
  "varkind =
     pan_Local
   | pan_Global";;

let pan_exp_INDUCT,pan_exp_RECURSION = define_datatype
  "pan_exp =
     pan_Const ('a word)
   | pan_Var varkind varname
   | pan_RStruct (pan_exp list)
   | pan_RField index pan_exp
   | pan_NStruct stcname ((fldname#pan_exp) list)
   | pan_NField fldname pan_exp
   | pan_Load shape pan_exp
     // exp: start addr of value with given shape
   | pan_Load32 pan_exp
   | pan_LoadByte pan_exp
   | pan_Op binop (pan_exp list)
   | pan_Panop panop (pan_exp list)
   | pan_Cmp cmp pan_exp pan_exp
   | pan_Shift pan_shift pan_exp pan_exp
   | pan_BaseAddr
   | pan_TopAddr
   | pan_BytesInWord";;

let opsize_INDUCT,opsize_RECURSION = define_datatype
  "opsize =
     Op8
   | OpW
   | Op32
   | Op16";;

let primop_INDUCT,primop_RECURSION = define_datatype
  "primop =
     pan_AddCarry";;

let pan_prog_INDUCT,pan_prog_RECURSION = define_datatype
  "pan_prog =
     pan_Skip
   | pan_Dec varname shape ('a pan_exp) pan_prog
   | pan_Assign varkind varname ('a pan_exp)
     // dest, source
   | pan_Primitive varname primop (('a pan_exp) list)
     // Primitives directly target constructs in wordLang.
   | pan_Store ('a pan_exp) ('a pan_exp)
     // dest, source
   | pan_Store32 ('a pan_exp) ('a pan_exp)
     // dest, source
   | pan_StoreByte ('a pan_exp) ('a pan_exp)
     // dest, source
   | pan_Seq pan_prog pan_prog
   | pan_If ('a pan_exp) pan_prog pan_prog
   | pan_While ('a pan_exp) pan_prog
   | pan_Break
   | pan_Continue
   | pan_Call (((varkind#varname) option#(eid#varname#pan_prog) option) option)
       funname (('a pan_exp) list)
   | pan_DecCall varname shape funname (('a pan_exp) list) pan_prog
   | pan_ExtCall funname ('a pan_exp) ('a pan_exp) ('a pan_exp) ('a pan_exp)
     // FFI name, conf_ptr, conf_len, array_ptr, array_len
   | pan_Raise eid ('a pan_exp)
   | pan_Return ('a pan_exp)
   | pan_ShMemLoad opsize varkind varname ('a pan_exp)
   | pan_ShMemStore opsize ('a pan_exp) ('a pan_exp)
   | pan_Tick
   | pan_Annot mlstring mlstring";;

let fun_decl_FIELDS = define_record "fun_decl"
  ["name","mlstring";
   "inline","bool";
   "export","bool";
   "params","(mlstring#shape) list";
   "body","'a pan_prog";
   "return","shape"];;

let decl_INDUCT,decl_RECURSION = define_datatype
  "decl =
     Function ('a fun_decl)
   | Decl shape mlstring ('a pan_exp)
   | ExnDecl eid shape
   | Name stcname ((fldname#shape) list)";;

let struct_info_FIELDS = define_record "struct_info"
  ["fields","(mlstring#shape) list";
   "size","num"];;

(* HOL4 panLangScript.sml:127: the overload TailCall, which the port expands *)
(* HOL4 panLangScript.sml:128: the overload AssignCall, which the port
   expands *)
(* HOL4 panLangScript.sml:129: the overload StandAloneCall, which the port
   expands *)

let MEM_IMP_shape_size = prove
 (`!shapes a. MEM a shapes ==> (shape_size a < 1 + list_size pan_shape_size
  shapes)`,
  CHEAT_TAC);;

let is_wf_shape_def,is_wf_shape_ind = define_shaped_rec
  "nested"
  `(is_wf_shape ctxt One = T) /\
   (is_wf_shape ctxt (Comb shs) = ALL (is_wf_shape ctxt) shs) /\
   (is_wf_shape ctxt (Named nm) =
      match ALOOKUP ctxt nm with SOME flds -> T
      | NONE -> F)`;;

let is_wf_flds_def,is_wf_flds_ind = define_rec
  `(is_wf_flds ctxt [] = T) /\
   (is_wf_flds ctxt (CONS (fld,sh) flds) =
      (is_wf_shape ctxt sh /\ is_wf_flds ctxt flds))`;;

let is_wf_ctxt_def,is_wf_ctxt_ind = define_rec
  `(is_wf_ctxt [] = T) /\
   (is_wf_ctxt (CONS (nm,info) ctxt') = (
      (ALOOKUP ctxt' nm = NONE) /\
      (is_wf_flds ctxt' (struct_info_fields info)) /\
      (is_wf_ctxt ctxt')))`;;

(* For passes with Nameds *)
let size_of_sh_with_ctxt_def,size_of_sh_with_ctxt_ind = define_shaped_rec
  "nested"
  `(size_of_sh_with_ctxt ctxt One = 1) /\
   (size_of_sh_with_ctxt ctxt (Comb shapes) = SUM (MAP
    (size_of_sh_with_ctxt ctxt) shapes)) /\
   (size_of_sh_with_ctxt ctxt (Named name) =
      match ALOOKUP ctxt name with SOME info -> struct_info_size info
      | NONE -> 1)
   // should not happen`;;

(* For passes after Nameds are compiled away eg pan_to_crep *)
let size_of_shape_def,size_of_shape_ind = define_shaped_rec
  "nested"
  `(size_of_shape One = 1) /\
   (size_of_shape (Comb shapes) = SUM (MAP size_of_shape shapes)) /\
   (size_of_shape (Named name) = 1)
   // should not happen`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let shape_to_str_def,shape_to_str_ind = define_wf
  `MEASURE (\x0. shape_size x0)`
  `(shape_to_str One = implode "1") /\
   (shape_to_str (Comb []) = implode "{}") /\
   // should never happen
   (shape_to_str (Comb (CONS x xs)) =
      mlstring_concat (APPEND (CONS (implode "{") (CONS (shape_to_str x)
              (MAP (\x. strcat (implode ",") x) (MAP shape_to_str xs))))
              [implode "}"])) /\
   (shape_to_str (Named nm) = nm)`;;

let shape_val_def,shape_val_ind = define_rec
  `(shape_val One = pan_Const (n2w 0)) /\
   (shape_val (Comb shapes) = pan_RStruct (shape_vals shapes)) /\
   (shape_val (Named nm) = pan_Const (n2w 0)) /\
   // should never happen
   (shape_vals [] = []) /\
   (shape_vals (CONS sh shs) = CONS (shape_val sh) (shape_vals shs))`;;

let MEM_IMP_exp_size = prove
 (`(!xs a. MEM a xs ==> (pan_exp_size l a < (list_size o pan_exp_size) l xs))
  /\
   (!xs a. MEM a xs ==> (pan_exp_size l (SND a) < (\l. list_size
     (pair_size mlstring_size (pan_exp_size l))) l xs))`,
  CHEAT_TAC);;


let nested_seq_def,nested_seq_ind = define_rec
  `(nested_seq [] = pan_Skip) /\
   (nested_seq (CONS e es) = pan_Seq e (nested_seq es))`;;

let with_shape_def,with_shape_ind = define_rec
  `(with_shape [] _ = []) /\
   (with_shape (CONS sh shs) e = CONS (TAKE (size_of_shape sh) e)
    (with_shape shs (DROP (size_of_shape sh) e)))`;;

let exp_ids_def,exp_ids_ind = define_shaped_rec
  "match"
  `exp_ids x1 =
     match x1 with
       pan_Skip -> ([]:mlstring list)
     | pan_Raise e _ -> [e]
     | pan_Dec _ _ _ p -> exp_ids p
     | pan_Seq p q -> APPEND (exp_ids p) (exp_ids q)
     | pan_If _ p q -> APPEND (exp_ids p) (exp_ids q)
     | pan_While _ p -> exp_ids p
     | pan_Call (SOME (_,(SOME (e,_,ep)))) _ _ -> CONS e (exp_ids ep)
     | pan_DecCall _ _ _ _ p -> exp_ids p
     | _ -> []`;;

let is_decl_def = new_definition
  `is_decl x1' =
   match x1' with
     Decl sh v e -> T
   | _ -> F`;;

let is_exn_decl_def = new_definition
  `is_exn_decl x1'' =
   match x1'' with
     ExnDecl eid sh -> T
   | _ -> F`;;

let is_name_def = new_definition
  `is_name x1''' =
   match x1''' with
     Name _ _ -> T
   | _ -> F`;;

let size_of_eids_def = new_definition
  `size_of_eids prog = LENGTH (FILTER is_exn_decl prog)`;;

(* the clauses in two quotations: fes is ((fldname # exp) list) and
   (_#_)list; sh is shape and shift, which one quotation cannot typecheck *)
let var_exp_def,var_exp_ind = assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(var_exp (pan_Const w) = ([]:mlstring list)) /\
    (var_exp (pan_Var pan_Local v) = (([v]):mlstring list)) /\
    (var_exp (pan_Var pan_Global v) = (([]):mlstring list)) /\
    (var_exp (pan_RStruct es) = ((FLAT (MAP var_exp es)):mlstring list)) /\
    (var_exp (pan_RField i e) = ((var_exp e):mlstring list)) /\
    (var_exp (pan_NStruct sn fes) = ((FLAT (MAP var_exp (MAP SND
    fes))):mlstring list)) /\
    (var_exp (pan_NField fld e) = ((var_exp e):mlstring list)) /\
    (var_exp (pan_Load sh e) = ((var_exp e):mlstring list)) /\
    (var_exp (pan_Load32 e) = ((var_exp e):mlstring list)) /\
    (var_exp (pan_LoadByte e) = ((var_exp e):mlstring list)) /\
    (var_exp (pan_Op bop es) = ((FLAT (MAP var_exp es)):mlstring list)) /\
    (var_exp (pan_Panop op es) = ((FLAT (MAP var_exp es)):mlstring list)) /\
    (var_exp (pan_Cmp c e1 e2) = ((APPEND (var_exp e1) (var_exp
    e2)):mlstring list)) /\
    (var_exp pan_BaseAddr = (([]):mlstring list)) /\
    (var_exp pan_TopAddr = (([]):mlstring list)) /\
    (var_exp pan_BytesInWord = (([]):mlstring list))`;
   `var_exp (pan_Shift sh e1 e2) = ((APPEND (var_exp e1) (var_exp
    e2)):mlstring list)`];;

(* the clauses in two quotations: fes is ((fldname # exp) list) and
   (_#_)list; sh is shape and shift, which one quotation cannot typecheck *)
let global_var_exp_def,global_var_exp_ind = assume_definition_rec_clauses
  "termination (CHEAT_TAC)"
  [`(global_var_exp (pan_Const w) = ([]:mlstring list)) /\
    (global_var_exp (pan_Var pan_Local v) = (([]):mlstring list)) /\
    (global_var_exp (pan_Var pan_Global v) = (([v]):mlstring list)) /\
    (global_var_exp (pan_RStruct es) = ((FLAT (MAP global_var_exp
    es)):mlstring list)) /\
    (global_var_exp (pan_RField i e) = ((global_var_exp e):mlstring list)) /\
    (global_var_exp (pan_NStruct sn fes) = ((FLAT (MAP (global_var_exp o
    SND) fes)):mlstring list)) /\
    (global_var_exp (pan_NField fld e) = ((global_var_exp e):mlstring list)) /\
    (global_var_exp (pan_Load sh e) = ((global_var_exp e):mlstring list)) /\
    (global_var_exp (pan_LoadByte e) = ((global_var_exp e):mlstring list)) /\
    (global_var_exp (pan_Op bop es) = ((FLAT (MAP global_var_exp
    es)):mlstring list)) /\
    (global_var_exp (pan_Panop op es) = ((FLAT (MAP global_var_exp
    es)):mlstring list)) /\
    (global_var_exp (pan_Cmp c e1 e2) = ((APPEND (global_var_exp e1)
    (global_var_exp e2)):mlstring list))`;
   `global_var_exp (pan_Shift sh e1 e2) = ((APPEND (global_var_exp e1)
    (global_var_exp e2)):mlstring list)`];;

let load_op_def = define_cases
  `load_op Op8 = asm_Load8 /\
   load_op Op16 = asm_Load16 /\
   load_op OpW = asm_Load /\
   load_op Op32 = asm_Load32`;;

let store_op_def = define_cases
  `store_op Op8 = asm_Store8 /\
   store_op Op16 = asm_Store16 /\
   store_op OpW = asm_Store /\
   store_op Op32 = asm_Store32`;;

let is_function_def = new_definition
  `is_function x1 =
   match x1 with
     Function _ -> T
   | _ -> F`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let functions_def,functions_ind = define_wf
  `MEASURE (\x0. list_size (decl_size (\x. 0)) x0)`
  `(functions [] = []) /\
   (functions (CONS (Function fi) fs) = CONS (fun_decl_name
    fi,fun_decl_params fi,fun_decl_body fi,fun_decl_return fi) (functions
    fs)) /\
   (functions (CONS (Decl _ _ _) fs) = functions fs) /\
   (functions (CONS (ExnDecl _ _) fs) = functions fs) /\
   (functions (CONS (Name _ _) fs) = functions fs)`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let exceptions_def,exceptions_ind = define_wf
  `MEASURE (\x0. list_size (decl_size (\x. 0)) x0)`
  `(exceptions [] = []) /\
   (exceptions (CONS (Function fi) fs) = exceptions fs) /\
   (exceptions (CONS (Decl _ _ _) fs) = exceptions fs) /\
   (exceptions (CONS (ExnDecl eid sh) fs) = CONS (eid,sh) (exceptions fs)) /\
   (exceptions (CONS (Name _ _) fs) = exceptions fs)`;;

let fun_ids_def,fun_ids_ind = define_shaped_rec
  "match"
  `fun_ids x1 =
     match x1 with
       pan_Dec _ _ _ p -> fun_ids p
     | pan_Seq p q -> APPEND (fun_ids p) (fun_ids q)
     | pan_If _ p q -> APPEND (fun_ids p) (fun_ids q)
     | pan_While _ p -> fun_ids p
     | pan_Call (SOME (_,(SOME (_,_,ep)))) nm _ -> CONS nm (fun_ids ep)
     | pan_Call _ nm _ -> [nm]
     | pan_DecCall _ _ nm _ p -> CONS nm (fun_ids p)
     | _ -> []`;;

let free_var_ids_def,free_var_ids_ind = define_shaped_rec
  "match"
  `free_var_ids x1' =
     match x1' with
       pan_Dec vn sh e p -> APPEND (var_exp e) (FILTER ((\x y. ~(x = y)) vn)
         (free_var_ids p))
     | pan_Seq p q -> APPEND (free_var_ids p) (free_var_ids q)
     | pan_If g p q -> APPEND (APPEND (var_exp g) (free_var_ids p))
       (free_var_ids q)
     | pan_While g p -> APPEND (var_exp g) (free_var_ids p)
     | pan_Assign vk v e ->
      if vk = pan_Local then CONS v (var_exp e)
      else var_exp e
     | pan_Primitive v pop es -> CONS v (FLAT (MAP var_exp es))
     | pan_Store e1 e2 -> APPEND (var_exp e1) (var_exp e2)
     | pan_Store32 e1 e2 -> APPEND (var_exp e1) (var_exp e2)
     | pan_StoreByte e1 e2 -> APPEND (var_exp e1) (var_exp e2)
     | pan_Raise eid e -> var_exp e
     | pan_Return e -> var_exp e
     | pan_ExtCall fn e1 e2 e3 e4 -> APPEND (APPEND (APPEND (var_exp e1)
       (var_exp e2)) (var_exp e3)) (var_exp e4)
     | pan_ShMemLoad os vk v e ->
      if vk = pan_Local then CONS v (var_exp e)
      else var_exp e
     | pan_ShMemStore os e1 e2 -> APPEND (var_exp e1) (var_exp e2)
     | pan_Call (SOME (NONE,SOME (_,vn,ep))) _ args -> APPEND (CONS vn
       (free_var_ids ep))
      (FLAT (MAP var_exp args))
     | pan_Call (SOME (SOME (vk,vn),SOME (_,en,ep))) _ args -> APPEND
       (APPEND (if vk = pan_Local then [vn] else []) (CONS en (free_var_ids
       ep)))
      (FLAT (MAP var_exp args))
     | pan_Call (SOME (SOME (vk,vn),NONE)) _ args -> APPEND (if vk =
       pan_Local then [vn] else [])
      (FLAT (MAP var_exp args))
     | pan_Call (SOME (NONE,NONE)) _ args ->
      FLAT (MAP var_exp args)
     | pan_Call NONE _ args -> FLAT (MAP var_exp args)
     | pan_DecCall vn _ _ args p -> APPEND (CONS vn (free_var_ids p)) (FLAT
       (MAP var_exp args))
     | _ -> []`;;

let inlinable_def = new_definition
  `inlinable x1'' =
   match x1'' with
     Function fi -> fun_decl_inline fi
   | _ -> F`;;

(* and the interface *)
let _ = unhide_overloads ();;
