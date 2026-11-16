(* ======================================================== *)
(*  panStatic: ported from HOL4's
    pancake/panStaticScript.sml
    A definition theory, with 50 definitions, 14 datatypes and no
    theorems.  Needed by compiler.ml.  *)
(* ======================================================== *)

(*
  Static checking for Pancake.

  General checks:
  - Errors:
    - Main function parameters
    - Exported main function
    - Exported function with >4 arguments
    - Missing function exit (return, tail call, etc)
    - Loop exit outside loop (break, continue)
    - Incorrect number of function arguments
    - Incorrect number of Op arguments (impossible from parser)
  - Warnings:
    - Unreachable statements (after function exit, after loop exit)
      - Note: To minimise output, subsequent warnings of this kind after the
        first guaranteed-unreachable line within a block are silenced. If an
        inner block occurs *before* this line, warnings within that block do not
        count towards this first. However, if an inner block occurs *after* this
        line, the line is recognised as the first for the inner block as well
    - Base-calculated address in shared memory operation
    - Non-base -calculated address in local memory operation

  Scope checks:
  - Errors:
    - Undefined/out-of-scope functions
    - Undefined/out-of-scope variables
    - Undefined/out-of-scope struct names
    - Redefined functions
    - Redefined function parameter names
    - Redefined struct names
    - Redefined struct field names
  - Warnings:
    - Redefined variables

  Shape checks:
  - Errors:
    - Mismatched variable declarations
    - Mismatched variable assignments
    - Mismatched function arguments
    - Mismatched function returns
    - Mismatched struct fields
    - Incorrect number of struct field values
    - Mismatched source/destination for memory operations
    - Non-word main function return declarations
    - Non-word FFI arguments
    - Non-word exported argument declarations
    - Non-word exported return declarations
    - Non-word addresses for memory operations
    - Non-word/mismatched operator operands
    - Non-word condition expressions
    - Invalid field index
    - Invalid field name
    - Returned shape size >32 words (TODO: raised shape size)

  Primitive checks:
  - Errors:
    - Mismatched destination shape
    - Incorrect number of arguments
    - Unsupported position
    - Assignment to global value
    - Mismatched operands
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mllist.ml";;
needs "basis/pure/mlmap.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfHeaps.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/errorLogMonad.ml";;
needs "lib/errorMonad.ml";;
needs "lib/machine_ieee.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "pancake/panLang.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "panStatic"
  ["mlint"; "mllist"; "mlmap"; "panLang"];;


(* Error categories for printing *)
let staterr_INDUCT,staterr_RECURSION = define_datatype
  "staterr =
     ScopeErr mlstring
   | WarningErr mlstring
   | GenErr mlstring
   | ShapeErr mlstring";;

(*
  Return type of static_check_* functions:
    (retval, proper error) error # warning list
*)
(* HOL4 panStaticScript.sml:86: the type abbreviation static_result, which
   the port expands *)

(*
  Exp-level state for references to @base
  "Priority": `Based` > `NotTrusted` > `Trusted` > `NotBased`
    where an exp can never have a lower priority state to its components,
    ie. an exp containing a `NotTrusted` exp can never be `Trusted` or `NotBased`
*)
let based_INDUCT,based_RECURSION = define_datatype
  "based =
     Based
   | NotBased
     // warned as appropriate
   | Trusted
     // excempt from warning
   | NotTrusted
     // always warned
  ";;

(* Exp-level state for shape-aware basedness *)
let shaped_based_INDUCT,shaped_based_RECURSION = define_datatype
  "shaped_based =
     WordB based
   | StructB (shaped_based list)
   | NamedB stcname ((fldname#shaped_based) list)";;

(*
  Prog-level state for reachability
  Possible transitions are linear: `IsReach` -> `WarnReach` -> `NotReach`
    where `NotReach` only comes after a reachability warning
*)
let reachable_INDUCT,reachable_RECURSION = define_datatype
  "reachable =
     IsReach
   | NotReach
     // as named
   | WarnReach
     // \"unreachable but has a pending warning\"
  ";;

(* Prog-level state for exit-ness of final statement *)
let last_stmt_INDUCT,last_stmt_RECURSION = define_datatype
  "last_stmt =
     RetLast
   | RaiseLast
   | TailLast
     // function exit
   | BreakLast
   | ContLast
     // loop exit
   | CondExitLast
     // ambiguous exit (after conditionals)
   | InvisLast
   | OtherLast
     // non-exit
  ";;

(* Type for function state *)
let func_info_FIELDS = define_record "func_info"
  ["ret_shape","shape";
   (* shape of return value *)
   "params","(mlstring#shape) list"
   (* parameter info *)
  ];;

(* Type for local var state *)
let local_info_FIELDS = define_record "local_info"
  ["vsh_bd","shaped_based"
   (* shaped basedness of var *)
  ];;

(* Type for global var state *)
let global_info_FIELDS = define_record "global_info"
  ["vshape","shape"
   (* shape of var *)
  ];;

(* Type for error scope *)
let scope_INDUCT,scope_RECURSION = define_datatype
  "scope =
     FunScope pan_funname mlstring
     // in a function, possibly more specific
   | DeclScope pan_varname
     // in a global declaration
   | StcScope stcname fldname
     // in a struct name declaration
   | TopLevel";;

(* Record for current (per-func) context *)
let panStatic_context_FIELDS = define_record "panStatic_context"
  ["locals","(mlstring,local_info)mlmap_map";
   (* tracked var state *)
   "globals","(mlstring,global_info)mlmap_map";
   (* declared globals *)
   "funcs","(mlstring,func_info)mlmap_map";
   (* all function info *)
   "exns","(mlstring,shape)mlmap_map";
   (* all exception decl info*)
   "structs","(mlstring#struct_info) list";
   (* struct name context *)
   "scope","scope";
   (* current scope info *)
   "in_loop","bool";
   (* loop status *)
   "is_reachable","reachable";
   (* reachability *)
   "last","last_stmt";
   (* exit-ness of last statement *)
   "loc","mlstring"
   (* location string *)
  ];;

(* Record for static_check_exp returns *)
let exp_return_FIELDS = define_record "exp_return"
  ["sh_bd","shaped_based"
   (* shaped basedness of exp *)
  ];;

(* Record for static_check_exps returns *)
let exps_return_FIELDS = define_record "exps_return"
  ["sh_bds","shaped_based list"
   (* shaped basedness of exps *)
  ];;

(* Record for static_check_prog returns *)
let prog_return_FIELDS = define_record "prog_return"
  ["exits_fun","bool";
   (* func exit status for all paths *)
   "exits_loop","bool";
   (* loop exit status for all paths *)
   "last","last_stmt";
   (* new exit-ness of last statement *)
   "var_delta","(mlstring,local_info)mlmap_map";
   (* change in var state *)
   "curr_loc","mlstring"
   (* latest location string *)
  ];;

(* Varieties of identifiers that can be out of scope *)
let scoped_id_INDUCT,scoped_id_RECURSION = define_datatype
  "scoped_id =
     panStatic_Var
   | panStatic_Fun
   | panStatic_Stc";;


(* Functions for `based` and `shaped_based` *)

(*
  Builds a shaped based from a given shape and single based
  USED ON PRE-CHECKED SHAPES ONLY (will never be NONE)
 *)
(* the termination relation that HOL4 gives is
     MEASURE LENGTH LEX MEASURE (shape_size o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panStaticScript.sml:227-233: the tactic that proves the termination *)
let sh_bd_from_sh_def,sh_bd_from_sh_ind = define_guess
  `(sh_bd_from_sh sctxt b pan_One = SOME (WordB b)) /\
   (sh_bd_from_sh sctxt b (pan_Comb shs) =
      (match OPT_MMAP (sh_bd_from_sh sctxt b) shs with SOME sbs -> SOME
          (StructB sbs)
      | NONE -> NONE)) /\
   (sh_bd_from_sh sctxt b (pan_Named nm) =
      (match dropWhile (\(n,i). ~(n = nm)) sctxt with CONS (nm,info) sctxt'
          ->
        (let (field_nms,field_shs) = UNZIP (struct_info_fields info) in
        (match OPT_MMAP (sh_bd_from_sh sctxt' b) field_shs with SOME
            field_sbs -> SOME (NamedB nm (ZIP field_nms field_sbs))
        | NONE -> NONE))
      | _ -> NONE))`;;

(* Builds a shaped based with the shape of a given shaped based and single based *)
let sh_bd_from_bd_def,sh_bd_from_bd_ind = define_guess
  `(sh_bd_from_bd b (WordB b') = WordB b) /\
   (sh_bd_from_bd b (StructB sbs) = StructB (MAP (sh_bd_from_bd b) sbs)) /\
   (sh_bd_from_bd b (NamedB nm flds) =
      NamedB nm (MAP (\(nm,sb). (nm,sh_bd_from_bd b sb)) flds))`;;

(* Determine if shaped based has a given shape *)
let sh_bd_has_shape_def,sh_bd_has_shape_ind = define_guess
  `(sh_bd_has_shape sh sb =
        match (sh,sb) with (pan_One,WordB b) -> T
        | (pan_Comb shs,StructB sbs) -> sh_bd_has_shape_list shs sbs
        | (pan_Named nm,NamedB nm' flds) -> nm = nm'
        | _ -> F) /\
   (sh_bd_has_shape_list [] [] = T) /\
   (sh_bd_has_shape_list (CONS sh shs) [] = F) /\
   (sh_bd_has_shape_list [] (CONS sb sbs) = F) /\
   (sh_bd_has_shape_list (CONS sh shs) (CONS sb sbs) =
      (sh_bd_has_shape sh sb /\ sh_bd_has_shape_list shs sbs))`;;

(* Determine if two shaped baseds have the same shape *)
let sh_bd_eq_shapes_def,sh_bd_eq_shapes_ind = define_guess
  `(sh_bd_eq_shapes sb sh =
        match (sb,sh) with (WordB b,WordB b') -> T
        | (StructB sbs,StructB sbs') -> sh_bd_eq_shapes_list sbs sbs'
        | (NamedB nm flds,NamedB nm' flds') -> nm = nm'
        | _ -> F) /\
   (sh_bd_eq_shapes_list [] [] = T) /\
   (sh_bd_eq_shapes_list (CONS sb sbs) [] = F) /\
   (sh_bd_eq_shapes_list [] (CONS sb sbs) = F) /\
   (sh_bd_eq_shapes_list (CONS sb sbs) (CONS sb' sbs') =
      (sh_bd_eq_shapes sb sb' /\ sh_bd_eq_shapes_list sbs sbs'))`;;

(* Lookup shaped basedness at a certain struct index *)
let index_sh_bd_def = define_cases
  `(index_sh_bd i (WordB b) = NONE) /\
   (index_sh_bd i (StructB sbs) = (\l n. oEL n l) sbs i) /\
   (index_sh_bd i (NamedB nm flds) = NONE)`;;

(* Lookup shaped basedness at a certain struct field *)
let field_sh_bd_def = define_cases
  `(field_sh_bd fld (WordB b) = NONE) /\
   (field_sh_bd fld (StructB sbs) = NONE) /\
   (field_sh_bd fld (NamedB nm flds) = ALOOKUP flds fld)`;;

(* Merge basedness according to priority *)
let based_merge_def = new_definition
  `based_merge x y =
     match (x,y) with (Based,_) -> Based
     | (_,Based) -> Based
     | (NotTrusted,_) -> NotTrusted
     | (_,NotTrusted) -> NotTrusted
     | (Trusted,_) -> Trusted
     | (_,Trusted) -> Trusted
     | (NotBased,NotBased) -> NotBased`;;

(* Comparison for combining based-ness between If/While branches *)
let sh_bd_branch_def = new_definition
  `sh_bd_branch x y = if x = y then x else sh_bd_from_bd NotTrusted x`;;

(*
  Combine local var state deltas of If/While branches
    where states are either combined between the two deltas (if in both) or with
    prior context (if in just one)
  Needs extension with extension of `local_info` type
*)
let branch_loc_inf_def = new_definition
  `branch_loc_inf vctxt x y =
     (let x' =
       mlmap_mapWithKey (\k v. local_info_vsh_bd_fupd (K
             (if ~(mlmap_member k y) then
               match mlmap_lookup vctxt k with SOME v' -> sh_bd_branch
                 (local_info_vsh_bd v) (local_info_vsh_bd v')
               | NONE -> sh_bd_from_bd NotTrusted (local_info_vsh_bd v)
             else local_info_vsh_bd v)) v) x in
     let y' =
       mlmap_mapWithKey (\k v. local_info_vsh_bd_fupd (K
             (if ~(mlmap_member k x) then
               match mlmap_lookup vctxt k with SOME v' -> sh_bd_branch
                 (local_info_vsh_bd v) (local_info_vsh_bd v')
               | NONE -> sh_bd_from_bd NotTrusted (local_info_vsh_bd v)
             else local_info_vsh_bd v)) v) y in
     mlmap_unionWith (\vx vy. local_info_vsh_bd_fupd (K (sh_bd_branch
       (local_info_vsh_bd vx) (local_info_vsh_bd vy))) vx) x' y')`;;

(* Combine local var state deltas of Seq progs *)
let seq_loc_inf_def = new_definition
  `seq_loc_inf x y = mlmap_union y x`;;

(* Get shape string from shaped based *)
let sh_bd_to_str_def,sh_bd_to_str_ind = define_guess
  `(sh_bd_to_str (WordB b) = implode "1") /\
   (sh_bd_to_str (StructB []) = implode "{}") /\
   // should never happen
   (sh_bd_to_str (StructB (CONS x xs)) = mlstring_concat (APPEND (CONS
        (implode "{") (CONS (sh_bd_to_str x)
      (MAP (\x. strcat (implode ",") x) (MAP sh_bd_to_str xs))))
      [implode "}"])) /\
   (sh_bd_to_str (NamedB nm flds) = nm)`;;


(* Functions for `last_stmt` and `reachable` *)

(*
  Get string name for statement exit-ness
  USED FOR PRINTING ASSOCIATED WARNINGS ONLY
*)
let last_to_str_def = new_definition
  `last_to_str l =
     match l with RetLast -> (implode "return")
     | RaiseLast -> (implode "raise")
     | TailLast -> (implode "tail call")
     | BreakLast -> (implode "break")
     | ContLast -> (implode "continue")
     | CondExitLast -> (implode "exiting conditional")
     | _ -> (implode "")`;;

(*
  Determine next reachability state for prog sequences based on current state
    and exit-ness
  Handles `IsReach` -> `WarnReach` transition
*)
let next_is_reachable_def = new_definition
  `next_is_reachable r x =
     match r with IsReach -> if ~(x = InvisLast \/ x = OtherLast) then
       WarnReach else IsReach
     | _ -> r`;;

(* Determine whether reachability has decreased *)
let next_now_unreachable_def = new_definition
  `next_now_unreachable r r' = (r = IsReach /\ ~(r' = IsReach))`;;

(*
  Determine whether a prog that can trigger a reachability warning is reached,
    and return last exit-ness and update context if so
  Handles `WarnReach` -> `NotReach` transition
*)
let reached_warnable_def = new_definition
  `reached_warnable s ctxt =
     (match s with pan_Seq prog1 prog2 -> (NONE,ctxt)
     | pan_Tick -> (NONE,ctxt)
     | pan_Annot str1 str2 -> (NONE,ctxt)
     | _ ->
       if panStatic_context_is_reachable ctxt = WarnReach then
         (SOME (panStatic_context_last
           ctxt),panStatic_context_is_reachable_fupd (K NotReach) ctxt)
       else (NONE,ctxt))`;;

(*
  Determine exit-ness of branches, based on whether a definite func or loop exit
    occurred
*)
let branch_last_stmt_def = new_definition
  `branch_last_stmt double_ret double_loop_exit =
     if (double_ret \/ double_loop_exit) then CondExitLast else OtherLast`;;

(* Determine exit-ness of Seq'd progs by ignoring invisible exit-ness *)
let seq_last_stmt_def = new_definition
  `seq_last_stmt x y = if y = InvisLast then x else y`;;


(* Error message helpers *)

(* Get description of current scope *)
let get_scope_desc_def = new_definition
  `get_scope_desc scope =
     match scope with FunScope fname desc ->
       mlstring_concat [implode "function "; fname; desc]
     | DeclScope vname ->
       mlstring_concat [(implode "initialisation of global variable ");
         vname]
     | StcScope sname fld ->
       mlstring_concat [
         implode "declaration of field "; fld;
         implode " in named struct "; sname]
     | TopLevel ->
       (implode "top-level declaration")`;;

(*
  Get message for out of scope identifiers
  id_type :scoped id
*)
let get_scope_msg_def = new_definition
  `get_scope_msg id_type loc id scope =
     let id_desc =
       (match id_type with panStatic_Var -> implode "variable "
       | panStatic_Fun -> implode "function "
       | panStatic_Stc -> implode "struct name ") in
     mlstring_concat [loc; id_desc; id;
       (implode " is not in scope in ");
       get_scope_desc scope; (implode "\n")]`;;

(*
  List of recognised Primitive identifiers for usage hints
*)
let primitive_idents_def = new_definition
  `primitive_idents = [(implode "__add_with_carry__")]`;;

(*
  Adds hint when a primitive is used in an unsupported position
*)
let add_primitive_hint_def = new_definition
  `add_primitive_hint fname msg =
     if MEM fname primitive_idents then mlstring_concat [msg;
            (implode "  note: "); fname;
            (implode " is a built-in primitive only available in ");
            (implode "declaration or assignment RHS positions\n")]
     else msg`;;

(*
  Get message for redefined identifiers
  id_type :scoped id
*)
let get_redec_msg_def = new_definition
  `get_redec_msg id_type loc id scope =
     let id_desc =
       (match id_type with panStatic_Var -> implode "variable "
       | panStatic_Fun -> implode "function "
       | panStatic_Stc -> implode "struct name ") in
     mlstring_concat [
       loc; id_desc; id;
       implode " is redeclared in ";
       get_scope_desc scope; implode "\n"]`;;

(*
  Get message for memory op addresses
  is_local: local vs shared
  is_load: load vs store
  is_untrust: NotTrusted vs other
*)
let get_memop_msg_def = new_definition
  `get_memop_msg is_local' asm_is_load is_untrust loc scope =
     let mem_type = (if is_local' then (implode "local ") else (implode
       "shared ")) in
     let op_type' = (if asm_is_load then (implode "load ") else (implode
       "store ")) in
     let issue =
       (match (is_local',is_untrust) with (F,F) -> (implode "is ")
       | (F,T) -> (implode "may be ")
       | (T,F) -> (implode "is not ")
       | (T,T) -> (implode "may not be ")) in
     mlstring_concat [
       loc; mem_type; op_type';
       (implode "address "); issue; (implode "calculated from base in ");
       get_scope_desc scope; (implode "\n")]`;;

(*
  Get message for op argument number
  is_exact: exactly vs at least
*)
let get_oparg_msg_def = new_definition
  `get_oparg_msg is_exact n_expected n_given loc op scope =
     let issue =
       (if is_exact then implode " only accepts "
       else implode " requires at least ") in
     mlstring_concat [
       loc; implode "operation "; op;
       issue; n_expected; implode " operands, ";
       n_given; implode " provided in ";
       get_scope_desc scope; implode "\n"]`;;

(* Get message for unreachable statement *)
let get_unreach_msg_def = new_definition
  `get_unreach_msg loc last scope = mlstring_concat [
     loc;
     implode "unreachable statement(s) after "; last;
     implode " in ";
     get_scope_desc scope; implode "\n"]`;;

(*
  Get message for rogue loop exit
  is_break: break vs continue
*)
let get_rogue_msg_def = new_definition
  `get_rogue_msg is_break loc scope =
     let stmt = (if is_break then (implode "break ") else (implode
       "continue ")) in
     mlstring_concat [
       loc; stmt;
       implode "statement outside loop in ";
       get_scope_desc scope; implode "\n"]`;;

(* Get message for non-word shape *)
let get_non_word_msg_def = new_definition
  `get_non_word_msg desc sh_str loc scope = mlstring_concat [
     loc; desc; implode " has shape "; sh_str;
     implode " instead of a word in ";
     get_scope_desc scope; implode "\n"]`;;

(* Get message for declared shape mismatch *)
let get_shape_mismatch_msg_def = new_definition
  `get_shape_mismatch_msg desc sh_str_actual sh_str_expect loc scope =
  mlstring_concat [
     loc; desc; implode " has shape "; sh_str_actual;
     implode " instead of declared shape "; sh_str_expect;
     implode " in ";
     get_scope_desc scope; implode "\n"]`;;

let get_implementation_err_msg_def = new_definition
  `get_implementation_err_msg desc loc scope = mlstring_concat [
     loc; desc; implode " in "; get_scope_desc scope; implode "\n";
     implode (APPEND "this should never happen. please report to a compi"
       "ler developer\n")]`;;


(* Misc functions *)

(* Find the first element in a sorted list that is repeated *)
let first_repeat_def,first_repeat_ind = define_guess
  `first_repeat xs =
     match xs with (CONS x1 (CONS x2 xs)) ->
         if x1 = x2 then SOME x1
         else first_repeat (CONS x2 xs)
     | _ -> NONE`;;

(* Get string name for binary ops *)
let binop_to_str_def = new_definition
  `binop_to_str op =
     match op with asm_Add -> (implode "Add")
     | asm_Sub -> (implode "Sub")
     | asm_And -> (implode "And")
     | asm_Or -> (implode "Or")
     | asm_Xor -> (implode "Xor")`;;

(* Get string name for Pancake ops *)
let panop_to_str_def = new_definition
  `panop_to_str op =
     match op with pan_Mul -> (implode "Mul")`;;

(* Get string name for Pancake primitives *)
let primop_to_str_def = new_definition
  `primop_to_str pop =
     match pop with pan_AddCarry -> (implode "AddCarry")`;;


(* Static check helpers *)

(* Check for out of scope func *)
let check_fun_name_def = new_definition
  `check_fun_name ctxt fname =
     (match mlmap_lookup (panStatic_context_funcs ctxt) fname with NONE ->
       errorMonad_error (ScopeErr
         (add_primitive_hint fname (get_scope_msg panStatic_Fun
           (panStatic_context_loc ctxt) fname (panStatic_context_scope ctxt))))
     | SOME f -> errorLogMonad_return f)`;;

(* Check for out of scope global *)
let check_global_var_def = new_definition
  `check_global_var ctxt vname =
     (match mlmap_lookup (panStatic_context_globals ctxt) vname with NONE ->
       errorMonad_error (ScopeErr (get_scope_msg panStatic_Var
       (panStatic_context_loc ctxt) vname (panStatic_context_scope ctxt)))
     | SOME v -> errorLogMonad_return v)`;;

(* Check for out of scope local *)
let check_local_var_def = new_definition
  `check_local_var ctxt vname =
     (match mlmap_lookup (panStatic_context_locals ctxt) vname with NONE ->
       errorMonad_error (ScopeErr (get_scope_msg panStatic_Var
       (panStatic_context_loc ctxt) vname (panStatic_context_scope ctxt)))
     | SOME v -> errorLogMonad_return v)`;;

(* Check for redeclared variable *)
let check_redec_var_def = new_definition
  `check_redec_var ctxt vname =
     (match (mlmap_lookup (panStatic_context_locals ctxt) vname,mlmap_lookup
       (panStatic_context_globals ctxt) vname) with (NONE,NONE) ->
       errorLogMonad_return one
     | _ -> errorLogMonad_log (WarningErr (get_redec_msg panStatic_Var
       (panStatic_context_loc ctxt) vname (panStatic_context_scope ctxt))))`;;

(* Check shapes of exported arguments *)
let check_export_params_def,check_export_params_ind = define_guess
  `(check_export_params loc scope [] = errorLogMonad_return one) /\
   (check_export_params loc scope (CONS (vname,shape) ps) =
      if ~(shape = pan_One) then
        errorMonad_error (ShapeErr (get_non_word_msg (
            mlstring_concat [implode "exported function parameter ";
                vname]) (shape_to_str shape) loc scope))
      else check_export_params loc scope ps)`;;

(* Check operand shape and return merged shaped basedness *)
let check_operands_def,check_operands_ind = define_guess
  `(check_operands ctxt op_str [] = errorLogMonad_return NotBased) /\
   (check_operands ctxt op_str (CONS sb sbs) =
      match sb with WordB b ->
        errorLogMonad_bind (check_operands ctxt op_str sbs) (\b'.
          errorLogMonad_return (based_merge b b'))
      | _ -> errorMonad_error (ShapeErr (get_non_word_msg (
          mlstring_concat [implode "operation "; op_str; implode
              " operand"]) (sh_bd_to_str sb) (panStatic_context_loc ctxt)
              (panStatic_context_scope ctxt))))`;;

(* Check args for primitives and return result shaped basedness *)
let check_primitive_args_def = new_definition
  `check_primitive_args ctxt pan_AddCarry sh_bds =
     errorLogMonad_bind (
       op_str << --(primop_to_str (pan_AddCarry:primop))) (\_.
         errorLogMonad_bind (
       nargs << --(LENGTH sh_bds)) (\_.
       errorLogMonad_bind (if ~(nargs = 3) then errorMonad_error (GenErr
         (get_oparg_msg T (implode "3")
           (num_to_str nargs) (panStatic_context_loc ctxt) op_str
             (panStatic_context_scope ctxt)))
       else errorLogMonad_return one) (\_. errorLogMonad_bind
         (check_operands ctxt op_str sh_bds) (\b.
       errorLogMonad_return (StructB [WordB b; WordB NotBased])))))`;;

(* Check for arg number and shape *)
let check_func_args_def,check_func_args_ind = define_guess
  `check_func_args ctxt fname params' sh_bds =
     (match (params',sh_bds) with (CONS (
         // check declared vs provided
         p,s) ps,CONS sb sbs) ->
       if ~(sh_bd_has_shape s sb) then
         errorMonad_error (ShapeErr (get_shape_mismatch_msg (mlstring_concat
           [
             (implode "value for argument "); p;
             (implode " given to function "); fname]) (sh_bd_to_str sb)
               (shape_to_str s) (panStatic_context_loc ctxt)
               (panStatic_context_scope ctxt)))
       else check_func_args ctxt fname ps sbs
     | (CONS (
         // no more provided args
         p,s) ps,[]) -> errorMonad_error (GenErr (mlstring_concat
           [panStatic_context_loc
         ctxt; implode "argument "; p;
         implode " for call to function "; fname;
         implode " is missing in ";
         get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
     | ([],CONS
            // no more declared params
            sb sbs) -> errorMonad_error (GenErr (mlstring_concat
              [panStatic_context_loc
         ctxt; implode "extra arguments given to function "; fname;
         implode " in ";
         get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
     | ([],[]) ->
                   // checks complete
                   errorLogMonad_return one)`;;

(* Check all fields are given exactly one value and shape *)
let check_struct_fields_def,check_struct_fields_ind = define_guess
  `check_struct_fields ctxt sname fields' fsbs =
     (match (fields',fsbs) with (CONS (
         // check declared vs provided
         fld,sh) fss,fsbs) ->
           errorLogMonad_bind (match FILTER (\(fld',sb). fld = fld') fsbs
             with [(
               // exactly one
               fld,sb)] -> errorLogMonad_return sb
           | [] ->
                   // zero
                   errorMonad_error (ShapeErr (mlstring_concat
                     [panStatic_context_loc
               ctxt; implode "missing field "; fld;
               implode " in named struct "; sname;
               implode " constant in ";
               get_scope_desc (panStatic_context_scope ctxt); implode
                 "\n"]))
           |
             // more than one
             _ -> errorMonad_error (ShapeErr (mlstring_concat
               [panStatic_context_loc
               ctxt; implode "multiple values for field "; fld;
               implode " in named struct "; sname;
               implode " constant in ";
               get_scope_desc (panStatic_context_scope ctxt); implode
                 "\n"]))) (\
         // check number of provided values
         sb.
         // check shape of provided value
         if ~(sh_bd_has_shape sh sb) then
           errorMonad_error (ShapeErr (get_shape_mismatch_msg
             (mlstring_concat [
               implode "value for field "; fld;
               implode " given to named struct "; sname]) (sh_bd_to_str sb)
                 (shape_to_str sh) (panStatic_context_loc ctxt)
                 (panStatic_context_scope ctxt)))
         else check_struct_fields ctxt sname fss (ADELKEY fld fsbs))
     | ([],CONS
            // no more declared fields
            fsb fsbs) -> errorMonad_error (GenErr (mlstring_concat
              [panStatic_context_loc
         ctxt; implode "unexpected field "; FST fsb;
         implode " given to named struct "; sname;
         implode " in ";
         get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
     | ([],[]) ->
                   // checks complete
                   errorLogMonad_return one)`;;

(* Check shape names in scope *)
let check_shape_def,check_shape_ind = define_guess
  `(check_shape sctxt loc scope pan_One = errorLogMonad_return one) /\
   (check_shape sctxt loc scope (pan_Comb shs) =
      check_shapes sctxt loc scope shs) /\
   (check_shape sctxt loc scope (pan_Named nm) =
      (match ALOOKUP sctxt nm with SOME flds -> errorLogMonad_return one
      | NONE -> errorMonad_error (ScopeErr (get_scope_msg panStatic_Stc
          loc nm scope)))) /\
   (check_shapes sctxt loc scope [] = errorLogMonad_return one) /\
   (check_shapes sctxt loc scope (CONS sh shs) =
        errorLogMonad_bind (check_shape sctxt loc scope sh) (\_.
        check_shapes sctxt loc scope shs))`;;

(* Check field/param shape *)
let check_id_shapes_def,check_id_shapes_ind = define_guess
  `(check_id_shapes sctxt loc scope [] =
      errorLogMonad_return one) /\
   (check_id_shapes sctxt loc scope (CONS (id,shape) ids) =
          errorLogMonad_bind (match scope with FunScope fname _ ->
            errorLogMonad_return (FunScope fname (mlstring_concat [implode
                " parameter "; id]))
          | StcScope sname _ ->
            errorLogMonad_return (StcScope sname id)
          |
            // should never occur if static checker implemented correctly
            s -> errorMonad_error (GenErr (get_implementation_err_msg
              (implode "parameter or field found in unexpected scope")
              loc scope))) (\
        // setup specific scope message
        scope'.
        errorLogMonad_bind (check_shape sctxt loc scope' shape) (\_.
        check_id_shapes sctxt loc scope ids)))`;;


(* Main static checking functions *)

(*
  static_check_exp returns:
    (exp info (:exp_return)) static_result
  static_check_exps returns:
    (exps info (:exps_return)) static_result
*)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL x -> pan_exp_size ARB (SND x)
                                   | INR x -> list_size (pan_exp_size ARB) (SND
                                     x))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 panStaticScript.sml:1032-1042: the tactic that proves the
   termination *)
let static_check_exp_def,static_check_exp_ind = define_guess
  `(static_check_exp ctxt (pan_Const num') =
      // return exp info
      errorLogMonad_return (mk_exp_return (WordB NotBased))) /\
   (static_check_exp ctxt (pan_Var pan_Local vname) =
      errorLogMonad_bind (check_local_var ctxt vname) (\
        // check for out of scope var
        vinf.
        // return stored info
        errorLogMonad_return (mk_exp_return (local_info_vsh_bd vinf)))) /\
   (static_check_exp ctxt (pan_Var pan_Global vname) =
      errorLogMonad_bind (check_global_var ctxt vname) (\
        // check for out of scope var
        vinf.
        match sh_bd_from_sh (panStatic_context_structs ctxt) Trusted
            (global_info_vshape vinf) with
          // return exp info with stored shape
          SOME sb -> errorLogMonad_return (mk_exp_return sb)
        |
          // should never occur if static checker implemented correctly
          NONE -> errorMonad_error (ScopeErr (get_implementation_err_msg
          (implode "static analysis failed to convert in-scope shape")
              (panStatic_context_loc
          ctxt) (panStatic_context_scope ctxt))))) /\
   (static_check_exp ctxt (pan_RStruct exps) =
      errorLogMonad_bind (static_check_exps ctxt exps) (\
        // check struct field exps
        esret.
        // return exp info with found shape
        errorLogMonad_return (mk_exp_return (StructB
            (exps_return_sh_bds esret))))) /\
   (static_check_exp ctxt (pan_RField index exp) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check struct exp
        eret.
        match index_sh_bd index (exp_return_sh_bd eret) with NONE ->
            errorMonad_error (ShapeErr (mlstring_concat [panStatic_context_loc
            ctxt; implode "expression shape "; sh_bd_to_str
                (exp_return_sh_bd eret);
            implode " has no field at index "; num_to_str index;
            implode " in "; get_scope_desc (panStatic_context_scope ctxt);
                implode "\n"]))
        |
          // return exp info with found shape
          SOME sb -> errorLogMonad_return (mk_exp_return sb))) /\
   (static_check_exp ctxt (pan_NStruct name eflds) =
          errorLogMonad_bind (match ALOOKUP (panStatic_context_structs
              ctxt) name with SOME info -> errorLogMonad_return info
          | NONE -> errorMonad_error (ScopeErr (get_scope_msg panStatic_Stc
              (panStatic_context_loc ctxt) name (panStatic_context_scope
              ctxt)))) (\sinfo. errorLogMonad_bind (
        (
         // check struct field exps
         field_names,field_exps) << --(UNZIP eflds)) (\_.
             errorLogMonad_bind (static_check_exps ctxt field_exps) (\esret.
             errorLogMonad_bind (
        field_sbs << --(ZIP field_names (exps_return_sh_bds esret))) (\_.
        errorLogMonad_bind (check_struct_fields ctxt name
            (struct_info_fields sinfo) field_sbs) (\_.
        // return exp info with found shape
        errorLogMonad_return (mk_exp_return (NamedB name
            field_sbs)))))))) /\
   (static_check_exp ctxt (pan_NField field' exp) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check struct exp
        eret.
        match field_sh_bd field' (exp_return_sh_bd eret) with NONE ->
            errorMonad_error (ShapeErr (mlstring_concat [panStatic_context_loc
            ctxt; implode "expression shape "; sh_bd_to_str
                (exp_return_sh_bd eret);
            implode " has no field "; field'; implode " in ";
            get_scope_desc (panStatic_context_scope ctxt); implode "\n"]))
        |
          // return exp info with found shape
          SOME sb -> errorLogMonad_return (mk_exp_return sb))) /\
   (static_check_exp ctxt (pan_Load shape addr) =
      errorLogMonad_bind
        // check shape
        (check_shape (panStatic_context_structs ctxt)
            (panStatic_context_loc ctxt) (panStatic_context_scope ctxt) shape)
            (\_. errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check addr exp
        aret. errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotBased ->
          errorLogMonad_log (WarningErr (get_memop_msg T T F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg T T T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_.
        match sh_bd_from_sh (panStatic_context_structs ctxt) Trusted shape
            with
          // return exp info
          SOME sb -> errorLogMonad_return (mk_exp_return sb)
        |
          // should never occur if static checker implemented correctly
          NONE -> errorMonad_error (ScopeErr (get_implementation_err_msg
          (implode "static analysis failed to convert in-scope shape")
              (panStatic_context_loc
          ctxt) (panStatic_context_scope ctxt))))))) /\
   (static_check_exp ctxt (pan_Load32 addr) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check addr exp
        aret. errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotBased ->
          errorLogMonad_log (WarningErr (get_memop_msg T T F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg T T T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_.
        // return exp info
        errorLogMonad_return (mk_exp_return (WordB Trusted))))) /\
   (static_check_exp ctxt (pan_LoadByte addr) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check addr exp
        aret. errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotBased ->
          errorLogMonad_log (WarningErr (get_memop_msg T T F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg T T T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_.
        // return exp info
        errorLogMonad_return (mk_exp_return (WordB Trusted))))) /\
   (static_check_exp ctxt (pan_Op bop exps) =
      errorLogMonad_bind (
        op_str << --(binop_to_str bop)) (\_. errorLogMonad_bind (
        // check num of op args
        nargs << --(LENGTH exps)) (\_.
        errorLogMonad_bind (match bop with asm_Sub ->
          if ~(nargs = 2) then
            errorMonad_error (GenErr (get_oparg_msg T (implode "2")
                (num_to_str nargs) (panStatic_context_loc
              ctxt) op_str (panStatic_context_scope ctxt)))
          else errorLogMonad_return one
        | _ ->
          if nargs < 2 then
            errorMonad_error (GenErr (get_oparg_msg F (implode "2")
                (num_to_str nargs) (panStatic_context_loc
              ctxt) op_str (panStatic_context_scope ctxt)))
          else errorLogMonad_return one) (\_. errorLogMonad_bind
              (static_check_exps ctxt exps) (\
        // check op args
        esret. errorLogMonad_bind (check_operands ctxt op_str
            (exps_return_sh_bds esret)) (\
        // check arg shapes
        b.
        errorLogMonad_return (mk_exp_return (WordB b)))))))) /\
   (static_check_exp ctxt (pan_Panop pop exps) =
      errorLogMonad_bind (
        op_str << --(panop_to_str pop)) (\_. errorLogMonad_bind (
        // check num of op args
        nargs << --(LENGTH exps)) (\_.
        errorLogMonad_bind (match pop with pan_Mul ->
          if ~(nargs = 2) then
            errorMonad_error (GenErr (get_oparg_msg T (implode "2")
                (num_to_str nargs) (panStatic_context_loc
              ctxt) op_str (panStatic_context_scope ctxt)))
          else errorLogMonad_return one) (\_. errorLogMonad_bind
              (static_check_exps ctxt exps) (\
        // check op args
        esret. errorLogMonad_bind (check_operands ctxt op_str
            (exps_return_sh_bds esret)) (\
        // check arg shapes
        b.
        errorLogMonad_return (mk_exp_return (WordB b)))))))) /\
   (static_check_exp ctxt (pan_Cmp cop exp1 exp2) =
      errorLogMonad_bind (static_check_exp ctxt exp1) (\
        // check cmp arg exps
        eret1. errorLogMonad_bind (static_check_exp ctxt exp2) (\eret2.
            errorLogMonad_bind
        // check for shape match
        (if ~(sh_bd_eq_shapes (exp_return_sh_bd eret1) (exp_return_sh_bd
            eret2)) then
          errorMonad_error (ShapeErr (mlstring_concat
              [panStatic_context_loc
              ctxt; implode
                  "comparison given operands of different shapes in ";
              get_scope_desc (panStatic_context_scope ctxt); implode
                  "\n"]))
        else errorLogMonad_return one) (\_.
        // return exp info
        errorLogMonad_return (mk_exp_return (WordB NotBased)))))) /\
   (static_check_exp ctxt (pan_Shift sop exp1 exp2) =
      errorLogMonad_bind (static_check_exp ctxt exp1) (\
        // check shifted exps
        eret1. errorLogMonad_bind (static_check_exp ctxt exp2) (\eret2.
            errorLogMonad_bind
        // check exp shape
        (if ~(sh_bd_has_shape pan_One (exp_return_sh_bd eret1)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "shifted expression")
            (sh_bd_to_str (exp_return_sh_bd eret1)) (panStatic_context_loc
                ctxt) (panStatic_context_scope ctxt)))
        else if ~(sh_bd_has_shape pan_One (exp_return_sh_bd eret2)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "shift expression")
            (sh_bd_to_str (exp_return_sh_bd eret2)) (panStatic_context_loc
                ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return exp info
        errorLogMonad_return eret2)))) /\
   (static_check_exp ctxt pan_BaseAddr =
      // return exp info
      errorLogMonad_return (mk_exp_return (WordB Based))) /\
   (static_check_exp ctxt pan_TopAddr =
      // return exp info
      errorLogMonad_return (mk_exp_return (WordB Based))) /\
   (static_check_exp ctxt BytesInWordB =
      // return exp info
      errorLogMonad_return (mk_exp_return (WordB NotBased))) /\
   (static_check_exps ctxt [] =
      // return exps info
      errorLogMonad_return (mk_exps_return [])) /\
   (static_check_exps ctxt (CONS exp exps) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check exps
        eret. errorLogMonad_bind (static_check_exps ctxt exps) (\esret.
        // return exps info with combined basedness and all shapes
        errorLogMonad_return (mk_exps_return (CONS (exp_return_sh_bd
            eret) (exps_return_sh_bds esret))))))`;;

(*
  static_check_prog returns:
    (prog info (:prog_return)) static_result
*)
let static_check_prog_def,static_check_prog_ind = define_guess
  `(static_check_prog ctxt pan_Skip =
      // return prog info with no checks
      errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
          mlstring_compare) (panStatic_context_loc ctxt))) /\
   (static_check_prog ctxt (pan_Dec vname shape exp prog) =
      errorLogMonad_bind
        // check for redeclaration
        (check_redec_var ctxt vname) (\_. errorLogMonad_bind
        // check shape
        (check_shape (panStatic_context_structs ctxt)
            (panStatic_context_loc ctxt) (panStatic_context_scope ctxt) shape)
            (\_. errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check initialising exp
        eret. errorLogMonad_bind
        // check for shape match
        (if ~(sh_bd_has_shape shape (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
              (mlstring_concat [
              implode "expression to initialise local variable "; vname])
                  (sh_bd_to_str (exp_return_sh_bd eret)) (shape_to_str shape)
                  (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_. errorLogMonad_bind (
        // check prog with declared var
        ctxt' << --(prog_return_last_fupd (K OtherLast)
            (panStatic_context_locals_fupd (K (mlmap_insert
            (panStatic_context_locals ctxt) vname (mk_local_info
            (exp_return_sh_bd eret)))) ctxt))) (\_. errorLogMonad_bind
            (static_check_prog ctxt' prog) (\pret.
        // return prog info without declared var
        errorLogMonad_return (mk_prog_return (prog_return_exits_fun
            pret) (prog_return_exits_loop pret) (prog_return_last pret)
            (mlmap_delete (prog_return_var_delta pret) vname)
            (prog_return_curr_loc pret))))))))) /\
   (static_check_prog ctxt (pan_DecCall vname shape fname args prog) =
      errorLogMonad_bind
        // check for redeclaration
        (check_redec_var ctxt vname) (\_. errorLogMonad_bind
        // check shape
        (check_shape (panStatic_context_structs ctxt)
            (panStatic_context_loc ctxt) (panStatic_context_scope ctxt) shape)
            (\_. errorLogMonad_bind (check_fun_name ctxt fname) (\
        // check func and arg exps
        finf. errorLogMonad_bind (static_check_exps ctxt args) (\esret.
            errorLogMonad_bind
        // check arg num and shapes
        (check_func_args ctxt fname (func_info_params finf)
            (exps_return_sh_bds esret)) (\_. errorLogMonad_bind
        // check for shape match
        (if ~(shape = func_info_ret_shape finf) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
              (mlstring_concat [
              implode "result of function call "; fname;
              implode " to initialise local variable "; vname])
                  (shape_to_str (func_info_ret_shape finf)) (shape_to_str
                  shape) (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
          errorLogMonad_bind (match sh_bd_from_sh
              (panStatic_context_structs ctxt) Trusted shape with
            // return exp info with stored shape
            SOME sb -> errorLogMonad_return sb
          |
            // should never occur if static checker implemented correctly
            NONE -> errorMonad_error (ScopeErr (get_implementation_err_msg
            (implode "static analysis failed to convert in-scope shape")
                (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))) (\
        // check prog with declared var
        sb. errorLogMonad_bind (
        ctxt' << --(prog_return_last_fupd (K OtherLast)
            (panStatic_context_locals_fupd (K (mlmap_insert
            (panStatic_context_locals ctxt) vname (mk_local_info sb))) ctxt)))
            (\_. errorLogMonad_bind (static_check_prog ctxt' prog) (\pret.
        // return prog info without declared var
        errorLogMonad_return (mk_prog_return (prog_return_exits_fun
            pret) (prog_return_exits_loop pret) (prog_return_last pret)
            (mlmap_delete (prog_return_var_delta pret) vname)
            (prog_return_curr_loc pret)))))))))))) /\
   (static_check_prog ctxt (pan_Assign pan_Local vname exp) =
      errorLogMonad_bind (check_local_var ctxt vname) (\
        // check for out of scope assignment
        vinf. errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check assigning exp
        eret. errorLogMonad_bind
        // check for shape match
        (if ~(sh_bd_eq_shapes (local_info_vsh_bd vinf) (exp_return_sh_bd
            eret)) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
              (mlstring_concat [
              implode "expression assigned to local variable "; vname])
                  (sh_bd_to_str (exp_return_sh_bd eret)) (sh_bd_to_str
                  (local_info_vsh_bd vinf)) (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info with updated var
        errorLogMonad_return (mk_prog_return F F OtherLast
            (mlmap_singleton mlstring_compare vname
                (local_info_vsh_bd_fupd (K (exp_return_sh_bd eret)) vinf))
                (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt (pan_Assign pan_Global vname exp) =
      errorLogMonad_bind (check_global_var ctxt vname) (\
        // check for out of scope assignment
        vinf. errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check assigning exp
        eret. errorLogMonad_bind
        // check for shape match
        (if ~(sh_bd_has_shape (global_info_vshape vinf) (exp_return_sh_bd
            eret)) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
              (mlstring_concat [
              implode "expression assigned to global variable "; vname])
                  (sh_bd_to_str (exp_return_sh_bd eret)) (shape_to_str
                  (global_info_vshape vinf)) (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info with updated var
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt ((\s h. asm_Call (SOME (SOME s,h)))
    (pan_Local,vname) hdl fname args) =
    errorLogMonad_bind (check_local_var ctxt vname) (\
    // check for out of scope assignment
    vinf. errorLogMonad_bind (check_fun_name ctxt fname) (\
    // check func ptr exp and arg exps
    finf. errorLogMonad_bind (static_check_exps ctxt args) (\esret.
        errorLogMonad_bind
    // check arg num and shapes
    (check_func_args ctxt fname (func_info_params finf) (exps_return_sh_bds
        esret)) (\_. errorLogMonad_bind
    // check for shape match
    (if ~(sh_bd_has_shape (func_info_ret_shape finf) (local_info_vsh_bd
        vinf)) then
      errorMonad_error (ShapeErr (get_shape_mismatch_msg (mlstring_concat [
          implode "result of function call "; fname;
          implode " assigned to local variable "; vname]) (shape_to_str
              (func_info_ret_shape finf)) (sh_bd_to_str (local_info_vsh_bd
              vinf)) (panStatic_context_loc
        ctxt) (panStatic_context_scope ctxt)))
    else errorLogMonad_return one) (\_. errorLogMonad_bind
    // check exception handling info
    (match hdl with NONE -> errorLogMonad_return one
    |
      // check for out of scope exception variable
      SOME (eid,evar,prog) ->
        errorLogMonad_bind (match mlmap_lookup (panStatic_context_exns
            ctxt) eid with
                  NONE -> errorMonad_error (ScopeErr (mlstring_concat [
                            implode "exception "; eid; implode
                                " is not declared\n"]))
                | SOME sh -> errorLogMonad_return sh) (\
          // check exception declared
          sh. errorLogMonad_bind (check_local_var ctxt evar) (\
          // check handler variable exists
          evinf. errorLogMonad_bind
          // check handler variable shape matches exception shape
          (if ~(sh_bd_has_shape sh (local_info_vsh_bd evinf)) then
            errorMonad_error (ShapeErr (mlstring_concat [
              implode "handler variable "; evar;
              implode " does not match shape of exception "; eid; implode
                  "\n"]))
          else errorLogMonad_return one) (\_.
            errorLogMonad_bind (match sh_bd_from_sh
                (panStatic_context_structs ctxt) Trusted sh with
              // return exp info with stored shape
              SOME sb -> errorLogMonad_return sb
            |
              // should never occur if static checker implemented correctly
              NONE -> errorMonad_error (ScopeErr
                  (get_implementation_err_msg
              (implode "static analysis failed to convert in-scope shape")
                  (panStatic_context_loc
              ctxt) (panStatic_context_scope ctxt)))) (\sb.
                  errorLogMonad_bind
          // type-check handler body
          (static_check_prog
            (panStatic_context_locals_fupd (K
              (mlmap_insert (panStatic_context_locals ctxt) evar
                (local_info_vsh_bd_fupd (K sb) evinf))) ctxt)
            prog) (\_.
          errorLogMonad_return one)))))) (\_.
    // return prog info with updated var
    errorLogMonad_return (mk_prog_return F F OtherLast
        (mlmap_singleton mlstring_compare vname (local_info_vsh_bd_fupd
            (K (sh_bd_from_bd Trusted (local_info_vsh_bd vinf))) vinf))
            (panStatic_context_loc ctxt))))))))) /\
   (static_check_prog ctxt ((\s h. asm_Call (SOME (SOME s,h)))
    (pan_Global,vname) hdl fname args) =
      errorLogMonad_bind (check_global_var ctxt vname) (\
        // check for out of scope assignment
        vinf. errorLogMonad_bind (check_fun_name ctxt fname) (\
        // check func ptr exp and arg exps
        finf. errorLogMonad_bind (static_check_exps ctxt args) (\esret.
            errorLogMonad_bind
        // check arg num and shapes
        (check_func_args ctxt fname (func_info_params finf)
            (exps_return_sh_bds esret)) (\_. errorLogMonad_bind
        // check for shape match
        (if ~(global_info_vshape vinf = func_info_ret_shape finf) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
              (mlstring_concat [
              implode "result of function call "; fname;
              implode " assigned to global variable "; vname])
                  (shape_to_str (func_info_ret_shape finf)) (shape_to_str
                  (global_info_vshape vinf)) (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_. errorLogMonad_bind
        // check exception handling info
        (match hdl with NONE -> errorLogMonad_return one
        |
          // check for out of scope exception variable
          SOME (eid,evar,prog) ->
            errorLogMonad_bind (check_local_var ctxt evar) (\evinf.
              errorLogMonad_bind (static_check_prog
                  (panStatic_context_locals_fupd (K
                  (mlmap_insert (panStatic_context_locals ctxt) evar
                      (local_info_vsh_bd_fupd (K (sh_bd_from_bd Trusted
                      (local_info_vsh_bd evinf))) evinf))) ctxt) prog) (\_.
              errorLogMonad_return one))) (\_.
        // return prog info with updated var
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt))))))))) /\
   (static_check_prog ctxt (pan_Primitive vname pop es) =
      errorLogMonad_bind (check_local_var ctxt vname) (\
        // check destination is in scope (Primitive always targets Local)
        vinf. errorLogMonad_bind (static_check_exps ctxt es) (\
        // check arg exps
        esret. errorLogMonad_bind (check_primitive_args ctxt pop
            (exps_return_sh_bds esret)) (\
        // per-primop arity/operand checks; returns result shaped basedness
        res_sb. errorLogMonad_bind
        // check declared destination shape matches result shape
        (if ~(sh_bd_eq_shapes (local_info_vsh_bd vinf) res_sb) then
            errorMonad_error (ShapeErr (get_shape_mismatch_msg (mlstring_concat
            [
              (implode "result of primitive "); primop_to_str pop;
              (implode " assigned to local variable "); vname])
                  (sh_bd_to_str res_sb) (sh_bd_to_str (local_info_vsh_bd vinf))
                  (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info with updated var
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_singleton
            mlstring_compare vname
                              (local_info_vsh_bd_fupd (K res_sb) vinf))
                                  (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (pan_Return exp) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check return value exp
        eret.
          errorLogMonad_bind (match panStatic_context_scope ctxt with
              FunScope fname _ -> check_fun_name ctxt fname
          |
            // should never occur if static checker implemented correctly
            _ -> errorMonad_error (GenErr (get_implementation_err_msg
            (implode "return found outside function scope")
                (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))) (\
        // lookup current function info
        finf. errorLogMonad_bind
        // check for shape match
        (if ~(sh_bd_has_shape (func_info_ret_shape finf) (exp_return_sh_bd
            eret)) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
            (implode "expression to return")
            (sh_bd_to_str (exp_return_sh_bd eret)) (shape_to_str
                (func_info_ret_shape finf)) (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return T F RetLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt ((asm_Call NONE) fname args) =
      errorLogMonad_bind (match panStatic_context_scope ctxt with FunScope
          caller _ -> check_fun_name ctxt caller
          |
            // should never occur if static checker implemented correctly
            _ -> errorMonad_error (GenErr (implode
                "tail call found outside function scope"))) (\
        // lookup current function info
        caller_inf. errorLogMonad_bind (check_fun_name ctxt fname) (\
        // check func ptr exp and arg exps
        callee_inf. errorLogMonad_bind (static_check_exps ctxt args)
            (\esret. errorLogMonad_bind
        // check for shape match
        (if ~(func_info_ret_shape caller_inf = func_info_ret_shape
            callee_inf) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
              (mlstring_concat [
              implode "result of function call "; fname;
              implode " to return"]) (shape_to_str (func_info_ret_shape
                  callee_inf))
            (shape_to_str (func_info_ret_shape caller_inf))
                (panStatic_context_loc
            ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_. errorLogMonad_bind
        // check arg num and shapes
        (check_func_args ctxt fname (func_info_params callee_inf)
            (exps_return_sh_bds esret)) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return T F TailLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt)))))))) /\
   (static_check_prog ctxt ((\h. asm_Call (SOME (NONE,h))) hdl fname args) =
      errorLogMonad_bind (check_fun_name ctxt fname) (\
        // check func ptr exp and arg exps
        finf. errorLogMonad_bind (static_check_exps ctxt args) (\esret.
            errorLogMonad_bind
        // check arg num and shapes
        (check_func_args ctxt fname (func_info_params finf)
            (exps_return_sh_bds esret)) (\_. errorLogMonad_bind
        // check exception handling info
        (match hdl with NONE -> errorLogMonad_return one
        |
          // check for out of scope exception variable
          SOME (eid,evar,prog) ->
            errorLogMonad_bind (match mlmap_lookup (panStatic_context_exns
                ctxt) eid with
                      NONE -> errorMonad_error (ScopeErr (mlstring_concat [
                              implode "exception "; eid; implode
                                  " is not declared\n"]))
                    | SOME sh -> errorLogMonad_return sh) (\
              // check exception declared
              sh. errorLogMonad_bind (check_local_var ctxt evar) (\
              // check handler variable exists
              evinf. errorLogMonad_bind
              // check handler variable shape matches exception shape
              (if ~(sh_bd_has_shape sh (local_info_vsh_bd evinf)) then
                errorMonad_error (ShapeErr (mlstring_concat [
                  implode "handler variable "; evar;
                  implode " does not match shape of exception "; eid;
                      implode "\n"]))
              else errorLogMonad_return one) (\_.
                errorLogMonad_bind (match sh_bd_from_sh
                    (panStatic_context_structs ctxt) Trusted sh with
                  // return exp info with stored shape
                  SOME sb -> errorLogMonad_return sb
                |
                  // should never occur if static checker implemented correctly
                  NONE -> errorMonad_error (ScopeErr
                      (get_implementation_err_msg
                  (implode
                      "static analysis failed to convert in-scope shape")
                      (panStatic_context_loc
                  ctxt) (panStatic_context_scope ctxt)))) (\sb.
                      errorLogMonad_bind
              // type-check handler body
              (static_check_prog
                (panStatic_context_locals_fupd (K
                  (mlmap_insert (panStatic_context_locals ctxt) evar
                    (local_info_vsh_bd_fupd (K sb) evinf))) ctxt)
                prog) (\_.
              errorLogMonad_return one)))))) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (pan_ExtCall fname ptr1 len1 ptr2 len2) =
      errorLogMonad_bind (static_check_exps ctxt [ptr1; len1; ptr2; len2])
          (\
        // check arg exps
        esret. errorLogMonad_bind
        // check arg shapes
        (match FIND (\sb. ~(sh_bd_has_shape pan_One sb))
            (exps_return_sh_bds esret) with SOME sb -> errorMonad_error
            (ShapeErr (get_non_word_msg (mlstring_concat [
            implode "value for argument given to FFI "; fname])
                (sh_bd_to_str sb) (panStatic_context_loc ctxt)
                (panStatic_context_scope ctxt)))
        | NONE -> errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt))))) /\
   (static_check_prog ctxt (pan_Seq prog1 prog2) =
      errorLogMonad_bind (
        (
         // check for prior warnable unreachability
         warn_p1,ctxt1) << --(reached_warnable prog1 ctxt)) (\_.
        errorLogMonad_bind (match warn_p1 with SOME ls ->
          errorLogMonad_log (WarningErr (get_unreach_msg
              (panStatic_context_loc ctxt1) (last_to_str ls)
              (panStatic_context_scope ctxt1)))
        | NONE -> errorLogMonad_return one) (\_. errorLogMonad_bind
            (static_check_prog ctxt1 prog1) (\
        // check first prog
        pret1. errorLogMonad_bind (
        // update unreachability after first prog
        next_r << --(next_is_reachable (panStatic_context_is_reachable
            ctxt1) (prog_return_last pret1))) (\_. errorLogMonad_bind (
        ctxt2 << --(panStatic_context_loc_fupd (K (prog_return_curr_loc
            pret1)) (prog_return_last_fupd (K
            (if next_now_unreachable (panStatic_context_is_reachable ctxt1)
                next_r then prog_return_last pret1
            else prog_return_last ctxt1))
                (panStatic_context_is_reachable_fupd (K next_r)
                (panStatic_context_locals_fupd (K (seq_loc_inf
                (panStatic_context_locals ctxt1) (prog_return_var_delta
                pret1))) ctxt1))))) (\_. errorLogMonad_bind (
        (
         // check for warnable unreachability after first prog
         warn_p2,ctxt3) << --(reached_warnable prog2 ctxt2)) (\_.
        errorLogMonad_bind (match warn_p2 with SOME ls ->
          errorLogMonad_log (WarningErr (get_unreach_msg
              (panStatic_context_loc ctxt3) (last_to_str ls)
              (panStatic_context_scope ctxt1)))
        | NONE -> errorLogMonad_return one) (\_. errorLogMonad_bind
            (static_check_prog ctxt3 prog2) (\
        // check second prog
        pret2.
        // return prog info by combining both appropriately
        errorLogMonad_return (mk_prog_return (prog_return_exits_fun
            pret1 \/ prog_return_exits_fun pret2) (prog_return_exits_loop
            pret1 \/ prog_return_exits_loop pret2) (seq_last_stmt
            (prog_return_last pret1) (prog_return_last pret2)) (seq_loc_inf
            (prog_return_var_delta pret1) (prog_return_var_delta pret2))
            (prog_return_curr_loc pret2))))))))))) /\
   (static_check_prog ctxt (pan_If exp prog1 prog2) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check condition exp
        eret. errorLogMonad_bind
        // check condition shape
        (if ~(sh_bd_has_shape pan_One (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "if condition") (sh_bd_to_str (exp_return_sh_bd eret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_. errorLogMonad_bind
            (static_check_prog ctxt prog1) (\
        // check branches
        pret1. errorLogMonad_bind (static_check_prog
            (panStatic_context_loc_fupd (K (prog_return_curr_loc pret1)) ctxt)
            prog2) (\pret2. errorLogMonad_bind (
        // return prog info by combining both appropriately
        double_ret << --(prog_return_exits_fun pret1
            /\ prog_return_exits_fun pret2)) (\_. errorLogMonad_bind (
        double_loop_exit << --(prog_return_exits_loop pret1
            /\ prog_return_exits_loop pret2)) (\_.
        errorLogMonad_return (mk_prog_return double_ret
            double_loop_exit (branch_last_stmt double_ret double_loop_exit)
            (branch_loc_inf (panStatic_context_locals ctxt)
            (prog_return_var_delta pret1) (prog_return_var_delta pret2))
            (prog_return_curr_loc pret2))))))))) /\
   (static_check_prog ctxt (pan_While exp prog) =
      errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check condition exp
        eret. errorLogMonad_bind
        // check condition shape
        (if ~(sh_bd_has_shape pan_One (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "while condition") (sh_bd_to_str (exp_return_sh_bd
                eret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        else errorLogMonad_return one) (\_. errorLogMonad_bind
            (static_check_prog (panStatic_context_in_loop_fupd (K T) ctxt)
            prog) (\
        // check loop body
        pret.
        // return prog info by treating like an else-less If
        errorLogMonad_return (mk_prog_return F F OtherLast (
              branch_loc_inf (panStatic_context_locals ctxt)
                  (prog_return_var_delta pret) (mlmap_empty
                  mlstring_compare)) (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt pan_Break =
      errorLogMonad_bind
        // check for rogueness
        (if ~(panStatic_context_in_loop ctxt) then
          errorMonad_error (GenErr (get_rogue_msg T (panStatic_context_loc
              ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F T BreakLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt)))) /\
   (static_check_prog ctxt pan_Continue =
      errorLogMonad_bind
        // check for rogueness
        (if ~(panStatic_context_in_loop ctxt) then
          errorMonad_error (GenErr (get_rogue_msg F (panStatic_context_loc
              ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F T ContLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt)))) /\
   (static_check_prog ctxt (pan_Raise eid exp) =
      errorLogMonad_bind (match mlmap_lookup (panStatic_context_exns ctxt)
          eid with
                NONE -> errorMonad_error (ScopeErr (mlstring_concat [
                          implode "exception "; eid; implode
                              " is not declared\n"]))
              | SOME sh -> errorLogMonad_return sh) (\
        // check exception declared
        sh. errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check exception value expression
        eret. errorLogMonad_bind
        // check shape match
        (if ~(sh_bd_has_shape sh (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (mlstring_concat [
            implode "raised exception "; eid;
            implode " has wrong value shape\n"]))
        else errorLogMonad_return one) (\_.
        errorLogMonad_return (mk_prog_return T F RaiseLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt (pan_Store addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check address and value exps
        aret. errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
            errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | WordB NotBased ->
          errorLogMonad_log (WarningErr (get_memop_msg T F F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg T F T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt)))))) /\
   (static_check_prog ctxt (pan_Store32 addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check address and value exps
        aret. errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
            errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | WordB NotBased ->
          errorLogMonad_log (WarningErr (get_memop_msg T F F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg T F T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_. errorLogMonad_bind
        // check value shape
        (if ~(sh_bd_has_shape pan_One (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store value") (sh_bd_to_str (exp_return_sh_bd eret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (pan_StoreByte addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check address and value exps
        aret. errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
            errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | WordB NotBased ->
          errorLogMonad_log (WarningErr (get_memop_msg T F F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg T F T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_. errorLogMonad_bind
        // check value shape
        (if ~(sh_bd_has_shape pan_One (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store value") (sh_bd_to_str (exp_return_sh_bd eret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (pan_ShMemLoad mop pan_Local vname addr) =
      errorLogMonad_bind (check_local_var ctxt vname) (\
        // check for out of scope var
        vinf. errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check address exp
        aret. errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB Based ->
          errorLogMonad_log (WarningErr (get_memop_msg F T F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg F T T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_. errorLogMonad_bind
        // check value shape
        (if ~(sh_bd_has_shape pan_One (local_info_vsh_bd vinf)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load variable") (sh_bd_to_str (local_info_vsh_bd
                vinf)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info with updated var
        errorLogMonad_return (mk_prog_return F F OtherLast
            (mlmap_singleton mlstring_compare vname
                (local_info_vsh_bd_fupd (K (sh_bd_from_bd Trusted
                (local_info_vsh_bd vinf))) vinf)) (panStatic_context_loc
                ctxt))))))) /\
   (static_check_prog ctxt (pan_ShMemLoad mop pan_Global vname addr) =
      errorLogMonad_bind (check_global_var ctxt vname) (\
        // check for out of scope var
        vinf. errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check address exp
        aret. errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load address") (sh_bd_to_str (exp_return_sh_bd aret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB Based ->
          errorLogMonad_log (WarningErr (get_memop_msg F T F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg F T T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_. errorLogMonad_bind
        // check value shape
        (if ~(pan_One = global_info_vshape vinf) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "load variable") (shape_to_str (global_info_vshape
                vinf)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info with updated var
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt (pan_ShMemStore mop addr exp) =
      errorLogMonad_bind (static_check_exp ctxt addr) (\
        // check address and value exps
        aret. errorLogMonad_bind (static_check_exp ctxt exp) (\eret.
            errorLogMonad_bind
        // check address shape and references base
        (match exp_return_sh_bd aret with StructB _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | NamedB _ _ ->
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store address") (sh_bd_to_str (exp_return_sh_bd
                aret)) (panStatic_context_loc ctxt) (panStatic_context_scope
                ctxt)))
        | WordB Based ->
          errorLogMonad_log (WarningErr (get_memop_msg F F F
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | WordB NotTrusted ->
          errorLogMonad_log (WarningErr (get_memop_msg F F T
              (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        | _ -> errorLogMonad_return one) (\_. errorLogMonad_bind
        // check value shape
        (if ~(sh_bd_has_shape pan_One (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (get_non_word_msg
            (implode "store value") (sh_bd_to_str (exp_return_sh_bd eret))
                (panStatic_context_loc ctxt) (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // return prog info
        errorLogMonad_return (mk_prog_return F F OtherLast (mlmap_empty
            mlstring_compare) (panStatic_context_loc ctxt))))))) /\
   (static_check_prog ctxt pan_Tick =
      // return prog info with no checks
      errorLogMonad_return (mk_prog_return F F InvisLast (mlmap_empty
          mlstring_compare) (panStatic_context_loc ctxt))) /\
   (static_check_prog ctxt (pan_Annot tag str) =
      // update current location
      let loc =
        (if (tag = (implode "location")) then
          mlstring_concat [implode "AT "; str; implode ": "]
        else panStatic_context_loc ctxt) in
      // return prog info with no checks
      errorLogMonad_return (mk_prog_return F F InvisLast (mlmap_empty
          mlstring_compare) loc))`;;

(*
  static_check_progs returns:
    (unit) static_result
*)
let static_check_progs_def,static_check_progs_ind = define_guess
  `(static_check_progs fctxt gctxt sctxt ectxt [] =
      // no more decls
      errorLogMonad_return one) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (Name _ _) decls) =
      // not a function
      static_check_progs fctxt gctxt sctxt ectxt decls) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (ExnDecl _ _) decls) =
      // not a function
      static_check_progs fctxt gctxt sctxt ectxt decls) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (Decl _ _ _) decls) =
      // not a function
      static_check_progs fctxt gctxt sctxt ectxt decls) /\
   (static_check_progs fctxt gctxt sctxt ectxt (CONS (Function fi) decls) =
      errorLogMonad_bind (
        (param_names,param_shapes) << --(UNZIP (func_info_params fi))) (\_.
          errorLogMonad_bind (match OPT_MMAP (sh_bd_from_sh sctxt Trusted)
              param_shapes with
            // return exp info with stored shape
            SOME sbs -> errorLogMonad_return (ZIP param_names sbs)
          |
            // should never occur if static checker implemented correctly
            NONE -> errorMonad_error (ScopeErr (get_implementation_err_msg
            (implode "static analysis failed to convert in-scope shape")
            (implode "") (FunScope (fun_decl_name fi) (implode "")))))
                (\param_sbs. errorLogMonad_bind (
        // setup initial checking context
        ctxt << --(mk_panStatic_context
                    (FOLDL (\m (v,sb). mlmap_insert m v (mk_local_info sb))
                      (mlmap_empty mlstring_compare) param_sbs) gctxt fctxt
                          ectxt sctxt (FunScope (fun_decl_name fi) (implode
                          "")) F IsReach InvisLast (implode ""))) (\_.
                          errorLogMonad_bind (static_check_prog ctxt
                          (fun_decl_body fi)) (\
        // check function body
        prog_ret. errorLogMonad_bind
        // check missing function exit
        (if ~(prog_return_exits_fun prog_ret) then
          errorMonad_error (GenErr (mlstring_concat [
              implode "branches missing return statement in ";
              get_scope_desc (FunScope (fun_decl_name fi) (implode ""));
                  implode "\n"]))
        else errorLogMonad_return one) (\_.
        // check remaining functions
        static_check_progs fctxt gctxt sctxt ectxt decls))))))`;;

(*
  static_check_decls returns:
    ((varname, global_info) map, (funname, func_info) map) static_result
*)
let static_check_decls_def,static_check_decls_ind = define_guess
  `(static_check_decls fctxt gctxt sctxt ectxt [] =
      // no more decls
      errorLogMonad_return (fctxt,gctxt,ectxt)) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (Name _ _) decls) =
      // already processed
      static_check_decls fctxt gctxt sctxt ectxt decls) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (Decl shape vname exp)
    decls) =
      errorLogMonad_bind (
        // setup initial checking context
        ctxt << --(mk_panStatic_context (mlmap_empty mlstring_compare)
            gctxt (mlmap_empty mlstring_compare) ectxt sctxt (DeclScope vname)
            F IsReach InvisLast (implode ""))) (\_. errorLogMonad_bind
        // check for redeclaration
        (check_redec_var (panStatic_context_scope_fupd (K TopLevel) ctxt)
            vname) (\_. errorLogMonad_bind
        // check shape
        // TODO: decl locs
        (check_shape sctxt (implode "") (panStatic_context_scope ctxt)
            shape) (\_. errorLogMonad_bind (static_check_exp ctxt exp) (\
        // check initialisation expression
        eret. errorLogMonad_bind
        // check for shape match
        (if ~(sh_bd_has_shape shape (exp_return_sh_bd eret)) then
          errorMonad_error (ShapeErr (get_shape_mismatch_msg
              (mlstring_concat [
              implode "expression to initialise global variable "; vname])
                  (sh_bd_to_str (exp_return_sh_bd eret)) (shape_to_str shape)
            (implode "") (panStatic_context_scope ctxt)))
        else errorLogMonad_return one) (\_.
        // check remaining decls
        static_check_decls fctxt (mlmap_insert gctxt vname
            (mk_global_info shape)) sctxt ectxt decls)))))) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (ExnDecl eid sh) decls) =
      errorLogMonad_bind
        // check redeclaration
        (if mlmap_member eid ectxt then
          errorMonad_error (ScopeErr (mlstring_concat [
            implode "exception "; eid; implode " is redeclared\n"]))
        else errorLogMonad_return one) (\_.
        // continue with updated exception environment
        static_check_decls fctxt gctxt sctxt (mlmap_insert ectxt eid
            sh) decls)) /\
   (static_check_decls fctxt gctxt sctxt ectxt (CONS (Function fi) decls) =
      errorLogMonad_bind
        // check for redeclaration
        // TODO: decl locs
        (if mlmap_member (fun_decl_name fi) fctxt then
          errorMonad_error (ScopeErr (get_redec_msg panStatic_Fun (implode
              "") (fun_decl_name fi) TopLevel))
        else errorLogMonad_return one) (\_. errorLogMonad_bind
        // check main func
        (if fun_decl_name fi = (implode "main") then
          errorLogMonad_bind
            // check main func args
            (if LENGTH (func_info_params fi) > 0 then
              errorMonad_error (GenErr (implode
                  "main function has arguments\n"))
            else errorLogMonad_return one) (\_. errorLogMonad_bind
            // check main func export status
            (if fun_decl_export fi then
              errorMonad_error (GenErr (implode
                  "main function is exported\n"))
            else errorLogMonad_return one) (\_.
            // check main func return shape
            if ~(fun_decl_return fi = pan_One) then
              errorMonad_error (ShapeErr (get_non_word_msg
                (implode "main function return") (shape_to_str
                    (fun_decl_return fi))
                (implode "") (FunScope (fun_decl_name fi) (implode ""))))
            else errorLogMonad_return one))
        else errorLogMonad_bind
            // check arg name uniqueness
            (match first_repeat (sort mlstring_lt (MAP FST
                (func_info_params fi))) with
              SOME pname -> errorMonad_error (ScopeErr (mlstring_concat [
                  implode "parameter "; pname; implode
                      " is redeclared in function "; fun_decl_name
                  fi; implode "\n"]))
            | NONE -> errorLogMonad_return one) (\_. errorLogMonad_bind
            // check exported func
            (if fun_decl_export fi then
              errorLogMonad_bind
                // check exported func arg num
                (if LENGTH (func_info_params fi) > 4 then
                  errorMonad_error (GenErr (mlstring_concat [
                      implode "exported function "; fun_decl_name fi;
                      implode " has more than 4 arguments\n"]))
                else errorLogMonad_return one) (\_. errorLogMonad_bind
                // check exported func arg shape
                (check_export_params (implode "")
                  (FunScope (fun_decl_name fi) (implode ""))
                      (func_info_params fi)) (\_.
                // check exported func return shape
                if ~(fun_decl_return fi = pan_One) then
                  errorMonad_error (ShapeErr (get_non_word_msg
                    (implode "exported function return") (shape_to_str
                        (fun_decl_return fi))
                    (implode "") (FunScope (fun_decl_name fi) (implode
                        ""))))
                else errorLogMonad_return one))
            else
              // check arg shapes
              // TODO: decl locs
              check_id_shapes sctxt (implode "")
                (FunScope (fun_decl_name fi) (implode ""))
                    (func_info_params fi)) (\_. errorLogMonad_bind
              // check return shape
              (check_shape sctxt (implode "")
                (FunScope (fun_decl_name fi) (implode " return"))
                    (fun_decl_return fi)) (\_.
              // check func return shape size
              if size_of_sh_with_ctxt sctxt (fun_decl_return fi) > 32 then
                errorMonad_error (ShapeErr (mlstring_concat [
                    implode "function "; fun_decl_name fi;
                    implode " returns a shape bigger than 32 words\n"]))
              else errorLogMonad_return one)))) (\_.
        // check remaining decls
        static_check_decls (mlmap_insert fctxt (fun_decl_name fi)
            (mk_func_info (fun_decl_return fi) (func_info_params fi)))
                gctxt sctxt ectxt decls)))`;;

(*
  static_check_names returns:
    ((stcname # struct_info) list) static_result
*)
let static_check_names_def,static_check_names_ind = define_guess
  `static_check_names sctxt x2 =
   match x2 with
     [] ->
     // no more decls
     errorLogMonad_return sctxt
   | CONS (Name name flds) decls ->
     errorLogMonad_bind
       // check for redeclaration
       (match ALOOKUP sctxt name with SOME info ->
         errorMonad_error (ScopeErr (get_redec_msg panStatic_Stc (implode
           "") name TopLevel))
       | NONE -> errorLogMonad_return one) (\_. errorLogMonad_bind
       // check field name uniqueness
       (match first_repeat (sort mlstring_lt (MAP FST flds)) with
         SOME fld -> errorMonad_error (ScopeErr (mlstring_concat [
             implode "field "; fld; implode
               " is redeclared in struct name ";
             name; implode "\n"]))
       | NONE -> errorLogMonad_return one) (\_. errorLogMonad_bind
       // check field shapes
       // TODO: decl locs
       (check_id_shapes sctxt (implode "") (StcScope name (implode ""))
         flds) (\_. errorLogMonad_bind (
       // setup struct info
       info << --(mk_struct_info flds (size_of_sh_with_ctxt sctxt (pan_Comb
         (MAP SND flds))))) (\_.
       // check remaining names
       static_check_names (CONS (name,info) sctxt) decls))))
   | CONS _ decls ->
     // not a struct name
     static_check_names sctxt decls`;;

(*
  static_check returns:
    (unit) static_result

  The static checker returns () if no error occurred, or the static error
  encountered, along with a list of warnings encountered (if any). All warnings
  and errors come with a message containing the issue and its location
*)
let static_check_def = assume_definition
  "declared (no value)"
  `static_check decls =
     errorLogMonad_bind (static_check_names [] decls) (\
       // check decls and build context
       sctxt.
         errorLogMonad_bind (static_check_decls (mlmap_empty
           mlstring_compare)
         (mlmap_empty mlstring_compare) sctxt (mlmap_empty mlstring_compare)
           decls) (\(fctxt,gctxt,ectxt).
       // check function bodies with context
       static_check_progs fctxt gctxt sctxt ectxt decls))`;;

(* and the interface *)
let _ = unhide_overloads ();;
