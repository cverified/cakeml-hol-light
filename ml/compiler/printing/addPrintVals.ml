(* ======================================================== *)
(*  addPrintVals: ported from HOL4's
    compiler/printing/addPrintValsScript.sml
    A definition theory, with 21 definitions, 1 datatype and no
    theorems.  Needed by printTweaks.ml and repl_init_types.ml.  *)
(* ======================================================== *)

(*
   The second pass of the add-printing process. Type checks
   the AST and adds code to print "val x = ..." for every
   variable "x" bound in a declaration. This requires type
   checking to know the type of "x".
*)

needs "basis/pure/mlprettyprinter.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/inference/infer_t.ml";;
needs "compiler/printing/typeDecToPP.ml";;
needs "lib/location.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;
needs "semantics/namespace.ml";;
needs "semantics/typeSystem.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "addPrintVals"
  ["ast"; "infer"; "mlprettyprinter"; "mlstring"; "namespace"; "typeDecToPP"];;

(* the clauses in two quotations: locs is (('n , 'v) alist) and (_#_)list;
   mods is (('m , namespace) alist) and (_)list; rest is (_#_)list and
   (_)list, which one quotation cannot typecheck *)
let nsContents_def,nsContents_ind = define_guess_clauses
  [`nsContents (Bind locs mods) = APPEND (MAP (\(x,y). (Short x,y)) locs)
    (nssContents mods)`;
   `(nssContents [] = []) /\
    (nssContents (CONS (mn,ns) rest) = APPEND (MAP (\(x,y). (Long mn x,y))
    (nsContents ns)) (nssContents rest))`];;

(* The inferencer builds a mapping from type names to its internal
   type numbers, but the printer needs a reverse mapping to print
   inferred types. It maintains a mapping from type numbers to the
   list of names that have mapped to that type, whether or not they
   are current.

   There is also a mapping for "fixes" for type identifiers that
   were not defined with a matching pretty-printer, which is expected
   to only apply to some basis types.
*)
let addPrintVals_type_names_FIELDS = define_record "addPrintVals_type_names"
  ["id_map","(((mlstring,mlstring)namespace_id) list) spt";
   "pp_fixes","(mlstring,mlstring,((mlstring,mlstring)namespace_id) \
   option)namespace"];;

let empty_type_names_def = new_definition
  `empty_type_names = mk_addPrintVals_type_names LN nsEmpty`;;

let add_type_name_def = new_definition
  `add_type_name nm id id_map' =
     let prev = (match sptree_lookup id id_map' with NONE -> [] | SOME nms
       -> nms) in
     sptree_insert id (CONS nm prev) id_map'`;;

let t_info_id_def = new_definition
  `t_info_id x1 =
   match x1 with
     (xs:mlstring list),Tapp ts id ->
     (if ts = MAP Tvar xs then SOME id else NONE)
   | _ -> NONE`;;

let update_type_names_def = new_definition
  `update_type_names ienv tn =
     (let new = MAP (\(x,y). (x,t_info_id y)) (nsContents (inf_env_inf_t
       ienv)) in addPrintVals_type_names_id_map_fupd (K (ITLIST (\(nm,opt_id)
       id_map'. match opt_id with NONE -> id_map'
         | SOME id -> add_type_name nm id id_map') new
           (addPrintVals_type_names_id_map tn)))
     tn)`;;

let strip_tapp_fun_def,strip_tapp_fun_ind = define_guess
  `strip_tapp_fun t =
   match t with
     Infer_Tapp [x; f] n -> (if n = Tfn_num then let (ys,t) = strip_tapp_fun
       f in
     (CONS x ys,t)
     else ([],Infer_Tapp [x; f] n))
   | t -> ([],t)`;;

let tn_current_def = new_definition
  `tn_current ienv id nm = (match nsLookup (inf_env_inf_v ienv) (pp_prefix nm)
  with
     NONE -> F
   | SOME (_,t) ->
     (let (params',_) = strip_tapp_fun t in
     (if NULL params' then F else match LAST params' with
         Infer_Tapp _ id2 -> id2 = id
       | Infer_Tvar_db _ -> T
       | _ -> F)))`;;

let add_to_namespace_def,add_to_namespace_ind = define_guess
  `(add_to_namespace (Short nm) x ns = nsBind nm x ns) /\
   (add_to_namespace (Long mnm id) x ns = (
      let m = (match nsLookupMod ns [mnm] with NONE -> nsEmpty | SOME m ->
          m) in
      nsAppend (nsLift mnm (add_to_namespace id x m)) ns))`;;

(* FOLDR, which the cv translator does not like in this instance. *)
let mk_namespace_aux_def,mk_namespace_aux_ind = define_guess
  `(mk_namespace_aux e [] = e) /\
   (mk_namespace_aux e (CONS (id,x) l) =
      add_to_namespace id x (mk_namespace_aux e l))`;;

let mk_namespace_def = new_definition
  `mk_namespace xs = mk_namespace_aux nsEmpty xs`;;

let FIND_SND_def = new_definition
  `FIND_SND = OPTION_MAP SND o INDEX_FIND 0 SND`;;

let tn_setup_fixes_def = new_definition
  `tn_setup_fixes ienv tn =
     (let info = MAP (\(i,ns). MAP (\n. (n,tn_current ienv i n)) ns)
         (toSortedAList (addPrintVals_type_names_id_map tn)) in
     let fixes = FLAT (MAP (\ns.
         let not_ok = MAP FST (FILTER ((~) o SND) ns) in
         if NULL not_ok then []
         else let fst_ok = OPTION_MAP FST (FIND_SND ns) in
         MAP (\nm. (nm,fst_ok)) not_ok)
      info) in addPrintVals_type_names_pp_fixes_fupd (K (mk_namespace
        fixes))
     tn)`;;

let init_type_names_def = new_definition
  `init_type_names ienv = tn_setup_fixes ienv
     (update_type_names ienv empty_type_names)`;;

let FIND_tn_current_def = new_definition
  `FIND_tn_current ienv id = OPTION_MAP SND o INDEX_FIND 0 (tn_current ienv
  id)`;;

let get_tn_ok_def = new_definition
  `get_tn_ok ienv tn id = OPTION_BIND (sptree_lookup id
  (addPrintVals_type_names_id_map tn))
     (\ids. match (ids,(FIND_tn_current ienv id) ids) with
         (_,SOME current_id) -> SOME current_id
       | ([],NONE) -> NONE
       | (CONS id _,NONE) -> (match nsLookup
         (addPrintVals_type_names_pp_fixes tn) id with
           NONE -> NONE
         | SOME _ ->
             // it's ok to use this, pp_of_ast_t will cope
             SOME id))`;;

(* map the inferred type of a val to its AST counterpart, monomorphising
   any type variables to PrettyPrinter.default_type *)
let inf_t_to_ast_t_mono_def,inf_t_to_ast_t_mono_ind = define_guess
  `(inf_t_to_ast_t_mono ienv tn (Infer_Tuvar _) =
      SOME (Atapp [] (Long (implode "PrettyPrinter") (Short (implode
          "default_type"))))) /\
   (inf_t_to_ast_t_mono ienv tn (Infer_Tvar_db _) =
      SOME (Atapp [] (Long (implode "PrettyPrinter") (Short (implode
          "default_type"))))) /\
   (inf_t_to_ast_t_mono ienv tn (Infer_Tapp ts ti) =
      OPTION_BIND (inf_t_to_ast_t_mono_map ienv tn ts) (\ts.
      if ti = Tfn_num then
        (match ts with [t1; t2] -> SOME (Atfun t1 t2) | _ -> NONE)
      else if ti = Ttup_num then SOME (Attup ts)
      else OPTION_BIND (get_tn_ok ienv tn ti) (\nm. SOME (Atapp ts
          nm)))) /\
   (inf_t_to_ast_t_mono_map ienv tn [] = SOME []) /\
   (inf_t_to_ast_t_mono_map ienv tn (CONS h tl) =
      match inf_t_to_ast_t_mono ienv tn h with NONE -> NONE
      | SOME h ->
        (match inf_t_to_ast_t_mono_map ienv tn tl with NONE -> NONE
        | SOME tl -> SOME (CONS h tl)))`;;

let type_con_name_def = new_definition
  `type_con_name tn ti =
   (match sptree_lookup ti (addPrintVals_type_names_id_map tn) with
       NONE -> (implode "undeclared")
     | SOME [] -> (implode "undeclared")
     | SOME nms -> id_to_n (LAST nms))`;;

(* This function used to be called inf_type_to_string_rec_gen and took a
   function f as an argument. Since inf_t_to_s was its only user, and only used
   it with (type_con_name tn) for some type_names tn, I have inlined it,
   allowing us to cv_trans it. *)
let addPrintVals_inf_type_to_string_def,addPrintVals_inf_type_to_string_ind =
  define_guess
  `(addPrintVals_inf_type_to_string tn (Infer_Tuvar n) =
        (mlstring_concat [(implode " "); mlint_toString (&n)],0)) /\
   (addPrintVals_inf_type_to_string tn (Infer_Tvar_db n) =
        (mlstring_concat [ty_var_name n],0)) /\
   (addPrintVals_inf_type_to_string tn (Infer_Tapp ts ti) =
        if ti = Tfn_num then
         (match ts with [t1; t2] ->
            (mlstring_concat [add_parens 2 (addPrintVals_inf_type_to_string
                tn t1); (implode " -> ");
                     add_parens 3 (addPrintVals_inf_type_to_string tn
                         t2)],3)
          | _ -> ((implode "<bad function type>"),0))
        else if ti = Ttup_num then
         (match ts with [] -> ((implode "unit"),0)
          | [t] -> addPrintVals_inf_type_to_string tn t
          | _ -> (mlstring_concat (infer_t_commas ((implode " * "))
                   (MAP (add_parens 1) (inf_type_to_string_list tn
                       ts))),2))
        else match ts with [] -> (type_con_name tn ti,0)
          | [t] ->
            (mlstring_concat [add_parens 1 (addPrintVals_inf_type_to_string
                tn t); (implode " ");
                     type_con_name tn ti],1)
          | _ ->
            (mlstring_concat (APPEND (APPEND [(implode "(")]
                     (infer_t_commas ((implode ","))
                       (MAP (add_parens 5) (inf_type_to_string_list tn
                           ts))))
                     [(implode ") "); type_con_name tn ti]),1)) /\
   (inf_type_to_string_list tn [] = []) /\
   (inf_type_to_string_list tn (CONS t ts) = CONS
    (addPrintVals_inf_type_to_string tn t)
      (inf_type_to_string_list tn ts))`;;

let inf_t_to_s_def = new_definition
  `inf_t_to_s tn t = FST (addPrintVals_inf_type_to_string tn t)`;;

let print_of_val_opts_def = new_definition
  `print_of_val_opts ienv tn (nm,inf_t) =
     (let nm_str = id_to_str nm in
     let idl = ast_Lit (ast_StrLit nm_str) in
     let tstr = ast_Lit (ast_StrLit (inf_t_to_s tn inf_t)) in
     let pp_hidden = Dlet unknown_loc ast_Pany (ast_App ast_Opapp [ast_Var
       (Short (implode "print_pp"));
         Apps (ast_Var (Long (implode "PrettyPrinter") (Short (implode
           "val_hidden_type")))) [idl; tstr]]) in
     let pp_val = (match inf_t_to_ast_t_mono ienv tn inf_t with
           NONE -> []
         | SOME ast_t -> [Dlet unknown_loc ast_Pany (ast_App ast_Opapp
           [ast_Var (Short (implode "print_pp"));
             Apps (ast_Var (Long (implode "PrettyPrinter") (Short (implode
               "val_eq"))))
                 [idl; pp_of_ast_t (addPrintVals_type_names_pp_fixes tn)
                   ast_t; ast_Var nm; tstr]])]) in
     (nm_str,APPEND pp_val [pp_hidden]))`;;

let val_prints_def = new_definition
  `val_prints tn prev_ienv decs_ienv =
     let tn2 = update_type_names decs_ienv tn in
     let full_ienv = extend_dec_ienv decs_ienv prev_ienv in
     let prints = MAP (print_of_val_opts full_ienv tn2)
         (MAP (\(x,y). (x,SND y)) (REVERSE (nsContents (ns_nub
           (inf_env_inf_v decs_ienv))))) in
     (prints,tn2)`;;

(* and the interface *)
let _ = unhide_overloads ();;
