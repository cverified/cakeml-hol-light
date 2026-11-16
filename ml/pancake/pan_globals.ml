(* ======================================================== *)
(*  pan_globals: ported from HOL4's
    pancake/pan_globalsScript.sml
    A definition theory, with 11 definitions, 1 datatype and no
    theorems.  Needed by from_pancake32Prog.ml,
    from_pancake64Prog.ml and pan_to_word.ml.  *)
(* ======================================================== *)

(*
  Allocate globals at the end of heap.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "lib/byte.ml";;
needs "pancake/panLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_globals"
  ["backend_common"; "panLang"];;

let pan_globals_context_FIELDS = define_record "pan_globals_context"
  ["globals","(mlstring,shape#'a word)fmap";
   "globals_size","'a word";
   "max_globals_size","'a word"];;

(* the termination relation that HOL4 gives is
     MEASURE (\e. pan_exp_size ARB (SND e))
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pan_globalsScript.sml:47-53: the tactic that proves the termination *)
let pan_globals_compile_exp_def,pan_globals_compile_exp_ind = define_guess
  `pan_globals_compile_exp ctxt e =
     match e with
       pan_Var pan_Local vname -> pan_Var pan_Local vname
     | pan_Var pan_Global vname ->
      (match FLOOKUP (pan_globals_context_globals ctxt) vname with
        NONE -> pan_Const (n2w 0)
      |
        // should never happen
        SOME (sh,addr) -> pan_Load sh (pan_Op asm_Sub [pan_TopAddr;
          pan_Const addr]))
     | pan_RStruct es -> pan_RStruct (MAP (pan_globals_compile_exp ctxt) es)
     | pan_RField index e ->
      pan_RField index (pan_globals_compile_exp ctxt e)
     | pan_NStruct nm flds ->
      pan_Const (n2w 0)
     // should never happen
     | pan_NField fld e ->
      pan_Const (n2w 0)
     // should never happen
     | pan_Load sh e ->
      pan_Load sh (pan_globals_compile_exp ctxt e)
     | pan_LoadByte e ->
      pan_LoadByte (pan_globals_compile_exp ctxt e)
     | pan_Load32 e ->
      pan_Load32 (pan_globals_compile_exp ctxt e)
     | pan_Op bop es ->
      pan_Op bop (MAP (pan_globals_compile_exp ctxt) es)
     | pan_Panop pop es ->
      pan_Panop pop (MAP (pan_globals_compile_exp ctxt) es)
     | pan_Cmp cmp e e' ->
      pan_Cmp cmp (pan_globals_compile_exp ctxt e) (pan_globals_compile_exp
        ctxt e')
     | pan_Shift sh e e' ->
      pan_Shift sh (pan_globals_compile_exp ctxt e) (pan_globals_compile_exp
        ctxt e')
     | pan_TopAddr -> pan_Op asm_Sub [pan_TopAddr; pan_Const
       (pan_globals_context_max_globals_size ctxt)]
     | e -> e`;;

(* HOL4 pan_globalsScript.sml:61-67: the tactic that proves the termination *)
let fresh_name_def,fresh_name_ind = define_guess
  `fresh_name name names =
   if MEM name names then
     fresh_name (strcat name (implode "'")) names
   else name`;;

let pan_globals_compile_def,pan_globals_compile_ind = define_guess
  `pan_globals_compile ctxt p =
     match p with
       pan_Dec v s e p ->
      pan_Dec v s (pan_globals_compile_exp ctxt e) (pan_globals_compile ctxt
        p)
     | pan_Assign vk v e ->
      (match vk with
         pan_Global ->
           (match FLOOKUP (pan_globals_context_globals ctxt) v with
             NONE -> pan_Skip
            |
              // shouldn't happen
              SOME (sh,addr) -> pan_Store (pan_Op asm_Sub [pan_TopAddr;
                pan_Const addr]) (pan_globals_compile_exp ctxt e))
       | _ -> pan_Assign pan_Local v (pan_globals_compile_exp ctxt e))
     | pan_Primitive v pop es ->
      pan_Primitive v pop (MAP (pan_globals_compile_exp ctxt) es)
     | pan_Store ad v ->
      pan_Store (pan_globals_compile_exp ctxt ad) (pan_globals_compile_exp
        ctxt v)
     | pan_Store32 ad v ->
      pan_Store32 (pan_globals_compile_exp ctxt ad) (pan_globals_compile_exp
        ctxt v)
     | pan_StoreByte dest src ->
      pan_StoreByte (pan_globals_compile_exp ctxt dest)
        (pan_globals_compile_exp ctxt src)
     | pan_Return rt ->
      pan_Return (pan_globals_compile_exp ctxt rt)
     | pan_Raise eid excp ->
      pan_Raise eid (pan_globals_compile_exp ctxt excp)
     | pan_Seq p p' ->
      pan_Seq (pan_globals_compile ctxt p) (pan_globals_compile ctxt p')
     | pan_If e p p' ->
      pan_If (pan_globals_compile_exp ctxt e) (pan_globals_compile ctxt p)
        (pan_globals_compile ctxt p')
     | pan_While e p ->
      pan_While (pan_globals_compile_exp ctxt e) (pan_globals_compile ctxt
        p)
     | pan_Call rtyp e es ->
      (let cexps = MAP (pan_globals_compile_exp ctxt) es in
        match rtyp with
          NONE -> pan_Call NONE e cexps
        | SOME (SOME (pan_Global,vn),hdl) ->
            (match FLOOKUP (pan_globals_context_globals ctxt) vn with
              NONE ->
                // ...should never happen, but needs to preserve timeouts
                pan_Call (SOME (NONE,
                            (match hdl with NONE -> NONE
                            | SOME (eid,evar,p) ->
                              SOME (eid,evar,pan_globals_compile ctxt p))))
                     e
                     cexps
            | SOME (sh,addr) ->
                (match hdl with
                   NONE ->
                     pan_DecCall (implode "") sh e cexps (pan_Store (pan_Op
                       asm_Sub [pan_TopAddr; pan_Const addr]) (pan_Var
                       pan_Local (implode "")))
                 | SOME (eid,evar,p) ->
                     let
                       p' = pan_globals_compile ctxt p in let
                       names = APPEND (CONS evar (free_var_ids p')) (FLAT
                         (MAP var_exp cexps)) in let
                       vn' = fresh_name (implode "") names in let
                       flag = fresh_name (implode "vn'") (CONS vn' names) in
                       pan_Dec vn' sh (shape_val sh) (pan_Dec flag pan_One
                         (pan_Const (n2w 0)) (
                           pan_Seq (pan_Call (SOME (SOME
                             (pan_Local,vn'),SOME (eid,evar,pan_Seq p'
                             (pan_Assign pan_Local flag (pan_Const (n2w 1))))))
                             e cexps) (
                           pan_If (pan_Var pan_Local flag) pan_Skip
                           (pan_Store (pan_Op asm_Sub [pan_TopAddr;
                             pan_Const addr]) (pan_Var pan_Local vn')))))))
        | SOME (tl,hdl) ->
            pan_Call (SOME (tl,
                        (match hdl with NONE -> NONE
                        | SOME (eid,evar,p) ->
                            SOME (eid,evar,pan_globals_compile ctxt p))))
                 e
                 cexps)
     | pan_DecCall v s e es p ->
      pan_DecCall v s e (MAP (pan_globals_compile_exp ctxt) es)
        (pan_globals_compile ctxt p)
     | pan_ExtCall f ptr1 len1 ptr2 len2 ->
      pan_ExtCall f
              (pan_globals_compile_exp ctxt ptr1)
              (pan_globals_compile_exp ctxt len1)
              (pan_globals_compile_exp ctxt ptr2)
              (pan_globals_compile_exp ctxt len2)
     | pan_ShMemStore op r ad ->
      pan_ShMemStore op (pan_globals_compile_exp ctxt r)
        (pan_globals_compile_exp ctxt ad)
     | pan_ShMemLoad op pan_Local r ad ->
      pan_ShMemLoad op pan_Local r (pan_globals_compile_exp ctxt ad)
     | pan_ShMemLoad op pan_Global r ad ->
      (match FLOOKUP (pan_globals_context_globals ctxt) r with SOME
        (pan_One,addr) ->
          (let r' = strcat r (implode "'") in
             pan_Dec r pan_One (pan_globals_compile_exp ctxt ad) (
                 pan_Dec r' pan_One (pan_Const (n2w 0)) (
                 pan_Seq (pan_ShMemLoad op pan_Local r' (pan_Var pan_Local
                   r))
                 (pan_Store (pan_Op asm_Sub [pan_TopAddr; pan_Const addr])
                   (pan_Var pan_Local r')))))
      | _ -> pan_Skip)
     // Should never happen
     | p -> p`;;

let pan_globals_compile_decs_def,pan_globals_compile_decs_ind = define_guess
  `(pan_globals_compile_decs ctxt [] = ([],([]:('a decl) list),([]:('a
    decl) list),ctxt)) /\
   (pan_globals_compile_decs ctxt (CONS (Decl sh v e) ds) =
         let
           s = pan_globals_context_globals_size ctxt + bytes_in_word * n2w
               (size_of_shape sh) in let
           ctxt' = pan_globals_context_globals_size_fupd (K s)
               (pan_globals_context_globals_fupd (K
               (pan_globals_context_globals ctxt |+ (v,sh,s))) ctxt) in let
           (decs,funs,exns,ctxt'') = pan_globals_compile_decs ctxt' ds in
            (CONS (pan_Store (pan_Op asm_Sub [pan_TopAddr; pan_Const
                s]) (pan_globals_compile_exp ctxt e))
                decs,funs,exns,ctxt'')) /\
   (pan_globals_compile_decs ctxt (CONS (Function fi) ds) =
         let (decs,funs,exns,ctxt'') = pan_globals_compile_decs ctxt ds
             in (decs,CONS (Function (fun_decl_body_fupd (K
             (pan_globals_compile ctxt (fun_decl_body fi))) fi))
             funs,exns,ctxt'')) /\
   (pan_globals_compile_decs ctxt (CONS (ExnDecl eid sh) ds) =
         let (decs,funs,exns,ctxt'') = pan_globals_compile_decs ctxt ds
             in (decs,funs,CONS (ExnDecl eid sh) exns,ctxt'')) /\
   (pan_globals_compile_decs ctxt (CONS (Name nm flds) ds) =
    pan_globals_compile_decs ctxt ds)
   // should never happen`;;

let resort_decls_def = new_definition
  `resort_decls decs = APPEND (APPEND (APPEND (FILTER (is_name) decs)
  (FILTER (is_exn_decl) decs)) (FILTER (is_decl) decs)) (FILTER is_function
  decs)`;;

let fperm_name_def = new_definition
  `fperm_name f g h =
   if f = h then g
   else if g = h then f
   else h`;;

let fperm_def,fperm_ind = define_guess
  `fperm f g p =
     match p with
       pan_Dec v s e p ->
      pan_Dec v s e (fperm f g p)
     | pan_Seq p p' ->
      pan_Seq (fperm f g p) (fperm f g p')
     | pan_If e p p' ->
      pan_If e (fperm f g p) (fperm f g p')
     | pan_While e p ->
      pan_While e (fperm f g p)
     | pan_Call rtyp e es ->
      pan_Call (match rtyp with NONE -> NONE
            | SOME (tl,hdl) ->
                SOME (tl,
                      (match hdl with NONE -> NONE
                      | SOME (eid,evar,p) ->
                          SOME (eid,evar,fperm f g p))))
           (fperm_name f g e)
           es
     | pan_DecCall v s e es p ->
      pan_DecCall v s (fperm_name f g e) es (fperm f g p)
     | p -> p`;;

let fperm_decs_def,fperm_decs_ind = define_guess
  `fperm_decs f g x3 =
     match x3 with
       [] -> []
     | CONS (Function fi) decs ->
               CONS (Function (fun_decl_body_fupd (K (fperm f g
                 (fun_decl_body fi))) (fun_decl_name_fupd (K (fperm_name f g
                 (fun_decl_name fi))) fi))) (fperm_decs f g decs)
     | CONS d decs -> CONS d (fperm_decs f g decs)`;;

let new_main_name_def = new_definition
  `new_main_name decls = fresh_name (implode "main") (MAP FST (functions
  decls))`;;

let dec_shapes_def,dec_shapes_ind = define_guess
  `(dec_shapes (CONS (Function _) ds) = dec_shapes ds) /\
   (dec_shapes (CONS (Decl sh _ _) ds) = CONS sh (dec_shapes ds)) /\
   (dec_shapes (CONS (Name _ _) ds) = dec_shapes ds) /\
   (dec_shapes (CONS (ExnDecl _ _) ds) = dec_shapes ds) /\
   (dec_shapes [] = [])`;;

let compile_top_def = new_definition
  `pan_globals_compile_top decs start' =
   match ALOOKUP (functions decs) start' with
     NONE -> []
   | SOME (args,body,rshape) ->
       let nds = resort_decls decs in let
           start' = new_main_name decs in let
           nds' = fperm_decs start' start' nds in let
           (decls,funs,exns,ctxt) = pan_globals_compile_decs
                              (mk_pan_globals_context FEMPTY (n2w 0)
                                (bytes_in_word * n2w (SUM (MAP size_of_shape
                                (dec_shapes nds'))))) nds' in let
           params' = MAP (pan_Var pan_Local o FST) args in let
           new_main = Function (mk_fun_decl start' F F args (pan_Seq
             (pan_nested_seq decls) ((asm_Call NONE) start' params'))
             rshape) in APPEND exns (CONS new_main funs)`;;

(* and the interface *)
let _ = unhide_overloads ();;
