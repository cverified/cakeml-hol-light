(* ======================================================== *)
(*  pan_passes: ported from HOL4's
    pancake/pan_passesScript.sml
    A definition theory, with 23 definitions, 1 datatype and 8
    theorems.  Needed by compiler.ml.  *)
(* ======================================================== *)

(*
  Reformulates compile definition to expose the result of each internal
  compiler pass
*)

needs "basis/RuntimeProg.ml";;
needs "basis/pure/mllist.ml";;
needs "basis/pure/mlsexp.ml";;
needs "basis/pure/mlstring.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeaps.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/displayLang.ml";;
needs "compiler/backend/presLang.ml";;
needs "compiler/backend/wordLang.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/errorMonad.ml";;
needs "lib/multiword.ml";;
needs "lib/peg.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "pancake/crepLang.ml";;
needs "pancake/crep_arith.ml";;
needs "pancake/crep_inline.ml";;
needs "pancake/crep_to_loop.ml";;
needs "pancake/loopLang.ml";;
needs "pancake/panLang.ml";;
needs "pancake/pan_to_crep.ml";;
needs "pancake/pan_to_target.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_passes"
  ["backend"; "backend_passes"; "mllist"; "pan_to_target"; "presLang"];;


let any_pan_prog_INDUCT,any_pan_prog_RECURSION = define_datatype
  "any_pan_prog =
     pan_passes_Pan (('a decl) list)
   | pan_passes_Crep ((mlstring#num list#alpha crep_prog) list)
   | pan_passes_Loop ((num#num list#alpha loop_prog) list) (mlstring spt)
   | pan_passes_Cake ('a any_prog)";;

let pan_to_target_all_def = new_definition
  `pan_to_target_all asm_conf (c:backend_config) prog =
     let
       prog1:('a decl) list = (match SPLITP (\x. match x with
                             Function fi -> fun_decl_name fi = (implode
                               "main")
                           | _ -> F) prog with ([],ys) -> ys
               | (xs,[]) ->
                             CONS (Function
                             (mk_fun_decl (implode "main") F F []
                               (stack_Return (pan_Const (n2w 0))) pan_One)) xs
               | (xs,CONS y ys) -> APPEND (CONS y xs) ys) in
       let
         ps = [((implode "initial pancake program"),pan_passes_Pan prog1)]
           in let
         prog_a0 = pan_simp_compile_prog prog1 in let
         ps = APPEND ps [((implode "after pan_simp"),pan_passes_Pan
           prog_a0)] in let
         prog_a1 = pan_structs_compile_top prog_a0 in let
         ps = APPEND ps [((implode "after pan_structs"),pan_passes_Pan
           prog_a1)] in let
         prog_a = pan_globals_compile_top prog_a1 (implode "main") in let
         ps = APPEND ps [((implode "after pan_globals"),pan_passes_Pan
           prog_a)] in let
         prog_b0 = compile_to_crep prog_a in let
         ps = APPEND ps [((implode "after pan_to_crep"),pan_passes_Crep
           prog_b0)] in let
         inl_fs_names = MAP FST (functions (FILTER inlinable prog_a)) in let
         prog_bi = compile_inl_top inl_fs_names prog_b0 in let
         ps = APPEND ps [((implode "after crep_inline"),pan_passes_Crep
           prog_bi)] in let
         prog_b = MAP (\(n,ps,e). (n,ps,simp_prog e)) prog_bi in let
         ps = APPEND ps [((implode "after crep_arith"),pan_passes_Crep
           prog_b)] in let
         fnums = list_of_seq (\n. n + first_name) (LENGTH prog_b) in let
         funcs = pan_to_crep_make_funcs prog_b in let
         target = asm_config_ISA asm_conf in let
         word_to_stack_comp = pan_to_crep_comp_func target funcs in let
         prog_b1 = MAP2 (\n (name,params',body).
                     (n,(list_of_seq I o LENGTH) params',word_to_stack_comp
                       params' body)) fnums prog_b in let
         prog_c = MAP (\(name,params',body).
           (name,params',loop_live_optimise body)) prog_b1 in let
         prog2 = loop_to_word_compile_prog prog_c in let
         names = fromAList (ZIP (sort (<) (MAP FST prog2)) (CONS (implode
           "generated_main") (MAP FST (functions prog1)))) in let
         names = sptree_union (fromAList (APPEND (APPEND
           (word_to_stack_stub_names one)
                              (stack_alloc_stub_names one))
                              (stack_remove_stub_names one))) names in let
         ps = APPEND ps [((implode "after crep_to_loop"),pan_passes_Loop
           prog_b1 names)] in let
         ps = APPEND ps [((implode "after loop_optimise"),pan_passes_Loop
           prog_c names)] in let
         ps = APPEND ps [((implode "after loop_to_word"),pan_passes_Cake
           (backend_passes_Word prog2 names))] in let
         c = backend_config_exported_fupd (K (exports prog)) c in let
         (ps1,out) = from_word_0_all [] asm_conf c names prog2 in
         (APPEND ps (MAP (\(n,p). (n,pan_passes_Cake p)) ps1),out)`;;

(* [local] *)
let MAP2_MAP = prove
 (`!xs ys. MAP2 g xs (MAP f ys) = MAP2 (\x y. g x (f y)) xs ys`,
  CHEAT_TAC);;

(* [local] *)
let MAP_MAP2 = prove
 (`!xs ys. MAP f (MAP2 g xs ys) = MAP2 (\x y. f (g x y)) xs ys`,
  CHEAT_TAC);;

(* [local] *)
let make_funcs_MAP = prove
 (`!xs. pan_to_crep_make_funcs (MAP (\(n,ps,e). (n,ps,f e)) xs) =
  crep_to_loop_make_funcs xs`,
  CHEAT_TAC);;

let compile_prog_eq_pan_to_target_all = prove
 (`pan_to_target_compile_prog asm_conf c p = SND (pan_to_target_all asm_conf
  c p)`,
  CHEAT_TAC);;

(* pan *)

let opsize_to_display_def = define_cases
  `(opsize_to_display Op8 = empty_item (implode "byte")) /\
   (opsize_to_display Op16 = empty_item (implode "word16")) /\
   (opsize_to_display OpW = empty_item (implode "word")) /\
   (opsize_to_display Op32 = empty_item (implode "word32"))`;;

let insert_es_def = new_definition
  `insert_es x xs =
   match x with
     display_String n -> display_Item NONE n xs
   | x -> x`;;

let varkind_to_str_def = new_definition
  `varkind_to_str vk =
     match vk with
       pan_Global -> (implode "global")
     | pan_Local -> (implode "local")`;;

let primop_to_display_def = new_definition
  `primop_to_display pan_AddCarry = display_String (implode "AddCarry")`;;

(* the clauses in two quotations: fxs is ((fldname # exp) list) and
   (_#_)list; n is varname and index, which one quotation cannot typecheck *)
let pan_exp_to_display_def,pan_exp_to_display_ind = define_guess_clauses
  [`(pan_exp_to_display (pan_Const v) = item_with_word (implode "Const") v) /\
    (pan_exp_to_display (pan_Var vk n) = display_Item NONE (implode "Var")
          [display_String (varkind_to_str vk);
           display_String n]) /\
    (pan_exp_to_display pan_BaseAddr = display_Item NONE (implode
    "BaseAddr") []) /\
    (pan_exp_to_display pan_TopAddr = display_Item NONE (implode "TopAddr")
    []) /\
    (pan_exp_to_display pan_BytesInWord = display_Item NONE (implode
    "BytesInWord") []) /\
    (pan_exp_to_display (pan_Load shape exp2) = display_Item NONE (implode
    "MemLoad")
           [display_String (shape_to_str shape);
            pan_exp_to_display exp2]) /\
    (pan_exp_to_display (pan_Load32 exp2) = display_Item NONE (implode
    "MemLoad32") [pan_exp_to_display exp2]) /\
    (pan_exp_to_display (pan_LoadByte exp2) = display_Item NONE (implode
    "MemLoadByte") [pan_exp_to_display exp2]) /\
    (pan_exp_to_display (pan_RStruct xs) = display_Item NONE (implode
    "RawStruct") (MAP pan_exp_to_display xs)) /\
    (pan_exp_to_display (pan_NStruct nm fxs) =
      // #!DONE
      display_Item NONE (implode "NamedStruct") (CONS (display_String nm)
          (MAP (
        \(f,x). display_Tuple [display_String f; display_String
            (implode ":="); pan_exp_to_display x]) fxs))) /\
    (pan_exp_to_display (pan_Cmp cmp x1 x2) = insert_es (asm_cmp_to_display
      cmp)
                [pan_exp_to_display x1; pan_exp_to_display x2]) /\
    (pan_exp_to_display (pan_Op b xs) = insert_es (asm_binop_to_display b)
    (MAP pan_exp_to_display xs)) /\
    (pan_exp_to_display (pan_Panop p xs) = match p with pan_Mul ->
    display_Item NONE (implode "Mul") (MAP pan_exp_to_display xs)) /\
    (pan_exp_to_display (pan_NField f e) =
      // #!TEST
      display_Item NONE (implode "NamedField") [display_String f;
          pan_exp_to_display e]) /\
    (pan_exp_to_display (pan_Shift sh e e') = insert_es (shift_to_display
    sh) [pan_exp_to_display e; pan_exp_to_display e'])`;
   `pan_exp_to_display (pan_RField n e) = display_Item NONE (implode
    "RawField") [num_to_display n; pan_exp_to_display e]`];;

let dest_annot_def = new_definition
  `dest_annot x1 =
   match x1 with
     pan_Annot k str -> SOME (k,str)
   | _ -> NONE`;;

(* treat (Seq (Annot _) _) as a special case, and don't flatten it *)
let pan_seqs_def,pan_seqs_ind = define_guess
  `pan_seqs z =
     match z with pan_Seq x y -> (match dest_annot x with SOME _ ->
       display_List [z]
         | _ -> misc_Append (pan_seqs x) (pan_seqs y))
     | _ -> display_List [z]`;;

(* [local] *)
let MEM_append_pan_seqs = prove
 (`!prog1 a.
     MEM a (append (pan_seqs prog1)) ==>
     lab_prog_size ARB a <= lab_prog_size ARB prog1`,
  CHEAT_TAC);;

(* the clauses in two quotations: args is (('a exp) list) and ('a exp list);
   n is varname and eid, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL p -> pan_prog_size ARB p
                | INR p -> option_size (\(_,_,p). lab_prog_size ARB p) p)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pan_passesScript.sml:301-309: the tactic that proves the termination *)
let pan_prog_to_display_def,pan_prog_to_display_ind = define_guess_clauses
  [`(pan_prog_to_display pan_Skip = empty_item (implode "skip")) /\
    (pan_prog_to_display (pan_ShMemLoad s vk v e) =
         display_Item NONE (implode "shared_mem_load")
              [opsize_to_display s;
               display_String (varkind_to_str vk);
               display_String v;
               pan_exp_to_display e]) /\
    (pan_prog_to_display (pan_ShMemStore s e1 e2) =
         display_Item NONE (implode "shared_mem_store")
              [opsize_to_display s;
               pan_exp_to_display e1;
               pan_exp_to_display e2]) /\
    (pan_prog_to_display (pan_ExtCall f e1 e2 e3 e4) =
         display_Item NONE (implode "ext_call")
              [display_String f;
               pan_exp_to_display e1;
               pan_exp_to_display e2;
               pan_exp_to_display e3;
               pan_exp_to_display e4]) /\
    (pan_prog_to_display (pan_If e p1 p2) =
         display_Item NONE (implode "if")
              [pan_exp_to_display e;
               pan_prog_to_display p1;
               pan_prog_to_display p2]) /\
    (pan_prog_to_display (pan_While e p) =
         display_Item NONE (implode "while")
              [pan_exp_to_display e;
               pan_prog_to_display p]) /\
    (pan_prog_to_display (pan_Dec n shape e p) =
         display_Item NONE (implode "dec")
              [display_Tuple [display_String (implode "local");
                      display_String (shape_to_str shape);
                      display_String n;
                      display_String (implode ":=");
                      pan_exp_to_display e];
               pan_prog_to_display p]) /\
    (pan_prog_to_display (pan_Assign vk n exp) =
         display_Tuple [display_String (varkind_to_str vk);
                display_String n;
                display_String (implode ":=");
                pan_exp_to_display exp]) /\
    (pan_prog_to_display (pan_Primitive v pop es) =
         display_Tuple [display_String v;
                display_String (implode ":=");
                insert_es (primop_to_display pop) (MAP
                    pan_exp_to_display es)]) /\
    (pan_prog_to_display (pan_Store e1 e2) = display_Tuple
        [display_String (implode "mem"); pan_exp_to_display e1;
         display_String (implode ":="); pan_exp_to_display e2]) /\
    (pan_prog_to_display (pan_Store32 e1 e2) = display_Tuple
        [display_String (implode "mem"); pan_exp_to_display e1;
         display_String (implode ":="); display_String (implode
             "32bit"); pan_exp_to_display e2]) /\
    (pan_prog_to_display (pan_StoreByte e1 e2) = display_Tuple
        [display_String (implode "mem"); pan_exp_to_display e1;
         display_String (implode ":="); display_String (implode
             "byte"); pan_exp_to_display e2]) /\
    (pan_prog_to_display (pan_Annot k str) = display_Item NONE (implode
      "annot")
        [display_String (escape_str k); display_String (escape_str
            str)]) /\
    (pan_prog_to_display pan_Tick = empty_item (implode "tick")) /\
    (pan_prog_to_display pan_Break = empty_item (implode "break")) /\
    (pan_prog_to_display pan_Continue = empty_item (implode "continue")) /\
    (pan_prog_to_display (pan_Return e) =
         display_Item NONE (implode "return") [pan_exp_to_display e]) /\
    (pan_prog_to_display (pan_Seq prog1 prog2) =
         let xs = append (misc_Append (pan_seqs prog1) (pan_seqs prog2)) in
         separate_lines (implode "seq") (MAP pan_prog_to_display xs)) /\
    (pan_prog_to_display (pan_Call ret_opt f args) =
         match ret_opt with NONE ->
             display_Item NONE (implode "tail_call")
                  [display_String f;
                   display_Tuple (MAP pan_exp_to_display args)]
         | SOME (NONE,handler) ->
             display_Item NONE (implode "call")
                  [display_String f;
                   display_Tuple (MAP pan_exp_to_display args);
                   pan_prog_to_display_handler handler]
         | SOME (SOME (vk,v),handler) ->
             display_Tuple [display_String v;
                    display_String (implode ":=");
                    display_Item NONE (implode "call")
                         [display_String f;
                          display_Tuple (MAP pan_exp_to_display args);
                          pan_prog_to_display_handler handler]]) /\
    (pan_prog_to_display (pan_DecCall v shape f args p) =
         display_Item NONE (implode "dec")
              [display_Tuple [display_String (shape_to_str shape);
                      display_String v;
                      display_String (implode ":=");
                      display_Item NONE (implode "call")
                           [display_String f;
                            display_Tuple (MAP pan_exp_to_display args)]];
               pan_prog_to_display p]) /\
    (pan_prog_to_display_handler NONE = empty_item (implode "no_handler")) /\
    (pan_prog_to_display_handler (SOME (v1,v2,p)) =
        display_Item NONE (implode "handler")
          [display_Tuple [display_String v1; display_String v2;
              pan_prog_to_display p]])`;
   `pan_prog_to_display (pan_Raise n e) =
         display_Item NONE (implode "raise") [display_String n;
             pan_exp_to_display e]`];;

let pan_fun_to_display_def = new_definition
  `pan_fun_to_display decl =
     match decl with
       Function fi -> display_Tuple
         [display_String (implode "func"); display_String (shape_to_str
           (fun_decl_return fi)); display_String (fun_decl_name fi);
         display_Tuple (MAP (\(s,shape). display_Tuple [display_String s;
                              display_String (implode ":");
                              display_String (shape_to_str shape)])
                                (fun_decl_params fi));
         pan_prog_to_display (fun_decl_body fi)]
     | Decl sh nm exp -> display_Tuple
         [display_String (implode "global");
          display_String (shape_to_str sh);
          display_String nm;
          display_String (implode ":=");
          pan_exp_to_display exp]
     | Name nm flds -> display_Tuple
         [display_String (implode "struct");
          display_String nm;
         display_Tuple (MAP (\(fld,shape).
           display_Tuple [display_String fld;
                   display_String (implode ":");
                   display_String (shape_to_str shape)]) flds)]
     | ExnDecl nm sh -> display_Tuple
         [display_String (implode "exception");
          display_String nm;
          display_String (implode ":");
          display_String (shape_to_str sh)]`;;

let pan_to_strs_def = new_definition
  `pan_to_strs xs =
     map_to_append
       (str_tree_to_strs (implode "\n\n") o display_to_str_tree o
         pan_fun_to_display) xs`;;

(* crep *)

let crep_exp_to_display_def,crep_exp_to_display_ind = define_guess
  `(crep_exp_to_display (crep_Const v) = item_with_word (implode "Const") v) /\
   (crep_exp_to_display (crep_LoadGlob w) = item_with_word (implode
    "LoadGlob") w) /\
   (crep_exp_to_display (crep_Var n) = display_Item NONE (implode "Var")
    [num_to_display n]) /\
   (crep_exp_to_display crep_BaseAddr = display_Item NONE (implode
    "BaseAddr") []) /\
   (crep_exp_to_display crep_TopAddr = display_Item NONE (implode
    "TopAddr") []) /\
   (crep_exp_to_display (crep_Load exp2) = display_Item NONE (implode
    "MemLoad") [crep_exp_to_display exp2]) /\
   (crep_exp_to_display (crep_Load32 exp2) = display_Item NONE (implode
    "MemLoad32") [crep_exp_to_display exp2]) /\
   (crep_exp_to_display (crep_LoadByte exp2) = display_Item NONE (implode
    "MemLoadByte") [crep_exp_to_display exp2]) /\
   (crep_exp_to_display (crep_Cmp cmp x1 x2) = insert_es (asm_cmp_to_display
    cmp)
                [crep_exp_to_display x1; crep_exp_to_display x2]) /\
   (crep_exp_to_display (crep_Op b xs) = insert_es (asm_binop_to_display b)
    (MAP crep_exp_to_display xs)) /\
   (crep_exp_to_display (crep_Crepop p xs) = match p with crep_Mul ->
    display_Item NONE (implode "Mul") (MAP crep_exp_to_display xs)) /\
   (crep_exp_to_display (crep_Shift sh e e') = insert_es (shift_to_display
    sh) [crep_exp_to_display e; crep_exp_to_display e'])`;;

let crep_seqs_def,crep_seqs_ind = define_guess
  `crep_seqs z =
     match z with crep_Seq x y -> misc_Append (crep_seqs x) (crep_seqs y)
     | _ -> display_List [z]`;;

(* [local] *)
let MEM_append_crep_seqs = prove
 (`!prog1 a.
     MEM a (append (crep_seqs prog1)) ==>
     lab_prog_size ARB a <= lab_prog_size ARB prog1`,
  CHEAT_TAC);;

(* the clauses in two quotations: e1 is varname and ('a exp); e2 is varname
   and ('a exp); n is varname and num; w is (5 word) and ('a word), which one
   quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL p -> crep_prog_size ARB p
                | INR p -> option_size (pair_size w2n (crep_prog_size ARB)) p)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pan_passesScript.sml:481-490: the tactic that proves the termination *)
let crep_prog_to_display_def,crep_prog_to_display_ind = define_guess_clauses
  [`(crep_prog_to_display crep_Skip = empty_item (implode "skip")) /\
    (crep_prog_to_display (crep_ShMem mop v e) =
         let prefix = (match mop with asm_Load -> [display_String (implode
             "load"); display_String (implode "word")]
                       | asm_Load8 -> [display_String (implode "load");
                           display_String (implode "byte")]
                       | asm_Load16 -> [display_String (implode "load");
                           display_String (implode "word16")]
                       | asm_Load32 -> [display_String (implode "load");
                           display_String (implode "word32")]
                       | asm_Store -> [display_String (implode "store");
                           display_String (implode "word")]
                       | asm_Store8 -> [display_String (implode "store");
                           display_String (implode "byte")]
                       | asm_Store16 -> [display_String (implode "store");
                           display_String (implode "word16")]
                       | asm_Store32 -> [display_String (implode "store");
                           display_String (implode "word32")]) in
           display_Item NONE (implode "shared_mem")
                (APPEND prefix [num_to_display v; crep_exp_to_display
                    e])) /\
    (crep_prog_to_display (crep_ExtCall f e1 e2 e3 e4) =
         display_Item NONE (implode "ext_call")
              [display_String f;
               num_to_display e1;
               num_to_display e2;
               num_to_display e3;
               num_to_display e4]) /\
    (crep_prog_to_display (crep_StoreGlob w e) =
         display_Item NONE (implode "store_glob")
              [word_to_display w;
               crep_exp_to_display e]) /\
    (crep_prog_to_display (crep_If e p1 p2) =
         display_Item NONE (implode "if")
              [crep_exp_to_display e;
               crep_prog_to_display p1;
               crep_prog_to_display p2]) /\
    (crep_prog_to_display (crep_While e p) =
         display_Item NONE (implode "while")
              [crep_exp_to_display e;
               crep_prog_to_display p]) /\
    (crep_prog_to_display (crep_Dec n e p) =
         display_Item NONE (implode "dec")
              [display_Tuple [num_to_display n; display_String (implode
                  ":="); crep_exp_to_display e];
               crep_prog_to_display p]) /\
    (crep_prog_to_display (crep_Assign n exp) =
         display_Tuple [num_to_display n;
                display_String (implode ":=");
                crep_exp_to_display exp]) /\
    (crep_prog_to_display (crep_Primitive lhss pop rhss) =
         display_Tuple [display_Tuple (MAP num_to_display lhss);
                display_String (implode ":=");
                insert_es (primop_to_display pop) (MAP num_to_display
                    rhss)]) /\
    (crep_prog_to_display crep_Tick = empty_item (implode "tick")) /\
    (crep_prog_to_display (crep_Return es) =
         display_Item NONE (implode "return") (MAP crep_exp_to_display
             es)) /\
    (crep_prog_to_display (crep_Seq prog1 prog2) =
        (let xs = append (misc_Append (crep_seqs prog1) (crep_seqs prog2))
            in
           separate_lines (implode "seq") (MAP crep_prog_to_display
               xs))) /\
    (crep_prog_to_display (crep_Call ret_opt f args) =
         match ret_opt with NONE ->
             display_Item NONE (implode "tail_call")
                  [display_String f;
                   display_Tuple (MAP crep_exp_to_display args)]
         | SOME ([],handler) ->
             display_Item NONE (implode "call")
                  [display_String f;
                   display_Tuple (MAP crep_exp_to_display args);
                   crep_prog_to_display_handler handler]
         | SOME (vs,handler) ->
             display_Tuple [display_Tuple (MAP num_to_display vs);
                    display_String (implode ":=");
                    display_Item NONE (implode "call")
                         [display_String f;
                          display_Tuple (MAP crep_exp_to_display args);
                          crep_prog_to_display_handler handler]]) /\
    (crep_prog_to_display_handler NONE = empty_item (implode "no_handler")) /\
    (crep_prog_to_display_handler (SOME (w,p)) =
        display_Item NONE (implode "handler")
          [display_Tuple [word_to_display w; crep_prog_to_display p]])`;
   `(crep_prog_to_display (crep_Store e1 e2) = display_Tuple
        [display_String (implode "mem"); crep_exp_to_display e1;
         display_String (implode ":="); crep_exp_to_display e2]) /\
    (crep_prog_to_display (crep_Store32 e1 e2) = display_Tuple
        [display_String (implode "mem"); crep_exp_to_display e1;
         display_String (implode ":="); display_String (implode
             "32bit"); crep_exp_to_display e2]) /\
    (crep_prog_to_display (crep_StoreByte e1 e2) = display_Tuple
        [display_String (implode "mem"); crep_exp_to_display e1;
         display_String (implode ":="); display_String (implode
             "byte"); crep_exp_to_display e2]) /\
    (crep_prog_to_display (crep_Break n) = item_with_num (implode "break") n)
      /\
    (crep_prog_to_display (crep_Continue n) = item_with_num (implode
    "continue") n) /\
    (crep_prog_to_display (crep_Raise w) =
         item_with_word (implode "raise") w)`];;

let crep_fun_to_display_def = new_definition
  `crep_fun_to_display (nm,args,body) =
     display_Tuple
       [display_String (implode "func"); display_String nm;
        display_Tuple (MAP num_to_display args);
        crep_prog_to_display body]`;;

let crep_to_strs_def = new_definition
  `crep_to_strs xs =
     map_to_append
       (str_tree_to_strs (implode "\n\n") o display_to_str_tree o
         crep_fun_to_display) xs`;;

(* loop *)

let loop_exp_to_display_def,loop_exp_to_display_ind = define_guess
  `(loop_exp_to_display (loop_Const v) = item_with_word (implode "Const") v) /\
   (loop_exp_to_display (loop_Var n) = item_with_num (implode "Var") n) /\
   (loop_exp_to_display loop_BaseAddr = display_Item NONE (implode
    "BaseAddr") []) /\
   (loop_exp_to_display loop_TopAddr = display_Item NONE (implode
    "TopAddr") []) /\
   (loop_exp_to_display (loop_Lookup st) = item_with_word (implode
    "Lookup") st) /\
   (loop_exp_to_display (loop_Load exp2) = display_Item NONE (implode
    "MemLoad") [loop_exp_to_display exp2]) /\
   (loop_exp_to_display (loop_Op bop exs) = display_Item NONE (implode "Op") (
        CONS (asm_binop_to_display bop) (MAP loop_exp_to_display exs))) /\
   (loop_exp_to_display (loop_Shift sh exp exp') = display_Item NONE (implode
    "Shift") [
      shift_to_display sh;
      loop_exp_to_display exp;
      loop_exp_to_display exp'])`;;

let loop_seqs_def,loop_seqs_ind = define_guess
  `loop_seqs z =
     match z with loop_Seq x y -> misc_Append (loop_seqs x) (loop_seqs y)
     | _ -> display_List [z]`;;

(* [local] *)
let MEM_append_loop_seqs = prove
 (`!prog1 a.
     MEM a (append (loop_seqs prog1)) ==>
     lab_prog_size ARB a <= lab_prog_size ARB prog1`,
  CHEAT_TAC);;

(* the clauses in two quotations: a is loop_arith and ((num list # num_set)
   option), which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL (_,p) -> loop_prog_size ARB p
                | INR (_,p) -> option_size (\(a,b,c,d).
                  a + lab_prog_size ARB b + lab_prog_size ARB c + spt_size
                    1_size d) p)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 pan_passesScript.sml:633-644: the tactic that proves the termination *)
let loop_prog_to_display_def,loop_prog_to_display_ind = define_guess_clauses
  [`(loop_prog_to_display ns loop_Skip = empty_item (implode "skip")) /\
    (loop_prog_to_display ns (loop_Arith a) =
        match a with LLongMul n1 n2 n3 n4 ->
            item_with_nums (implode "long_mul") [n1; n2; n3; n4]
        | LLongDiv n1 n2 n3 n4 n5 ->
            item_with_nums (implode "long_div") [n1; n2; n3; n4; n5]
        | LDiv n1 n2 n3 ->
            item_with_nums (implode "div") [n1; n2; n3]) /\
    (loop_prog_to_display ns (loop_Assign n exp) =
         display_Tuple [num_to_display n;
                display_String (implode ":=");
                loop_exp_to_display exp]) /\
    (loop_prog_to_display ns (loop_Primitive lhss pop rhss) =
         display_Tuple [display_Tuple (MAP num_to_display lhss);
                display_String (implode ":=");
                insert_es (primop_to_display pop) (MAP num_to_display
                    rhss)]) /\
    (loop_prog_to_display ns (loop_SetGlobal w exp) =
         display_Item NONE (implode "set_global")
              [word_to_display w;
               loop_exp_to_display exp]) /\
    (loop_prog_to_display ns (loop_Seq prog1 prog2) =
        (let xs = append (misc_Append (loop_seqs prog1) (loop_seqs prog2))
            in
           separate_lines (implode "seq") (MAP (loop_prog_to_display
               ns) xs))) /\
    (loop_prog_to_display ns (loop_FFI nm n1 n2 n3 n4 ms) =
        display_Item NONE (implode "ffi") (
            APPEND (CONS (string_imp nm) (MAP num_to_display [n1; n2;
                n3; n4])) [num_set_to_display ms])) /\
    (loop_prog_to_display ns (loop_Raise n) = item_with_num (implode
    "raise") n) /\
    (loop_prog_to_display ns (loop_Return ns0) = item_with_nums (implode
    "return") ns0) /\
    (loop_prog_to_display ns loop_Tick = empty_item (implode "tick")) /\
    (loop_prog_to_display ns (loop_Break n) = item_with_num (implode
    "break") n) /\
    (loop_prog_to_display ns (loop_Continue n) = item_with_num (implode
    "continue") n) /\
    (loop_prog_to_display ns loop_Fail = empty_item (implode "fail")) /\
    (loop_prog_to_display ns (loop_Load32 n1 n2) =
        item_with_nums (implode "load_32") [n1; n2]) /\
    (loop_prog_to_display ns (loop_LoadByte n1 n2) =
        item_with_nums (implode "load_byte") [n1; n2]) /\
    (loop_prog_to_display ns (loop_Store32 n1 n2) =
        item_with_nums (implode "store_32") [n1; n2]) /\
    (loop_prog_to_display ns (loop_StoreByte n1 n2) =
        item_with_nums (implode "store_byte") [n1; n2]) /\
    (loop_prog_to_display ns (loop_LocValue n1 n2) =
        display_Item NONE (implode "loc_value") [display_String
            (attach_name ns (SOME n1)); num_to_display n2]) /\
    (loop_prog_to_display ns (loop_ShMem mop n e) = display_Tuple
        [display_String (implode "share_mem"); asm_memop_to_display mop;
         num_to_display n; loop_exp_to_display e]) /\
    (loop_prog_to_display ns (loop_If cmp n reg p1 p2 ms) =
        display_Item NONE (implode "if")
          [display_Tuple [asm_cmp_to_display cmp;
                  num_to_display n;
                  asm_reg_imm_to_display reg];
           loop_prog_to_display ns p1; loop_prog_to_display ns p2;
               num_set_to_display ms]) /\
    (loop_prog_to_display ns (loop_Loop ms1 p ms2) =
        display_Item NONE (implode "loop")
          [num_set_to_display ms1;
           loop_prog_to_display ns p;
           num_set_to_display ms2]) /\
    (loop_prog_to_display ns (loop_Mark prog) = display_Item NONE (implode
    "mark")
        [loop_prog_to_display ns prog]) /\
    (loop_prog_to_display ns (loop_Store exp n) = display_Tuple
        [display_String (implode "mem"); loop_exp_to_display exp;
         display_String (implode ":="); num_to_display n]) /\
    (loop_prog_to_display_handler ns NONE = empty_item (implode
    "no_handler")) /\
    (loop_prog_to_display_handler ns (SOME (n1,p1,p2,ms)) =
        display_Item NONE (implode "handler")
          [display_Tuple
             [num_to_display n1;
              loop_prog_to_display ns p1;
              loop_prog_to_display ns p2;
              num_set_to_display ms]])`;
   `loop_prog_to_display ns (loop_Call a b c d) =
         match a with NONE -> display_Item NONE (implode "tail_call")
                     [(\f opt. match opt with NONE -> empty_item (implode
                         "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  (\n. display_String (attach_name ns (SOME n))) b;
                      (\f xs. display_Tuple (MAP f xs)) num_to_display c]
         | SOME (ns0,ms) ->
             display_Tuple [(\f xs. display_Tuple (MAP f xs))
                 num_to_display ns0;
                    display_String (implode ":=");
                    display_Item NONE (implode "call")
                     [(\f opt. match opt with NONE -> empty_item (implode
                         "none")
              | SOME opt' -> display_Item NONE (implode "some") [f opt'])
                  (\n. display_String (attach_name ns (SOME n))) b;
                      (\f xs. display_Tuple (MAP f xs)) num_to_display c;
                      num_set_to_display ms;
                      loop_prog_to_display_handler ns d]]`];;

let loop_fun_to_display_def = new_definition
  `loop_fun_to_display names (n,args,body) =
     display_Tuple
       [display_String (implode "func"); display_String (attach_name names
         (SOME n));
        display_Tuple (MAP num_to_display args);
        loop_prog_to_display names body]`;;

let loop_to_strs_def = new_definition
  `loop_to_strs names xs =
     map_to_append
       (str_tree_to_strs (implode "\n\n") o display_to_str_tree o
         loop_fun_to_display names) xs`;;

let any_pan_prog_pp_def = new_definition
  `any_pan_prog_pp x = match x with pan_passes_Pan p -> pan_to_strs p
     | pan_passes_Crep p -> crep_to_strs p
     | pan_passes_Loop p ns -> loop_to_strs ns p
     | pan_passes_Cake p -> any_prog_pp p`;;

let pan_compile_tap_def = assume_definition
  "declared (no value)"
  `pan_compile_tap asm_conf (c:backend_config) p =
     if tap_config_explore_flag (backend_config_tap_conf c) then
       let (ps,out) = pan_to_target_all asm_conf c p in
         (out,ITLIST (pp_with_title any_pan_prog_pp) ps misc_Nil)
     else (pan_to_target_compile_prog asm_conf c p,misc_Nil)`;;

(* compile_alt *)
let pan_passes_compile_alt = prove
 (`pan_to_target_compile_prog asm_conf c p = FST (pan_compile_tap asm_conf c
  p)`,
  CHEAT_TAC);;

(* and the interface *)
let _ = unhide_overloads ();;
