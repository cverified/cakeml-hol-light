(* ======================================================== *)
(*  pan_to_target: ported from HOL4's
    pancake/pan_to_targetScript.sml
    A definition theory, with 2 definitions and 1 theorem.  Needed
    by compiler.ml, from_pancake32Prog.ml, from_pancake64Prog.ml and
    pan_passes.ml.  *)
(* ======================================================== *)

(*
  Compiler from Pancake to machine code
*)

needs "basis/pure/mllist.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/word_depth.ml";;
needs "compiler/backend/word_to_word.ml";;
needs "lib/sptree.ml";;
needs "pancake/panLang.ml";;
needs "pancake/pan_to_word.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "pan_to_target"
  ["backend"; "mllist"; "pan_to_word"; "word_depth"; "word_to_word"];;

let _ = do_list hide_constant ["prog"];;

(* this file reads the name of a record field as a variable and
   needs the accessors of that field as well, so only these
   pairs come out of the interface *)
let _ = hide_overloads
  ["return","errorLogMonad_return";
   "return","errorMonad_return"];;

let exports_def,exports_ind = define_guess
  `exports x1 =
     match x1 with
       CONS (Function fi) ds ->
      if fun_decl_export fi then CONS (fun_decl_name fi) (exports ds)
      else exports ds
     | CONS _ ds -> exports ds
     | [] -> []`;;

let pan_to_target_compile_prog_def = new_definition
  `pan_to_target_compile_prog asm_conf c prog =
     // Ensure either user-written main or new main that does nothing is first in func list
     (let prog1:('a decl) list = (match SPLITP (\x. match x with
                              Function fi -> fun_decl_name fi = (implode
                                "main")
                              | _ -> F) prog with
                   ([],ys) -> ys
                 | (xs,[]) ->
                              CONS (Function
                              (mk_fun_decl (implode "main") F F []
                                (loop_Return (pan_Const (n2w 0))) pan_One)) xs
                 | (xs,CONS y ys) -> APPEND (CONS y xs) ys) in
     // Compiler passes
     let prog2 = pan_to_word_compile_prog (asm_config_ISA asm_conf) prog1 in
     let (col,prog3) = word_to_word_compile
       (backend_config_word_to_word_conf c) asm_conf prog2 in
     let c = backend_config_word_to_word_conf_fupd (\c.
       word_to_word_config_col_oracle_fupd (K col) c) c in
     // Add user functions to name mapping
     let names = (fromAList (ZIP (sort (<) (MAP FST prog2)) (CONS
                              // func numbers
                              (implode "generated_main")
                              (MAP FST (functions prog1)))):mlstring spt) in
     // Add stubs to name mapping
     let names = sptree_union (fromAList (APPEND (APPEND
       (word_to_stack_stub_names one)
       (stack_alloc_stub_names one)) (stack_remove_stub_names one))) names
         in
     // Add exported functions to
     let c = backend_config_exported_fupd (K (exports prog)) c in
       backend_from_word asm_conf c names prog3)
   // func names`;;

(*  TODO: evaluate max_depth ... (full_call_graph dest (fromAList prog))  *)

(* compile_prog_eq *)
let pan_to_target_compile_prog_eq = prove
 (`pan_to_target_compile_prog asm_conf c prog =
     // Ensure either user-written main or new main that does nothing is first in func list
     let prog1:('a decl) list = (match SPLITP (\x. match x with
                              Function fi -> fun_decl_name fi = (implode
                                "main")
                              | _ -> F) prog with
                   ([],ys) -> ys
                 | (xs,[]) ->
                              CONS (Function
                              (mk_fun_decl (implode "main") F F []
                                (loop_Return (pan_Const (n2w 0))) pan_One)) xs
                 | (xs,CONS y ys) -> APPEND (CONS y xs) ys) in
     // Compiler passes
     let prog2 = pan_to_word_compile_prog (asm_config_ISA asm_conf) prog1 in
     // Add user functions to name mapping
     let names = (fromAList (ZIP (sort (<) (MAP FST prog2)) (CONS
                              // func numbers
                              (implode "generated_main")
                              (MAP FST (functions prog1)))):mlstring spt) in
     // Add stubs to name mapping
     let names = sptree_union (fromAList (APPEND (APPEND
       (word_to_stack_stub_names one)
                 (stack_alloc_stub_names one)) (stack_remove_stub_names
                   one))) names in
     let c = backend_config_exported_fupd (K (exports prog)) c in
       backend_from_word_0 asm_conf c names prog2
   // func names`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["prog"];;

(* and the interface *)
let _ = unhide_overloads ();;
