(* ======================================================== *)
(*  compiler64Prog: ported from HOL4's
    compiler/bootstrap/translation/compiler64ProgScript.sml
    A definition theory, with 10 definitions, 1 datatype and 12
    theorems.  Needed by 6 files of the port.  *)
(* ======================================================== *)

(*
  Finish translation of the 64-bit version of the compiler.
*)

needs "basis/basis_ffi.ml";;
needs "basis/pure/mlstring.ml";;
needs "candle/standard/monadic/holKernel.ml";;
needs "characteristic/cfApp.ml";;
needs "characteristic/cfFFIType.ml";;
needs "characteristic/cfHeapsBase.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/bootstrap/translation/mipsProg.ml";;
needs "compiler/compiler.ml";;
needs "compiler/parsing/cmlParse.ml";;
needs "lib/pegexec.ml";;
needs "semantics/lexer_fun.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/evaluate_dec.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compiler64Prog"
  ["basis_ffi"; "cf"; "compiler"; "export"; "mipsProg"; "ml_translator"];;

(* HOL4 compiler64ProgScript.sml:10-14: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:18: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:20-21: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:23-24: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:28: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:30: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:32-35: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:37: ML code, not ported *)

(* OPT_MMAP_eq_MAP[local] *)
let compiler64Prog_OPT_MMAP_eq_MAP = prove
 (`OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs`,
  CHEAT_TAC);;

(* move recursion out of OPT_MMAP to aid the translator *)
(* HOL4 compiler64ProgScript.sml:46-49: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:51-59: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:61-66: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:68-77: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:79-83: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:85: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:87-88: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:90-100: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:102-108: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:110-112: ML code, not ported *)

(* the right hand side is the one that the ML of the source
   computes, computed the same way *)
let max_heap_limit_64_def = new_definition
  (cake_def_of "max_heap_limit_64" ["c"]
   (rhs (concl (SIMP_RULE [word_shift_def] (SPEC_ALL (INST_TYPE
     [`:64`,`:A`] max_heap_limit_def))))));;


(* HOL4 compiler64ProgScript.sml:122: ML code, not ported *)

let max_heap_limit_64_thm = prove
 (`max_heap_limit (:64) = max_heap_limit_64`,
  CHEAT_TAC);;

(* HOL4 compiler64ProgScript.sml:130: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:132-135: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:137: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:139-140: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:142: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:144: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:146-149: ML code, not ported *)

(* backend_passes_to_bvi_all_side[local] *)
let compiler64Prog_backend_passes_to_bvi_all_side = prove
 (`backend_passes_to_bvi_all_side c p`,
  CHEAT_TAC);;

(* HOL4 compiler64ProgScript.sml:159: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:161: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:163: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:165-166: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:168-169: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:171-172: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:174: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:176: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:178-179: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:181: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:183-184: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:186-188: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:190-192: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:194-196: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:198-199: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:201-203: ML code, not ported *)
(* lem[local] *)
let compiler64Prog_lem = prove
 (`dimindex (:64) = 64`,
  CHEAT_TAC);;
(* HOL4 compiler64ProgScript.sml:209-212: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:214-227: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:229: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:231-233: ML code, not ported *)

(* exportTheory *)
(* TODO: exportTheory functions that don't depend on the word size
   should probably be moved up to to_dataProg or something*)
(* HOL4 compiler64ProgScript.sml:238-244: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:246-250: a theorem that HOL4 states as the
   value of an ML expression: export_byte_to_string_side_def *)

(* HOL4 compiler64ProgScript.sml:252-255: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:257: code that the source has in a comment *)

(* TODO: maybe do this directly to the definition of data_section *)
(* HOL4 compiler64ProgScript.sml:260-276: ML code, not ported *)
(* -- *)

(* HOL4 compiler64ProgScript.sml:279-281: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:283: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:285: ML code, not ported *)
(* -- *)

(* compilerTheory *)

(* HOL4 compiler64ProgScript.sml:290: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:292: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:294-298: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:300-301: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:303-304: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:306: ML code, not ported *)

(* Compiler interface in compilerTheory
  TODO: some of these should be moved up, see comment above on exportScript
 *)
(* HOL4 compiler64ProgScript.sml:311: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:313-314: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:316-320: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:322: ML code, not ported *)

(* comma_tokens treats strings as char lists so we switch modes temporarily *)
(* HOL4 compiler64ProgScript.sml:325-326: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:328-338: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:340: ML code, not ported *)

(* Translations for each 64-bit target
  Note: ffi_asm is translated multiple times...
 *)

(* HOL4 compiler64ProgScript.sml:346: ML code, not ported *)

(* x64 *)
(* HOL4 compiler64ProgScript.sml:349-358: ML code, not ported *)

(* riscv *)
(* HOL4 compiler64ProgScript.sml:361-369: ML code, not ported *)

(* mips *)
(* HOL4 compiler64ProgScript.sml:372-380: ML code, not ported *)

(* arm8 *)
(* HOL4 compiler64ProgScript.sml:383-391: ML code, not ported *)

(* Leave the module now, so that key things are available in the toplevel
   namespace for main. *)
(* HOL4 compiler64ProgScript.sml:395: ML code, not ported *)

(* Rest of the translation *)
(* HOL4 compiler64ProgScript.sml:398-400: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:402-406: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:408: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:410: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:412-414: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:416: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:418: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:420: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:422-424: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:426-430: ML code, not ported *)

let compiler64Prog_nonzero_exit_code_for_error_msg_def = new_definition
  `compiler64Prog_nonzero_exit_code_for_error_msg e =
   if is_error_msg e then
   (let a = empty_ffi (implode "nonzero_exit") in
   force_out_of_memory_error one)
   else one`;;

(* HOL4 compiler64ProgScript.sml:440-441: ML code, not ported *)

(* incremental compiler *)

let compiler_for_eval_def = new_definition
  `compiler_for_eval = compile_inc_progs_for_eval x64_config`;;

(* [local] *)
let upper_w2w_eq_I = prove
 (`upper_w2w = (I:word64->word64)`,
  CHEAT_TAC);;

(* HOL4 compiler64ProgScript.sml:455-464: the ML values that the definitions
   below antiquote *)

(* HOL4 compiler64ProgScript.sml:466-470: ML code, not ported *)

(* fun eval_prim env s1 decs s2 bs ws = Eval [env,s1,decs,s2,bs,ws] *)
(* HOL4 compiler64ProgScript.sml:473-479: ML code, not ported *)

let eval_res_INDUCT,eval_res_RECURSION = define_datatype
  "eval_res =
     Compile_error ('a)
   | Eval_result ('b) ('c)
   | Eval_exn ('d) ('e)";;

(* HOL4 compiler64ProgScript.sml:485: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:487-496: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:498-502: ML code, not ported *)

let report_exn_dec_def = new_definition
  `report_exn_dec = exn_msg_dec`;;

(* HOL4 compiler64ProgScript.sml:508-509: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:511-516: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:518-520: ML code, not ported *)

let report_error_dec_def = new_definition
  `report_error_dec = error_msg_dec`;;

(* HOL4 compiler64ProgScript.sml:526-527: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:529-533: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:535-536: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:538-539: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:541-542: ML code, not ported *)
(* input_str is passed in here only for error reporting purposes *)
(* HOL4 compiler64ProgScript.sml:544-546: ML code, not ported *)
    (* here safe_decs are guaranteed to not crash;
         the last declaration of safe_decs calls !Repl.readNextString *)
(* HOL4 compiler64ProgScript.sml:549-553: ML code, not ported *)
        (* check whether the program that ran has loaded in new input *)
(* HOL4 compiler64ProgScript.sml:555-556: ML code, not ported *)
            (* if there is new input: parse the input and recurse *)
(* HOL4 compiler64ProgScript.sml:558-562: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:564-565: ML code, not ported *)

let parse_cakeml_syntax_def = new_definition
  `parse_cakeml_syntax input =
   match parse_prog (lexer_fun (explode input)) with peg_Success _ x _ ->
     sum_INR x
   | peg_Failure l _ -> sum_INL (strcat (implode "Parsing failed at ")
     (locs_to_string input (SOME l)))`;;

let parse_ocaml_syntax_def = new_definition
  `parse_ocaml_syntax input =
   match caml_parser_run (explode input) with sum_INR res -> sum_INR res
   | sum_INL (l,err) -> sum_INL
                    (strcat (strcat err (implode "\nParsing failed at "))
                      (locs_to_string input (SOME l)))`;;

let select_parse_def = new_definition
  `select_parse cl =
   if MEMBER (implode "--candle") cl then parse_ocaml_syntax
   else parse_cakeml_syntax`;;

(* HOL4 compiler64ProgScript.sml:589-592: ML code, not ported *)

let init_next_string_def = new_definition
  `init_next_string cl = if ag32_MEM (implode "--candle") cl then (implode
  "candle") else (implode "")`;;

(* HOL4 compiler64ProgScript.sml:598-599: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:601-614: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:616-624: ML code, not ported *)

let has_repl_flag_def = new_definition
  `has_repl_flag cl <=> ag32_MEM (implode "--repl") cl \/ ag32_MEM (implode
  "--candle") cl`;;

(* HOL4 compiler64ProgScript.sml:630-631: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:633: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:635-655: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:657: ML code, not ported *)

(* main_spec *)
let compiler64Prog_main_spec = prove
 (`~(has_repl_flag (TL cl)) /\ IS_SOME (stdin_content fs) ==>
   app (p:('ffi->(mlstring,ffi)fmap)#(mlstring list#(mlstring->word8
     list->word8 list->ffi->(ffi cfHeapsBase_ffi_result) option)) list) main_v
       [semanticPrimitives_Conv NONE []] (STDIO fs * COMMANDLINE cl)
       (POSTv (\uv.
        &(UNIT_TYPE one uv) * STDIO (full_compile_64 (TL cl) (get_stdin
          fs) fs) * COMMANDLINE cl))`,
  CHEAT_TAC);;

(* main_whole_prog_spec *)
let compiler64Prog_main_whole_prog_spec = prove
 (`~(has_repl_flag (TL cl)) /\ IS_SOME (stdin_content fs) ==>
   whole_prog_spec main_v cl fs NONE
                   ((=) (full_compile_64 (TL cl) (get_stdin fs) fs))`,
  CHEAT_TAC);;

(* dec_sides[local] *)
let compiler64Prog_dec_sides = prove
 (`(peg_v_side <=> T) /\
   (peg_longv_side <=> T) /\
   (peg_uqconstructorname_side <=> T) /\
   (cmlpeg_side <=> T)`,
  CHEAT_TAC);;

(* HOL4 compiler64ProgScript.sml:821-822: ML code, not ported *)

let semantics_compiler64_prog = prove
 (`~(has_repl_flag (TL cl)) /\ IS_SOME (stdin_content fs) /\ wfcl cl /\ wfFS fs
  /\
   STD_streams fs ==>
   (?io_events'.
     semantics_dec_list
       (semanticPrimitives_state_eval_state_fupd (K (SOME (EvalDecs
         (eval_decs_state_env_id_counter_fupd (K (0,0,1)) eval_state_var))))
         (ml_prog_init_state
         (basis_ffi ext cl fs)))
       init_env compiler64_prog (ffi_Terminate ffi_Success io_events') /\
     extract_fs ext (cl,fs) io_events' =
       SOME (full_compile_64 (TL cl) (get_stdin fs) fs))`,
  CHEAT_TAC);;

(* saving a tidied up final theorem *)

(* HOL4 compiler64ProgScript.sml:843: ML code, not ported *)
  (* |> ml_progLib.clean_state *)
(* HOL4 compiler64ProgScript.sml:845-847: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:849-855: a theorem whose statement the port
   cannot state yet: BUTLAST_compiler64_prog *)

(* HOL4 compiler64ProgScript.sml:857-862: ML code, not ported *)

(* HOL4 compiler64ProgScript.sml:864: a theorem that HOL4 states as the
   value of an ML expression: Decls_FRONT_compiler64_prog *)

(* HOL4 compiler64ProgScript.sml:866-867: a theorem that HOL4 states as the
   value of an ML expression: LAST_compiler64_prog *)

(* HOL4 compiler64ProgScript.sml:869: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
