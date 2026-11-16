(* ======================================================== *)
(*  compiler32Prog: ported from HOL4's
    compiler/bootstrap/translation/compiler32ProgScript.sml
    A definition theory, with 2 definitions and 8 theorems.  Needed
    by ag32Bootstrap.ml, ag32BootstrapProof.ml, sexprBootstrap32.ml,
    x64_32Bootstrap.ml and x64_32BootstrapProof.ml.  *)
(* ======================================================== *)

(*
  Finish translation of the 32-bit version of the compiler.
*)

needs "basis/basis_ffi.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/bootstrap/translation/ag32Prog.ml";;
needs "compiler/bootstrap/translation/arm7Prog.ml";;
needs "compiler/compiler.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "translator/evaluate_dec.ml";;
needs "translator/ml_prog.ml";;
needs "translator/ml_translator.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "compiler32Prog"
  ["ag32Prog"; "arm7Prog"; "basis_ffi"; "cf"; "compiler"; "export";
   "ml_translator"];;

(* HOL4 compiler32ProgScript.sml:11-15: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:19-20: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:22: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:26: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:28: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:30-33: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:35: ML code, not ported *)

(* OPT_MMAP_eq_MAP[local] *)
let compiler32Prog_OPT_MMAP_eq_MAP = prove
 (`OPT_MMAP f xs = (OPT_MMAP I o MAP f) xs`,
  CHEAT_TAC);;

(* move recursion out of OPT_MMAP to aid the translator *)
(* HOL4 compiler32ProgScript.sml:44-47: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:49-57: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:59-64: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:66-75: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:77-81: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:83: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:85-86: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:88-98: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:100-106: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:108-110: ML code, not ported *)

(* PORT FAILED: Definition max_heap_limit_32_def: expected ')' but found
   '|>' at 82 *)
(* HOL4 compiler32ProgScript.sml:112-118: the definition *)

(* HOL4 compiler32ProgScript.sml:120: ML code, not ported *)

let max_heap_limit_32_thm = prove
 (`max_heap_limit (:32) = max_heap_limit_32`,
  CHEAT_TAC);;

(* HOL4 compiler32ProgScript.sml:128: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:130-133: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:135: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:137-138: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:140: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:142: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:144-147: ML code, not ported *)

(* [local] *)
let backend_passes_to_bvi_all_side = prove
 (`backend_passes_to_bvi_all_side c p`,
  CHEAT_TAC);;

(* HOL4 compiler32ProgScript.sml:157: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:159: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:161: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:163-164: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:166-167: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:169-170: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:172: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:174: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:176-177: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:179: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:181-182: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:184-186: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:188-190: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:192-194: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:196-197: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:199-201: ML code, not ported *)
(* lem[local] *)
let compiler32Prog_lem = prove
 (`dimindex (:32) = 32`,
  CHEAT_TAC);;
(* HOL4 compiler32ProgScript.sml:207-210: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:212-225: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:227: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:229-231: ML code, not ported *)

(* exportTheory *)
(* TODO: exportTheory functions that don't depend on the word size
   should probably be moved up to to_dataProg or something*)
(* HOL4 compiler32ProgScript.sml:236-242: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:244-248: a theorem that HOL4 states as the
   value of an ML expression: export_byte_to_string_side_def *)

(* HOL4 compiler32ProgScript.sml:250-253: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:255: code that the source has in a comment *)

(* TODO: maybe do this directly to the definition of data_section *)
(* HOL4 compiler32ProgScript.sml:258-274: ML code, not ported *)
(* -- *)

(* HOL4 compiler32ProgScript.sml:277-279: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:281: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:283: ML code, not ported *)
(* -- *)

(* compilerTheory *)

(* HOL4 compiler32ProgScript.sml:288: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:290: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:292-296: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:298-299: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:301-302: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:304: ML code, not ported *)

(* Compiler interface in compilerTheory
  TODO: some of these should be moved up, see comment above on exportScript
*)
(* HOL4 compiler32ProgScript.sml:309: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:311-312: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:314-318: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:320: ML code, not ported *)

(* comma_tokens treats strings as char lists so we switch modes temporarily *)
(* HOL4 compiler32ProgScript.sml:323-324: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:326-336: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:338: ML code, not ported *)

(* Translations for each 32-bit target
  Note: ffi_asm is translated multiple times...
*)

(* HOL4 compiler32ProgScript.sml:344: ML code, not ported *)

(* ag32 *)
(* HOL4 compiler32ProgScript.sml:347-351: ML code, not ported *)

(* arm7 *)
(* HOL4 compiler32ProgScript.sml:354-362: ML code, not ported *)

(* Leave the module now, so that key things are available in the toplevel
   namespace for main. *)
(* HOL4 compiler32ProgScript.sml:366: ML code, not ported *)

(* Rest of the translation *)
(* HOL4 compiler32ProgScript.sml:369-371: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:373: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:375-379: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:381: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:383-385: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:387-391: ML code, not ported *)

let nonzero_exit_code_for_error_msg_def = new_definition
  `compiler32Prog_nonzero_exit_code_for_error_msg e =
     if is_error_msg e then
       (let a = empty_ffi (implode "nonzero_exit") in
          force_out_of_memory_error one)
     else one`;;

(* HOL4 compiler32ProgScript.sml:401-402: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:404: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:406: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:408: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:410-412: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:414: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:416-434: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:436: ML code, not ported *)

(* HOL4 compiler32ProgScript.sml:438-562: a theorem whose statement the port
   cannot state yet: main_spec *)

let main_whole_prog_spec = prove
 (`IS_SOME (stdin_content fs) ==>
    whole_prog_spec main_v cl fs NONE
     ((=) (full_compile_32 (TL cl) (get_stdin fs) fs))`,
  CHEAT_TAC);;

(* [local] *)
let dec_sides = prove
 (`(peg_v_side <=> T) /\
   (peg_longv_side <=> T) /\
   (peg_uqconstructorname_side <=> T) /\
   (cmlpeg_side <=> T)`,
  CHEAT_TAC);;

(* HOL4 compiler32ProgScript.sml:595-596: ML code, not ported *)

let semantics_compiler32_prog = prove
 (`IS_SOME (stdin_content fs) /\ wfcl cl /\ wfFS fs /\ STD_streams fs ==>
   (?io_events.
     semantics_dec_list
       (semanticPrimitives_state_eval_state_fupd (K
          (SOME (EvalDecs (eval_decs_state_env_id_counter_fupd (K (0,0,1))
            eval_state_var)))) (ml_prog_init_state (basis_ffi ext cl fs)))
       init_env compiler32_prog (ffi_Terminate ffi_Success io_events) /\
     extract_fs ext (cl,fs) io_events =
       SOME (full_compile_32 (TL cl) (get_stdin fs) fs))`,
  CHEAT_TAC);;

(* HOL4 compiler32ProgScript.sml:614: ML code, not ported *)

(* and the interface *)
let _ = unhide_overloads ();;
