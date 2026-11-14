(* ======================================================== *)
(*  export_arm8: ported from HOL4's
    compiler/backend/arm8/export_arm8Script.sml
    A definition theory, with 5 definitions and no theorems.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the format of the compiler-generated .S file for ARMv8
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "lib/bitstring.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "export_arm8"
  ["export"];;

(*
CakeML expects 4 arguments in order:

x0 - entry address i.e., the address of cake_main
x1 - first address of heap
x2 - first address of stack
x3 - first address past the stack

In addition, the first address on the heap should store the address of cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
let export_arm8_startup_def = new_definition
  `export_arm8_startup ret pk =
     SmartAppend (misc_List
       [(implode "\n");
        (implode "/* Start up code */\n");
        (implode "\n");
        (implode "     .text\n");
        (implode "     .p2align 3\n");
        (implode "     .globl  cdecl(cml_main)\n");
        (implode "     .globl  cdecl(cml_heap)\n");
        (implode "     .globl  cdecl(cml_stack)\n");
        (implode "     .globl  cdecl(cml_stackend)\n");
        (implode "#ifndef __APPLE__\n");
        (implode "     .type   cml_main, function\n");
        (implode "#endif\n");
        (implode "\n");
        (implode ".macro _ldrel reg sym\n");
        (implode "#ifdef __APPLE__\n");
        (implode "adrp \\reg, \\sym@PAGE\n");
        (implode "add  \\reg, \\reg, \\sym@PAGEOFF\n");
        (implode "#else\n");
        (implode "adrp \\reg, \\sym\n");
        (implode "add  \\reg, \\reg, :lo12:\\sym\n");
        (implode "#endif\n");
        (implode ".endm\n");
        (implode "\n");
        (implode "cdecl(cml_main):\n");
        (implode (APPEND
          "     _ldrel x0, cake_main            /* arg1: entr"
          "y address */\n"));
        (implode (APPEND
          "     _ldrel x1, cdecl(cml_heap)      /* arg2: firs"
          "t address of heap */\n"));
        (implode "     ldr    x1,[x1]\n")])
     (SmartAppend (misc_List
       (if ~pk then
         [(implode "     _ldrel x2, cake_bitmaps\n");
          (implode (APPEND
            "     str    x2,[x1]                  /* store bitm"
            "ap pointer */\n"))] else []))
     (SmartAppend (misc_List
       [(implode (APPEND
         "     _ldrel x2, cdecl(cml_stack)     /* arg3: firs"
         "t address of stack */\n"));
        (implode "     ldr    x2,[x2]\n");
        (implode (APPEND
          "     _ldrel x3, cdecl(cml_stackend)  /* arg4: firs"
          "t address past the stack */\n"));
        (implode "     ldr    x3,[x3]\n")])
     (SmartAppend (misc_List
       (if ret then
         [(implode "     b      cml_enter\n")] else
         [(implode "     b      cake_main\n")]))
     (misc_List
       [(implode "     .ltorg\n");
        (implode "\n")]))))`;;

let export_arm8_ffi_asm_def,export_arm8_ffi_asm_ind = define_rec
  [`export_arm8_ffi_asm [] = misc_Nil`;
   `export_arm8_ffi_asm (CONS ffi ffis) =
          SmartAppend (misc_List [
           (implode "cake_ffi"); ffi; (implode ":\n");
           (implode "     b     cdecl(ffi"); ffi; (implode ")\n");
           (implode "     .p2align 4\n");
           (implode "\n")]) (export_arm8_ffi_asm ffis)`];;

(* HOL4 export_arm8Script.sml:82-106: the ML values that the
   definitions below antiquote *)

(* HOL4 export_arm8Script.sml:108-110: the ML values that the
   definitions below antiquote *)

(* HOL4 export_arm8Script.sml:112-113: the ML values that the
   definitions below antiquote *)

(* HOL4 export_arm8Script.sml:115-193: the ML values that the
   definitions below antiquote *)

let export_arm8_export_func_def = new_definition
  `export_arm8_export_func appl (name,label,start',len) =
     SmartAppend appl (misc_List
     [(implode "\n    .globl cdecl("); name; (implode ")\n");
      (implode "#ifndef __APPLE__\n");
      (implode "     .type   "); name; (implode ", function\n");
      (implode "#endif\n");
      (implode "cdecl("); name; (implode "):\n");
      (implode "     _ldrel x10, "); name; (implode "_jmp\n");
      (implode "     b      cake_enter\n");
             name; (implode "_jmp:\n");
      (implode "     b      "); label; (implode "\n")])`;;

let export_arm8_export_funcs_def = new_definition
  `export_arm8_export_funcs lsyms exp =
     FOLDL export_arm8_export_func misc_Nil (FILTER ((C MEM exp) o
       FST) lsyms)`;;

let arm8_export_def = new_definition
  `arm8_export ffi_names' bytes (data:word64 list) syms exp ret pk =
     (let lsyms = get_sym_labels syms in
     SmartAppend
       (SmartAppend (misc_List preamble)
       (SmartAppend (misc_List (data_section ".quad" ret))
       (SmartAppend (split16 (words_line (implode "\t.quad ")
         word_to_string) data)
       (SmartAppend (misc_List data_buffer)
       (SmartAppend (export_arm8_startup ret pk) ((\ret. if ret then
         ((\ret. SmartAppend
     (misc_List (MAP (\n. implode (APPEND n "\n"))
      [(APPEND "/* CakeML FFI interface (each block is 16 bytes lo"
        "ng) */"); "";
        "     .p2align 4";
        ""])) (SmartAppend
      (export_arm8_ffi_asm (REVERSE ffi_names')) (misc_List (MAP (\n.
        implode (APPEND n "\n"))
       (APPEND (APPEND ["cake_clear:";
        "     b   cdecl(cml_exit)";
        "     .p2align 4";
        "";
        "cake_exit:"]
        (if ret then
          ["     b   cml_return"] else
          ["     b   cdecl(cml_exit)"]))
        ["     .p2align 4";
        "";
        "cake_main:";
        "";
        "/* Generated machine code follows */";
        ""]))))) T) else ((\ret. SmartAppend (misc_List (MAP (\n.
          implode (APPEND n "\n")) [(APPEND
          "/* CakeML FFI interface (each block is 16 bytes lo"
          "ng) */"); ""; "     .p2align 4"; ""])) (SmartAppend
          (export_arm8_ffi_asm (REVERSE ffi_names')) (misc_List (MAP
          (\n. implode (APPEND n "\n")) (APPEND (APPEND ["cake_clear:";
          "     b   cdecl(cml_exit)"; "     .p2align 4"; "";
          "cake_exit:"] (if ret then ["     b   cml_return"] else
          ["     b   cdecl(cml_exit)"])) ["     .p2align 4"; "";
          "cake_main:"; ""; "/* Generated machine code follows */";
          ""]))))) F)) ret))))))
       (SmartAppend (split16 (words_line (implode "\t.byte ")
         byte_to_string) bytes) (SmartAppend (misc_List code_buffer)
       (SmartAppend (emit_symbols lsyms)
       (if ret then
         (SmartAppend ((misc_List (MAP (\n. implode (APPEND n "\n"))
     [""; "";
      "cml_enter:"; "     str    x30, [sp, #-32]!";
      "     str    x29, [sp, #-32]!";
      "     str    x28, [sp, #-32]!"; "     str    x27, [sp, #-32]!";
      "     str    x26, [sp, #-32]!";
      "     str    x25, [sp, #-32]!";
      "     str    x24, [sp, #-32]!";
      "     str    x23, [sp, #-32]!";
      "     str    x22, [sp, #-32]!";
      "     str    x21, [sp, #-32]!";
      "     str    x20, [sp, #-32]!";
      "     str    x19, [sp, #-32]!";
      "     b      cake_main";
      "     .p2align 4";
      ""; "";
      "cake_enter:";
      "     str    x30, [sp, #-32]!";
      "     str    x29, [sp, #-32]!";
      "     str    x28, [sp, #-32]!";
      "     str    x27, [sp, #-32]!";
      "     str    x26, [sp, #-32]!";
      "     str    x25, [sp, #-32]!";
      "     str    x24, [sp, #-32]!";
      "     str    x23, [sp, #-32]!";
      "     str    x22, [sp, #-32]!";
      "     str    x21, [sp, #-32]!";
      "     str    x20, [sp, #-32]!";
      "     str    x19, [sp, #-32]!";
      "     _ldrel x9, can_enter";
      "     ldr    x11, [x9]";
      "     cbz    x11, cake_err3";
      "     str    xzr, [x9]";
      "     _ldrel x9, ret_base";
      "     ldr    x28, [x9]";
      "     _ldrel x9, ret_stack";
      "     ldr    x25, [x9]";
      "     _ldrel x9, ret_stackend";
      "     ldr    x27, [x9]";
      "     _ldrel x30, cake_return";
      "     br     x10";
      "     .p2align 4";
      ""; "";
      "cml_return:";
      "     _ldrel x9, ret_base";
      "     str    x28, [x9]";
      "     _ldrel x9, ret_stack";
      "     str    x25, [x9]";
      "     _ldrel x9, ret_stackend";
      "     str    x27, [x9]";
      "";
      "cake_return:";
      "     _ldrel x9, can_enter";
      "     mov    x11, #1";
      "     str    x11, [x9]";
      "     mov    x8, x0";
      "     ldr    x19, [sp], #32";
      "     ldr    x20, [sp], #32";
      "     ldr    x21, [sp], #32";
      "     ldr    x22, [sp], #32";
      "     ldr    x23, [sp], #32";
      "     ldr    x24, [sp], #32";
      "     ldr    x25, [sp], #32";
      "     ldr    x26, [sp], #32";
      "     ldr    x27, [sp], #32";
      "     ldr    x28, [sp], #32";
      "     ldr    x29, [sp], #32";
      "     ldr    x30, [sp], #32";
      "     ret";
      "     .p2align 4";
      ""; "";
      "cake_err3:";
      "     mov    x0, #3";
      "     b      cdecl(cml_err)";
      "     .p2align 4";
      ""]))) (export_arm8_export_funcs lsyms exp)) else misc_List
        [])))))`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
