(* ======================================================== *)
(*  export_arm7: ported from HOL4's
    compiler/backend/arm7/export_arm7Script.sml
    A definition theory, with 5 definitions and no theorems.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the format of the compiler-generated .S file for ARMv7
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "export_arm7"
  ["export"];;

(*
CakeML expects 4 arguments in order:

r0 - entry address i.e., the address of cake_main
r1 - first address of heap
r2 - first address of stack
r3 - first address past the stack

In addition, the first address on the heap should store the address of cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
let export_arm7_startup_def = new_definition
  `export_arm7_startup ret pk =
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
        (implode "     .type   cml_main, function\n");
        (implode "cdecl(cml_main):\n");
        (implode (APPEND
          "     ldr    r0,=cake_main            /* arg1: entr"
          "y address */\n"));
        (implode (APPEND
          "     ldr    r1,=cdecl(cml_heap)      /* arg2: firs"
          "t address of heap */\n"));
        (implode "     ldr    r1,[r1]\n")])
     (SmartAppend (misc_List
       (if ~pk then
         [(implode "     ldr    r2,=cake_bitmaps\n");
          (implode (APPEND
            "     str    r2,[r1]                  /* store bitm"
            "ap pointer */\n"))] else []))
     (SmartAppend (misc_List
       [(implode (APPEND
         "     ldr    r2,=cdecl(cml_stack)     /* arg3: firs"
         "t address of stack */\n"));
        (implode "     ldr    r2,[r2]\n");
        (implode (APPEND
          "     ldr    r3,=cdecl(cml_stackend)  /* arg4: firs"
          "t address past the stack */\n"));
        (implode "     ldr    r3,[r3]\n")])
     (SmartAppend (misc_List
       (if ret then
         [(implode "     b      cml_enter\n")] else
         [(implode "     b      cake_main\n")]))
     (misc_List
       [(implode "     .ltorg\n");
        (implode "\n")]))))`;;
hol4_overload "startup" "export_arm7_startup";;

let export_arm7_ffi_asm_def,export_arm7_ffi_asm_ind = define_rec
  [`export_arm7_ffi_asm [] = misc_Nil`;
   `export_arm7_ffi_asm (CONS ffi ffis) =
          SmartAppend (misc_List [
           (implode "cake_ffi"); ffi; (implode ":\n");
           (implode "     b     cdecl(ffi"); ffi; (implode ")\n");
           (implode "     .p2align 4\n");
           (implode "\n")]) (export_arm7_ffi_asm ffis)`];;
hol4_overload "ffi_asm" "export_arm7_ffi_asm";;

(* HOL4 export_arm7Script.sml:69-93: the ML values that the
   definitions below antiquote *)

(* HOL4 export_arm7Script.sml:95-97: the ML values that the
   definitions below antiquote *)

(* HOL4 export_arm7Script.sml:99-100: the ML values that the
   definitions below antiquote *)

(* HOL4 export_arm7Script.sml:102-149: the ML values that the
   definitions below antiquote *)

let export_arm7_export_func_def = new_definition
  `export_arm7_export_func appl (name,label,start',len) =
     SmartAppend appl (misc_List
     [(implode "\n     .globl  cdecl("); name; (implode ")\n");
      (implode "     .type   "); name; (implode ", function\n");
      (implode "cdecl("); name; (implode "):\n");
      (implode "     push   {r4}\n");
      (implode "     ldr    r4,="); name; (implode "_jmp\n");
      (implode "     b       cake_enter\n");
             name; (implode "_jmp:\n");
      (implode "     b       "); label; (implode "\n")])`;;
hol4_overload "export_func" "export_arm7_export_func";;

let export_arm7_export_funcs_def = new_definition
  `export_arm7_export_funcs lsyms exp =
     FOLDL export_arm7_export_func misc_Nil (FILTER ((C MEM exp) o
       FST) lsyms)`;;
hol4_overload "export_funcs" "export_arm7_export_funcs";;

let arm7_export_def = new_definition
  `arm7_export ffi_names' bytes (data:word32 list) syms exp ret pk =
     (let lsyms = get_sym_labels syms in
     SmartAppend
       (SmartAppend (misc_List preamble)
       (SmartAppend (misc_List (data_section ".long" ret))
       (SmartAppend (split16 (words_line (implode "\t.long ")
         word_to_string) data)
       (SmartAppend (misc_List data_buffer)
       (SmartAppend (export_arm7_startup ret pk) ((\ret. if ret then
         ((\ret. SmartAppend
     (misc_List (MAP (\n. implode (APPEND n "\n"))
      [(APPEND "/* CakeML FFI interface (each block is 16 bytes lo"
        "ng) */"); "";
        "     .p2align 4";
        ""])) (SmartAppend
      (export_arm7_ffi_asm (REVERSE ffi_names')) (misc_List (MAP (\n.
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
          (export_arm7_ffi_asm (REVERSE ffi_names')) (misc_List (MAP
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
      "cml_enter:"; "     push   {r5,r6,r8,r10,r11,lr}";
      "     b      cake_main";
      "     .p2align 4";
      ""; "";
      "cake_enter:";
      "     push   {r5,r6,r8,r10,r11,lr}";
        "     ldr    r5,=can_enter";
      "     ldr    r6, [r5]";
      "     cmp    r6, #0";
      "     beq    cake_err3";
      "     mov    r6, #0";
      "     str    r6, [r5]"; "     ldr    r5,=ret_base";
      "     ldr    r10, [r5]";
      "     ldr    r5,=ret_stack";
      "     ldr    r11, [r5]";
      "     ldr    r5,=ret_stackend";
      "     ldr    r8, [r5]";
      "     ldr    lr,=cake_return";
      "     bx     r4";
      "     .p2align 4";
      ""; "";
      "cml_return:";
      "     ldr    r5,=ret_base";
      "     str    r10, [r5]";
      "     ldr    r5,=ret_stack";
      "     str    r11, [r5]";
      "     ldr    r5,=ret_stackend";
      "     str    r8, [r5]";
      "";
      "cake_return:";
      "     ldr    r5,=can_enter";
      "     mov    r6, #1";
      "     str    r6, [r5]";
      "     pop    {r5,r6,r8,r10,r11,lr}";
      "     pop    {r4}";
      "     bx     lr";
      "     .p2align 4";
      ""; "";
      "cake_err3:";
      "     mov    r0, #3";
      "     b      cdecl(cml_err)";
      "     .p2align 4";
      ""]))) (export_arm7_export_funcs lsyms exp)) else misc_List
        [])))))`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
