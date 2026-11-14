(* ======================================================== *)
(*  export_riscv: ported from HOL4's
    compiler/backend/riscv/export_riscvScript.sml
    A definition theory, with 5 definitions and no theorems.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the format of the compiler-generated .S file for RISC-V
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "export_riscv"
  ["export"];;

(*
CakeML expects 4 arguments in order:

a0 - entry address i.e., the address of cake_main
a1 - first address of heap
a2 - first address of stack
a3 - first address past the stack

In addition, the first address on the heap should store the address of cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
let export_riscv_startup_def = new_definition
  `export_riscv_startup ret pk =
     SmartAppend (misc_List
       [(implode "\n");
        (implode "#### Start up code\n");
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
          "     la      a0,cake_main           # arg1: entry "
          "address\n"));
        (implode (APPEND
          "     ld      a1,cdecl(cml_heap)     # arg2: first "
          "address of heap\n"))])
     (SmartAppend (misc_List
       (if ~pk then
         [(implode "     la      t3,cake_bitmaps\n");
         (implode (APPEND
           "     sd      t3, 0(a1)              # store bitmap"
           " pointer\n"))] else []))
     (SmartAppend (misc_List
       [(implode (APPEND
         "     ld      a2,cdecl(cml_stack)    # arg3: first "
         "address of stack\n"));
        (implode (APPEND
          "     ld      a3,cdecl(cml_stackend) # arg4: first "
          "address past the stack\n"))])
     (SmartAppend (misc_List
       (if ret then
         [(implode "     j       cml_enter\n")] else
         [(implode "     j       cake_main\n")]))
     (misc_List
       [(implode "\n")]))))`;;
hol4_overload "startup" "export_riscv_startup";;

let export_riscv_ffi_asm_def,export_riscv_ffi_asm_ind = define_rec
  [`export_riscv_ffi_asm [] = misc_Nil`;
   `export_riscv_ffi_asm (CONS ffi ffis) =
          SmartAppend (misc_List [
           (implode "cake_ffi"); ffi; (implode ":\n");
           (implode "     tail cdecl(ffi"); ffi; (implode ")\n");
           (implode "     .p2align 4\n");
           (implode "\n")]) (export_riscv_ffi_asm ffis)`];;
hol4_overload "ffi_asm" "export_riscv_ffi_asm";;

(* HOL4 export_riscvScript.sml:65-89: the ML values that the
   definitions below antiquote *)

(* HOL4 export_riscvScript.sml:91-93: the ML values that the
   definitions below antiquote *)

(* HOL4 export_riscvScript.sml:95-96: the ML values that the
   definitions below antiquote *)

(* HOL4 export_riscvScript.sml:98-181: the ML values that the
   definitions below antiquote *)

let export_riscv_export_func_def = new_definition
  `export_riscv_export_func appl (name,label,start',len) =
     SmartAppend appl (misc_List
     [(implode "\n     .globl  cdecl("); name; (implode ")\n");
      (implode "     .type   "); name; (implode ", function\n");
      (implode "cdecl("); name; (implode "):\n");
      (implode "     la      t0, "); name; (implode "_jmp\n");
      (implode "     j       cake_enter\n");
             name; (implode "_jmp:\n");
      (implode "     j       "); label; (implode "\n")])`;;
hol4_overload "export_func" "export_riscv_export_func";;

let export_riscv_export_funcs_def = new_definition
  `export_riscv_export_funcs lsyms exp =
     FOLDL export_riscv_export_func misc_Nil (FILTER ((C MEM exp)
       o FST) lsyms)`;;
hol4_overload "export_funcs" "export_riscv_export_funcs";;

let riscv_export_def = new_definition
  `riscv_export ffi_names' bytes (data:word64 list) syms exp ret pk =
     (let lsyms = get_sym_labels syms in
     SmartAppend
       (SmartAppend (misc_List preamble)
       (SmartAppend (misc_List (data_section ".quad" ret))
       (SmartAppend (split16 (words_line (implode "\t.quad ")
         word_to_string) data)
       (SmartAppend (misc_List data_buffer)
       (SmartAppend (export_riscv_startup ret pk) ((\ret. if ret then
         ((\ret. SmartAppend
     (misc_List (MAP (\n. implode (APPEND n "\n"))
      [(APPEND "#### CakeML FFI interface (each block is 16 bytes "
        "long)");
        "";
        "     .p2align 4"; ""])) (
     SmartAppend
      (export_riscv_ffi_asm (REVERSE ffi_names'))
      (misc_List (MAP (\n. implode (APPEND n "\n"))
       (APPEND (APPEND ["cake_clear:";
        "     tail cdecl(cml_exit)"; "     .p2align 4";
        "";
        "cake_exit:"]
        (if ret then
          ["     j    cml_return"] else
          ["     tail cdecl(cml_exit)"]))
        ["     .p2align 4";
        "";
        "cake_main:";
        "";
        "#### Generated machine code follows";
        ""]))))) T) else ((\ret. SmartAppend (misc_List (MAP (\n.
          implode (APPEND n "\n")) [(APPEND
          "#### CakeML FFI interface (each block is 16 bytes " "long)");
          ""; "     .p2align 4"; ""])) (SmartAppend
          (export_riscv_ffi_asm (REVERSE ffi_names')) (misc_List (MAP
          (\n. implode (APPEND n "\n")) (APPEND (APPEND ["cake_clear:";
          "     tail cdecl(cml_exit)"; "     .p2align 4"; "";
          "cake_exit:"] (if ret then ["     j    cml_return"] else
          ["     tail cdecl(cml_exit)"])) ["     .p2align 4"; "";
          "cake_main:"; ""; "#### Generated machine code follows";
          ""]))))) F)) ret))))))
       (SmartAppend (split16 (words_line (implode "\t.byte ")
         byte_to_string) bytes) (SmartAppend (misc_List code_buffer)
       (SmartAppend (emit_symbols lsyms) (if ret then (SmartAppend
         ((misc_List (MAP (\n. implode (APPEND n "\n"))
     [""; "";
      "cml_enter:";
      "     addi    sp, sp, -104";
      "     sd      ra, 0(sp)";
      "     sd      s11, 8(sp)";
      "     sd      s10, 16(sp)";
      "     sd      s9, 24(sp)";
      "     sd      s8, 32(sp)";
      "     sd      s7, 40(sp)";
      "     sd      s6, 48(sp)"; "     sd      s5, 56(sp)";
      "     sd      s4, 64(sp)";
      "     sd      s3, 72(sp)";
      "     sd      s2, 80(sp)";
      "     sd      s1, 88(sp)"; "     sd      s0, 96(sp)";
      "     j       cake_main";
      "     .p2align 4";
      ""; "";
      "cake_enter:";
      "     addi    sp, sp, -104";
      "     sd      ra, 0(sp)";
      "     sd      s11, 8(sp)";
      "     sd      s10, 16(sp)";
      "     sd      s9, 24(sp)";
      "     sd      s8, 32(sp)";
      "     sd      s7, 40(sp)";
      "     sd      s6, 48(sp)";
      "     sd      s5, 56(sp)";
      "     sd      s4, 64(sp)";
      "     sd      s3, 72(sp)";
      "     sd      s2, 80(sp)";
      "     sd      s1, 88(sp)";
      "     sd      s0, 96(sp)";
      "     la      t1, can_enter";
      "     ld      t2, 0(t1)";
      "     beq     t2, zero, cake_err3";
      "     sd      zero, 0(t1)";
      "     la      t1, ret_base";
      "     ld      s10, 0(t1)";
      "     la      t1, ret_stack";
      "     ld      s8, 0(t1)";
      "     la      t1, ret_stackend";
      "     ld      s9, 0(t1)";
      "     la      ra, cake_return";
      "     jr      t0";
      "     .p2align 4";
      ""; "";
      "cml_return:";
      "     la      t1, ret_base";
      "     sd      s10, 0(t1)";
      "     la      t1, ret_stack";
      "     sd      s8, 0(t1)";
      "     la      t1, ret_stackend";
      "     sd      s9, 0(t1)";
      "";
      "cake_return:";
      "     la      t1, can_enter";
      "     li      t2, 1";
      "     sd      t2, 0(t1)";
      "     ld      s0, 96(sp)";
      "     ld      s1, 88(sp)";
      "     ld      s2, 80(sp)";
      "     ld      s3, 72(sp)";
      "     ld      s4, 64(sp)";
      "     ld      s5, 56(sp)";
      "     ld      s6, 48(sp)";
      "     ld      s7, 40(sp)";
      "     ld      s8, 32(sp)";
      "     ld      s9, 24(sp)";
      "     ld      s10, 16(sp)";
      "     ld      s11, 8(sp)";
      "     ld      ra, 0(sp)";
      "     addi    sp, sp, 104";
      "     ret";
      "     .p2align 4";
      ""; "";
      "cake_err3:";
      "     li      a0, 3";
      "     j       cdecl(cml_err)";
      "     .p2align 4";
      ""]))) (export_riscv_export_funcs lsyms exp)) else misc_List
        [])))))`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
