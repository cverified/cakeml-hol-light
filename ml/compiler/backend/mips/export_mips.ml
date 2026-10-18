(* ======================================================== *)
(*  export_mips: ported from HOL4's
    compiler/backend/mips/export_mipsScript.sml  *)
(* ======================================================== *)

(*
  Define the format of the compiler-generated .S file for MIPS
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/stackLang.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/semanticPrimitives.ml";;
needs "semantics/typeSystem.ml";;

(*
CakeML expects 4 arguments in order:

a0 - entry address i.e., the address of cake_main
a1 - first address of heap
a2 - first address of stack
a3 - first address past the stack

In addition, the first address on the heap should store the address of
  cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
let startup_def = cake_define
  `export_mips_startup ret pk =
     SmartAppend (misc_List
       [(implode "\n");
        (implode "#### Start up code\n");
        (implode "     .text\n");
        (implode "     .p2align 3\n");
        (implode "     .globl  cdecl(cml_main)\n");
        (implode "     .globl  cdecl(cml_heap)\n");
        (implode "     .globl  cdecl(cml_stack)\n");
        (implode "     .globl  cdecl(cml_stackend)\n");
        (implode "     .type   cml_main, function\n");
        (implode "cdecl(cml_main):\n");
        (implode
          ("     dla     $a0,cake_main           # arg1: entry" ++
          " address\n"));
        (implode
          ("     ld      $a1,cdecl(cml_heap)     # arg2: first" ++
          " address of heap\n"))])
     (SmartAppend (misc_List
       (if ~pk then
         [(implode "     dla     $t0,cake_bitmaps\n");
          (implode
            ("     sd      $t0, 0($a1)             # store bitma" ++
            "p pointer\n"))] else []))
     (SmartAppend (misc_List
       [(implode
         ("     ld      $a2,cdecl(cml_stack)    # arg3: first" ++
         " address of stack\n"));
        (implode
          ("     ld      $a3,cdecl(cml_stackend) # arg4: first" ++
          " address past the stack\n"))])
     (SmartAppend (misc_List
       (if ret then
         [(implode "     j       cml_enter\n")] else
         [(implode "     j       cake_main\n")]))
     (misc_List
       [(implode "     nop\n");
        (implode "\n")]))))`;;
hol4_overload "startup" "export_mips_startup";;

let ffi_asm_def = cake_define_list
  [`export_mips_ffi_asm [] = misc_Nil`;
   `export_mips_ffi_asm (ffi :: ffis) =
          SmartAppend (misc_List [
           (implode "cake_ffi"); ffi; (implode ":\n");
           (implode "     dla    $t9,cdecl(ffi"); ffi; (implode
             ")\n");
           (implode "     jr     $t9\n");
           (implode "     .p2align 4\n");
           (implode "\n")]) (export_mips_ffi_asm ffis)`];;
hol4_overload "ffi_asm" "export_mips_ffi_asm";;

(* HOL4 export_mipsScript.sml:66-92: ML code, not ported *)

(* HOL4 export_mipsScript.sml:94-96: ML code, not ported *)

(* HOL4 export_mipsScript.sml:98-99: ML code, not ported *)

(* HOL4 export_mipsScript.sml:101-174: ML code, not ported *)

let export_func_def = cake_define
  `export_mips_export_func appl (name,label,start',len) =
     SmartAppend appl (misc_List
     [(implode "\n     .globl  cdecl("); name; (implode ")\n");
      (implode "     .type   "); name; (implode ", function\n");
      (implode "cdecl("); name; (implode "):\n");
      (implode "     dla     $t0, "); name; (implode "_jmp\n");
      (implode "     j       cake_enter\n");
             name; (implode "_jmp:\n");
      (implode "     j       "); label; (implode "\n")])`;;
hol4_overload "export_func" "export_mips_export_func";;

let export_funcs_def = cake_define
  `export_mips_export_funcs lsyms exp =
     FOLDL export_mips_export_func misc_Nil (FILTER ((C MEM exp) o
       FST) lsyms)`;;
hol4_overload "export_funcs" "export_mips_export_funcs";;

let mips_export_def = cake_define
  `mips_export ffi_names' bytes (data:word64 list) syms exp ret pk =
     (let lsyms = get_sym_labels syms in
     SmartAppend
       (SmartAppend (misc_List preamble)
       (SmartAppend (misc_List (data_section ".quad" ret))
       (SmartAppend (split16 (words_line (implode "\t.quad ")
         word_to_string) data)
       (SmartAppend (misc_List data_buffer)
       (SmartAppend (export_mips_startup ret pk) ((\ret. if ret then
         ((\ret. SmartAppend
     (misc_List (MAP (\n. implode (n ++ "\n"))
      [("#### CakeML FFI interface (each block is 16 bytes " ++
        "long)"); "";
        "     .p2align 4";
        ""])) (SmartAppend
      (export_mips_ffi_asm (REVERSE ffi_names'))
      (misc_List (MAP (\n. implode (n ++ "\n"))
       (["cake_clear:";
        "     dla   $t9,cdecl(cml_exit)";
        "     jr    $t9";
        "     .p2align 4";
        "";
        "cake_exit:"] ++
        (if ret then
          ["     j    cml_return"] else
         ["     dla   $t9,cdecl(cml_exit)";
          "     jr    $t9"]) ++
        ["     .p2align 4";
        "";
        "cake_main:";
        "";
        "#### Generated machine code follows";
        ""]))))) T) else ((\ret. SmartAppend (misc_List (MAP (\n.
          implode (n ++ "\n"))
          [("#### CakeML FFI interface (each block is 16 bytes " ++
          "long)"); ""; "     .p2align 4"; ""])) (SmartAppend
          (export_mips_ffi_asm (REVERSE ffi_names')) (misc_List (MAP
          (\n. implode (n ++ "\n")) (["cake_clear:";
          "     dla   $t9,cdecl(cml_exit)"; "     jr    $t9";
          "     .p2align 4"; ""; "cake_exit:"] ++ (if ret then
          ["     j    cml_return"] else
          ["     dla   $t9,cdecl(cml_exit)"; "     jr    $t9"]) ++
          ["     .p2align 4"; ""; "cake_main:"; "";
          "#### Generated machine code follows"; ""]))))) F)) ret))))))
       (SmartAppend (split16 (words_line (implode "\t.byte ")
         byte_to_string) bytes)
       (SmartAppend (misc_List code_buffer)
       (SmartAppend (emit_symbols lsyms)
       (if ret then
         (SmartAppend ((misc_List (MAP (\n. implode (n ++ "\n"))
     [""; "";
      "cml_enter:"; "     daddiu  $sp, $sp, -72";
      "     sd      $ra, 0($sp)"; "     sd      $s7, 8($sp)";
      "     sd      $s6, 16($sp)";
      "     sd      $s5, 24($sp)"; "     sd      $s4, 32($sp)";
      "     sd      $s3, 40($sp)"; "     sd      $s2, 48($sp)";
      "     sd      $s1, 56($sp)";
      "     sd      $s0, 64($sp)"; "     j       cake_main";
      "     .p2align 4";
      ""; "";
      "cake_enter:";
      "     daddiu  $sp, $sp, -72";
      "     sd      $ra, 0($sp)";
      "     sd      $s7, 8($sp)";
      "     sd      $s6, 16($sp)";
      "     sd      $s5, 24($sp)";
      "     sd      $s4, 32($sp)";
      "     sd      $s3, 40($sp)";
      "     sd      $s2, 48($sp)";
      "     sd      $s1, 56($sp)";
      "     sd      $s0, 64($sp)";
      "     dla     $t1, can_enter";
      "     ld      $t2, 0($t1)";
      "     beq     $t2, $zero, cake_err3";
      "     sd      $zero, 0($t1)";
      "     dla     $t1, ret_base";
      "     ld      $s7, 0($t1)";
      "     dla     $t1, ret_stack";
      "     ld      $s5, 0($t1)";
      "     dla     $t1, ret_stackend";
      "     ld      $s6, 0($t1)";
      "     dla     $ra, cake_return";
      "     jr      $t0";
      "     .p2align 4";
      ""; "";
      "cml_return:";
      "     dla     $t1, ret_base";
      "     sd      $s7, 0($t1)";
      "     dla     $t1, ret_stack";
      "     sd      $s5, 0($t1)";
      "     dla     $t1, ret_stackend";
      "     sd      $s6, 0($t1)";
      "";
      "cake_return:";
      "     dla     $t1, can_enter";
      "     li      $t2, 1";
      "     sd      $t2, 0($t1)";
      "     move    $v0, $a0";
      "     ld      $s0, 64($sp)";
      "     ld      $s1, 56($sp)";
      "     ld      $s2, 48($sp)";
      "     ld      $s3, 40($sp)";
      "     ld      $s4, 32($sp)";
      "     ld      $s5, 24($sp)";
      "     ld      $s6, 16($sp)";
      "     ld      $s7, 8($sp)";
      "     ld      $ra, 0($sp)";
      "     daddiu  $sp, $sp, 72";
      "     jr      $ra";
      "     .p2align 4";
      ""; "";
      "cake_err3:";
      "     li      $a0, 3";
      "     dla     $t9,cdecl(cml_err)";
      "     jr      $t9";
      "     .p2align 4";
      ""]))) (export_mips_export_funcs lsyms exp)) else misc_List
        [])))))`;;
