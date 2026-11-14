(* ======================================================== *)
(*  export_x64: ported from HOL4's
    compiler/backend/x64/export_x64Script.sml
    A definition theory, with 6 definitions and no theorems.  Needed
    by compiler.ml.  *)
(* ======================================================== *)

(*
  Define the format of the compiler-generated .S file for x64
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/export.ml";;
needs "compiler/backend/word_bignum.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "lib/regexp_compiler.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/typeSystem.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "export_x64"
  ["export"];;

(*
CakeML expects 4 arguments in order:

RDI - entry address i.e., the address of cake_main
RSI - first address of heap
RDX - first address of stack
RCX - first address past the stack

In addition, the first address on the heap should store the address of cake_bitmaps

Note: this set up does NOT account for restoring clobbered registers
*)
let startup_def = new_definition
  `export_x64_startup ret pk =
     SmartAppend (misc_List
       [(implode "\n");
        (implode "/* Start up code */\n");
        (implode "\n");
        (implode "     .text\n");
        (implode "     .p2align 12\n");
        (implode "     .globl  cdecl(cake_text_begin)\n");
        (implode "cdecl(cake_text_begin):\n");
        (implode "     .globl  cdecl(cml_main)\n");
        (implode "     .globl  cdecl(cml_heap)\n");
        (implode "     .globl  cdecl(cml_stack)\n");
        (implode "     .globl  cdecl(cml_stackend)\n");
        (implode "#if defined(__APPLE__)\n");
        (implode "\n");
        (implode "#elif defined(__WIN32)\n");
        (implode "     .func   cml_main\n");
        (implode "#else\n");
        (implode "     .type   cml_main, function\n");
        (implode "#endif\n");
        (implode "cdecl(cml_main):\n");
        (implode (APPEND
          "     pushq   %rbp                            # pus"
          "h base pointer\n"));
        (implode (APPEND
          "     movq    %rsp, %rbp                      # sav"
          "e stack pointer\n"));
        (implode (APPEND
          "     leaq    cake_main(%rip), %rdi           # arg"
          "1: entry address\n"));
        (implode (APPEND
          "     movq    cdecl(cml_heap)(%rip), %rsi     # arg"
          "2: first address of heap\n"))])
     (SmartAppend (misc_List
       (if ~pk then
         [(implode "     leaq    cake_bitmaps(%rip), %rax\n");
          (implode (APPEND
            "     movq    %rax, 0(%rsi)                   # sto"
            "re bitmap pointer\n"));
          (implode (APPEND
            "     leaq    cdecl(cake_bitmaps_buffer_begin)(%rip"
            "), %rax\n"));
          (implode (APPEND
            "     movq    %rax, 8(%rsi)                   # sto"
            "re bitmap mutable start pointer\n"));
          (implode (APPEND
            "     leaq    cdecl(cake_bitmaps_buffer_end)(%rip),"
            " %rax\n"));
          (implode (APPEND
            "     movq    %rax, 16(%rsi)                  # sto"
            "re bitmap mutable end pointer\n"));
          (implode (APPEND
            "     leaq    cdecl(cake_codebuffer_begin)(%rip), %"
            "rax\n"));
          (implode (APPEND
            "     movq    %rax, 24(%rsi)                  # sto"
            "re code mutable start pointer\n"));
          (implode (APPEND
            "     leaq    cdecl(cake_codebuffer_end)(%rip), %ra"
            "x\n"));
          (implode (APPEND
            "     movq    %rax, 32(%rsi)                  # sto"
            "re code mutable end pointer\n"))] else []))
     (SmartAppend (misc_List
       [(implode (APPEND
         "     movq    cdecl(cml_stack)(%rip), %rdx    # arg"
         "3: first address of stack\n"));
        (implode (APPEND
          "     movq    cdecl(cml_stackend)(%rip), %rcx # arg"
          "4: first address past the stack\n"))])
     (SmartAppend (misc_List
       (if ret then
         [(implode "     jmp     cml_enter\n")] else
         [(implode "     jmp     cake_main\n")]))
     (misc_List
       [(implode "\n");
        (implode "#if defined(__WIN32)\n");
        (implode "     .endfunc\n");
        (implode "#endif\n")]))))`;;

let ffi_asm_def,ffi_asm_ind = define_rec
  [`export_x64_ffi_asm [] = misc_Nil`;
   `export_x64_ffi_asm (CONS ffi ffis) =
          SmartAppend (misc_List [
           (implode "cake_ffi"); ffi; (implode ":\n");
           (implode "     pushq   %rax\n");
           (implode "     jmp     wcdecl(ffi"); ffi; (implode
             ")\n");
           (implode "     .p2align 4\n");
           (implode "\n")]) (export_x64_ffi_asm ffis)`];;

(* HOL4 export_x64Script.sml:87-115: the ML values that the
   definitions below antiquote *)

(* HOL4 export_x64Script.sml:117-119: the ML values that the
   definitions below antiquote *)

(* HOL4 export_x64Script.sml:121-122: the ML values that the
   definitions below antiquote *)

let windows_ffi_asm_def,windows_ffi_asm_ind = define_rec
  [`windows_ffi_asm [] = misc_Nil`;
   `windows_ffi_asm (CONS ffi ffis) =
          SmartAppend (misc_List [
           (implode "windows_ffi"); ffi; (implode ":\n");
           (implode "     movq    %rcx, %r9\n");
           (implode "     movq    %rdx, %r8\n");
           (implode "     movq    %rsi, %rdx\n");
           (implode "     movq    %rdi, %rcx\n");
           (implode "     jmp     cdecl(ffi"); ffi; (implode ")\n");
           (implode "\n")]) (windows_ffi_asm ffis)`];;

(* HOL4 export_x64Script.sml:137-160: the ML values that the
   definitions below antiquote *)

(* HOL4 export_x64Script.sml:162-164: the ML values that the
   definitions below antiquote *)

(* HOL4 export_x64Script.sml:166-167: the ML values that the
   definitions below antiquote *)

(* HOL4 export_x64Script.sml:169-235: the ML values that the
   definitions below antiquote *)

let export_func_def = new_definition
  `export_x64_export_func appl (name,label,start',len) =
     SmartAppend appl (misc_List
     [(implode "\n    .globl cdecl("); name; (implode ")\n");
      (implode "#if defined(__APPLE__)\n");
      (implode "\n");
      (implode "#elif defined(__WIN32)\n");
      (implode "     .func   cdecl("); name; (implode ")\n");
      (implode "#else\n");
      (implode "     .type   cdecl("); name; (implode
        "), function\n");
      (implode "#endif\n");
      (implode "cdecl("); name; (implode "):\n");
      (implode "     lea     "); name; (implode
        "_jmp(%rip), %r10\n");
      (implode "     jmp     wcml(cake_enter)\n");
             name; (implode "_jmp:\n");
      (implode "     jmp     "); label; (implode "\n");
      (implode "#if defined(__WIN32)\n");
      (implode "     .endfunc\n");
      (implode "#endif\n")])`;;

let export_funcs_def = new_definition
  `export_x64_export_funcs lsyms exp =
     FOLDL export_x64_export_func misc_Nil (FILTER ((C MEM exp) o
       FST) lsyms)`;;

let x64_export_def = new_definition
  `x64_export ffi_names' bytes (data:word64 list) syms exp ret pk =
     (let lsyms = get_sym_labels syms in
     SmartAppend
       (SmartAppend
       (SmartAppend (misc_List preamble)
       (SmartAppend (misc_List (data_section ".quad" ret))
       (SmartAppend (split16 (words_line (implode "\t.quad ")
         word_to_string) data)
       (SmartAppend (misc_List data_buffer)
       (SmartAppend (export_x64_startup ret pk) ((\ret. if ret then
         ((\ret. SmartAppend
     (misc_List (MAP (\n. implode (APPEND n "\n")) [(APPEND
       "/* CakeML FFI interface (each block is 16 bytes lo" "ng) */");
        "";
        "     .p2align 4";
        ""])) (
     SmartAppend (export_x64_ffi_asm (REVERSE ffi_names'))
      (misc_List (MAP (\n. implode (APPEND n "\n"))
       (APPEND (APPEND ["cake_clear:";
        "     pushq   %rax";
        "     pushq   %rdi";
        "     callq   wcdecl(cml_clear)";
        "     popq    %rdi";
        "     ret";
        "     .p2align 4";
        "";
        "cake_exit:"]
        (if ret then
          ["     jmp     cml_return"] else
          ["     callq   cdecl(cml_exit)"]))
        ["     .p2align 4";
        "";
        "cake_main:";
        "";
        "/* Generated machine code follows */";
        ""]))))) T) else ((\ret. SmartAppend (misc_List (MAP (\n.
          implode (APPEND n "\n")) [(APPEND
          "/* CakeML FFI interface (each block is 16 bytes lo"
          "ng) */"); ""; "     .p2align 4"; ""])) (SmartAppend
          (export_x64_ffi_asm (REVERSE ffi_names')) (misc_List (MAP (\n.
          implode (APPEND n "\n")) (APPEND (APPEND ["cake_clear:";
          "     pushq   %rax"; "     pushq   %rdi";
          "     callq   wcdecl(cml_clear)"; "     popq    %rdi";
          "     ret"; "     .p2align 4"; ""; "cake_exit:"] (if ret then
          ["     jmp     cml_return"] else
          ["     callq   cdecl(cml_exit)"])) ["     .p2align 4"; "";
          "cake_main:"; ""; "/* Generated machine code follows */";
          ""]))))) F)) ret))))))
       (SmartAppend (split16 (words_line (implode "\t.byte ")
         byte_to_string) bytes)
       (SmartAppend (misc_List code_buffer)
       (emit_symbols lsyms))))
       (SmartAppend ((\ret. if ret then ((\ret. SmartAppend
         (misc_List [(implode (APPEND
         "\n/* Windows Compatibility for CakeML FFI interfac"
         "e */\n\n"))])
     (
     SmartAppend (windows_ffi_asm (REVERSE ffi_names'))
      (misc_List (MAP (\n. implode (APPEND n "\n"))
       (APPEND ["windows_cml_clear:"; "     movq    %rcx, %r9";
         "     movq    %rdx, %r8";
         "     movq    %rsi, %rdx";
         "     movq    %rdi, %rcx";
         "     jmp     cdecl(cml_clear)"]
        (if ret then
          [] else [
           // don't need to treat cake_exit as a function
           "windows_cml_exit:";
          "     movq    %rcx, %r9";
          "     movq    %rdx, %r8";
          "     movq    %rsi, %rdx";
          "     movq    %rdi, %rcx";
          "     callq   cdecl(cml_exit)"])))))) T) else ((\ret.
            SmartAppend (misc_List [(implode (APPEND
            "\n/* Windows Compatibility for CakeML FFI interfac"
            "e */\n\n"))]) (SmartAppend (windows_ffi_asm (REVERSE
            ffi_names')) (misc_List (MAP (\n. implode (APPEND n "\n"))
            (APPEND ["windows_cml_clear:"; "     movq    %rcx, %r9";
            "     movq    %rdx, %r8"; "     movq    %rsi, %rdx";
            "     movq    %rdi, %rcx"; "     jmp     cdecl(cml_clear)"]
            (if ret then [] else ["windows_cml_exit:";
            "     movq    %rcx, %r9"; "     movq    %rdx, %r8";
            "     movq    %rsi, %rdx"; "     movq    %rdi, %rcx";
            "     callq   cdecl(cml_exit)"])))))) F)) ret)
       (if ret then
         (SmartAppend ((misc_List (MAP (\n. implode (APPEND n "\n"))
     ["cml_enter:";
      "     sub     $0x30, %rsp";
      "     movq    %r12, -0x8(%rbp)";
        "     movq    %r13, -0x10(%rbp)";
      "     movq    %r14, -0x18(%rbp)";
      "     movq    %r15, -0x20(%rbp)";
      "     movq    %rbx, -0x28(%rbp)";
      "     jmp     cake_main";
      "";
      "windows_cake_enter:";
      "     movq    %rcx, %rdi";
      "     movq    %rdx, %rsi";
      "     movq    %r8, %rdx";
      "     movq    %r9, %rcx";
      "";
      "cake_enter:";
      "     pushq   %rbp";
      "     movq    %rsp, %rbp";
      "     sub     $0x30, %rsp";
      "     movq    %r12, -0x8(%rbp)";
      "     movq    %r13, -0x10(%rbp)";
      "     movq    %r14, -0x18(%rbp)";
      "     movq    %r15, -0x20(%rbp)";
      "     movq    %rbx, -0x28(%rbp)";
      "     movq    can_enter(%rip), %r11";
      "     cmp     $0, %r11";
      "     je      cake_err3";
      "     movq    $0, can_enter(%rip)";
      "     movq    ret_base(%rip), %r14";
      "     movq    ret_stack(%rip), %r12";
      "     movq    ret_stackend(%rip), %r13";
      "     lea     cake_return(%rip), %rax";
      "     jmp     *%r10";
      "     .p2align 4";
      "";
      "cml_return:";
      "     movq    %r14, ret_base(%rip)";
      "     movq    %r12, ret_stack(%rip)";
      "     movq    %r13, ret_stackend(%rip)";
      "";
      "cake_return:";
      "     movq    $1, can_enter(%rip)";
      "     mov     %edi, %eax";
      "     movq    -0x28(%rbp),%rbx";
      "     movq    -0x20(%rbp),%r15";
      "     movq    -0x18(%rbp),%r14";
      "     movq    -0x10(%rbp),%r13";
      "     movq    -0x8(%rbp),%r12";
      "     leave";
      "     ret";
      "     .p2align 4";
      "";
      "cake_err3:";
      "     pushq   %rax";
      "     movq    $3, %rdi";
      "     jmp     wcdecl(cml_err)";
      "     .p2align 4";
      "";
      "windows_cml_err:";
      "     movq    %rcx, %r9";
      "     movq    %rdx, %r8";
      "     movq    %rsi, %rdx";
      "     movq    %rdi, %rcx";
      "     jmp     cdecl(cml_err)";
      ""]))) (export_x64_export_funcs lsyms exp)) else misc_List
        [])))`;;

(*
  EVAL``append(split16 (words_line «\t.quad » word_to_string) [100w:word64;393w;392w])``

  EVAL ``append (x64_export ["getArgs";"putChar";"getChar"] 400 300
    [3w;4w;5w;9w;11w;12w;13w;14w;79w;12w;91w;21w;34w;32w;53w;255w;128w;122w;127w]
    [0w;3w;2w;9w;3w;299w;3w;4w;100w;200w;10w;1w;3w;2w;4w;500w;1000w;12w;123w;93392039w;INT_MAXw])``
  |> concl |> rand |> listSyntax.dest_list |> fst |> map rand
  |> map stringSyntax.fromHOLstring |> concat |> print
*)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
