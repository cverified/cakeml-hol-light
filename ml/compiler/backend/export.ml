(* ======================================================== *)
(*  export: ported from HOL4's
    compiler/backend/exportScript.sml
    A definition theory, with 17 definitions and 2 theorems.  Needed
    by export_ag32.ml, export_arm7.ml, export_arm8.ml,
    export_mips.ml, export_riscv.ml and export_x64.ml.  *)
(* ======================================================== *)

(*
  Some common helper functions for writing the final byte list ->
  string exporter.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "compiler/backend/data_space.ml";;
needs "lib/regexp_compiler.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "export"
  ["mlint"; "mlstring"; "mlvector"];;

(* the termination relation that HOL4 gives is
     MEASURE (LENGTH o SND)
   which is not one that HOL Light takes here, so the
   port lets its own machinery find one *)
(* HOL4 exportScript.sml:17-20: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let split16_def,split16_ind = define_guess_cheat
  [`split16 f xs =
        match xs with
          [] -> misc_Nil
        | xs ->
        (let xs1 = TAKE 16 xs in
        let xs2 = DROP 16 xs in
          SmartAppend (f xs1) (split16 f xs2))`];;

(* HOL4 exportScript.sml:22-72: the ML values that the definitions
   below antiquote *)
let preamble_def = new_definition
  `preamble = ((MAP (\n. implode (APPEND n "\n"))
       [(APPEND "/* Preprocessor to get around Mac OS, Windows, and"
         (APPEND " Linux differences in naming and calling conventio"
         "ns */"));
        "";
        "#if defined(__APPLE__)";
        "# define cdecl(s) _##s";
        "#else";
        "# define cdecl(s) s";
        "#endif";
        "";
        "#if defined(__APPLE__)";
        "# define wcdecl(s) _##s";
        "#elif defined(__WIN32)";
        "# define wcdecl(s) windows_##s";
        "#else";
        "# define wcdecl(s) s";
        "#endif";
        "";
        "#if defined(__APPLE__)";
        "# define wcml(s) s";
        "#elif defined(__WIN32)";
        "# define wcml(s) windows_##s";
        "#else";
        "# define wcml(s) s";
        "#endif";
        "";
        "#if defined(__APPLE__)";
        ".macro _makesym name, base, len";
        ".set \\name, cake_main+\\base";
        ".endm";
        (APPEND "# define makesym(name,base,len) _makesym name, bas"
          "e, len");
        "#elif defined(__WIN32)";
        ".macro _makesym name, base, len";
        ".set \\name, cake_main+\\base";
        ".endm";
        (APPEND "# define makesym(name,base,len) _makesym name, bas"
          "e, len");
        "#else";
        ".macro _makesym name, base, len";
        ".local \\name";
        ".set \\name, cake_main+\\base";
        ".size \\name, \\len";
        ".type \\name, function";
        ".endm";
        (APPEND "# define makesym(name,base,len) _makesym name, bas"
          "e, len");
        "#endif";
        "";
        "#define DATA_BUFFER_SIZE    65536";
        "#define CODE_BUFFER_SIZE  5242880";
        "";
        "     .file        \"cake.S\"";
        ""]))`;;

let data_section_def = new_definition
  `data_section word_directive ret =
      MAP (\n. implode (APPEND n "\n"))
        (APPEND (APPEND ["     .data";
         "     .p2align 3"; APPEND (APPEND "cdecl(cml_heap): "
           word_directive) " 0"; APPEND (APPEND "cdecl(cml_stack): "
           word_directive) " 0"; APPEND (APPEND "cdecl(cml_stackend): "
           word_directive) " 0"]
         (if ret then
           [APPEND (APPEND "ret_base: " word_directive) " 0"; APPEND
             (APPEND "ret_stack: " word_directive) " 0"; APPEND (APPEND
             "ret_stackend: " word_directive) " 0"; APPEND (APPEND
             "can_enter: " word_directive) " 0"] else []))
         ["     .p2align 3";
         "cake_bitmaps:"])`;;

let data_buffer_def = new_definition
  `data_buffer =
      MAP (\n. implode (APPEND n "\n"))
        ["     .globl cdecl(cake_bitmaps_buffer_begin)";
         "cdecl(cake_bitmaps_buffer_begin):";
         "#if defined(EVAL)";
         "     .space DATA_BUFFER_SIZE";
         "#endif";
         "     .globl cdecl(cake_bitmaps_buffer_end)";
         "cdecl(cake_bitmaps_buffer_end):"]`;;

let code_buffer_def = new_definition
  `code_buffer =
      MAP (\n. implode (APPEND n "\n"))
        ["     .globl cdecl(cake_codebuffer_begin)";
         "cdecl(cake_codebuffer_begin):";
         "#if defined(EVAL)";
         "     .space CODE_BUFFER_SIZE";
         "#endif";
         "     .p2align 12";
         "     .globl cdecl(cake_codebuffer_end)";
         "cdecl(cake_codebuffer_end):";
         "     .space 4096"]`;;

let comm_strlit_def = new_definition
  `comm_strlit = (implode ",")`;;
let newl_strlit_def = new_definition
  `newl_strlit = (implode "\n")`;;

let comma_cat_def,comma_cat_ind = define_guess
  [`comma_cat f x =
     (match x with [] -> [newl_strlit] | [x] -> [f x;
       newl_strlit] | (CONS x xs) -> CONS (f x) (CONS comm_strlit
       (comma_cat f xs)))`];;

let words_line_def = new_definition
  `words_line word_directive to_string ls =
     misc_List (CONS word_directive (comma_cat to_string ls))`;;

let word_to_string_def = new_definition
  `word_to_string w = mlint_toString (w2n w)`;;

let byte_to_string_def = new_definition
  `byte_to_string (b:word8) =
     implode (
                  APPEND (APPEND "0x" [EL (w2n b DIV 16)
                    "0123456789ABCDEF"]) [EL (w2n b MOD 16)
                    "0123456789ABCDEF"])`;;

let all_bytes_def = new_definition
  `all_bytes = Vector (list_of_seq (\n. byte_to_string (n2w n)) 256)`;;

(* HOL4 exportScript.sml:155-156: a theorem that HOL4 states as the
   value of an ML expression: all_bytes_eq *)

let byte_to_string_eq = prove
 (`!b. byte_to_string b = sub all_bytes (w2n b)`,
  (GEN_TAC THEN REWRITE_TAC[all_bytes_def; sub_def] THEN
   SUBGOAL_THEN `val (b:byte) < 256` ASSUME_TAC THENL
    [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8]
      THEN
     ARITH_TAC;
     ASM_SIMP_TAC[EL_LIST_OF_SEQ; WORD_VAL]]));;

(* gas allows 0-9a-zA-Z_$. in labels as long as the first is _A-Za-z *)
(* we prefix labels and reserve $; . is special *)

let escape_sym_char_def = new_definition
  `escape_sym_char ch = (let code = ORD ch in
     if code >= 97 /\ code <= 122 \/ code >= 65 /\ code <= 90 \/
        code >= 48 /\ code <= 57 \/ code = 95 then mlint_toString
          ch else (\x y. strcat x y) ((\x y. strcat x y) (implode
          "$") (mlint_toString (code))) (implode "_"))`;;

let get_sym_label_def = new_definition
  `get_sym_label (ix,appl) (name,start',len) =
     (let label = (\x y. strcat x y) ((\x y. strcat x y) ((\x y.
       strcat x y) (implode "cml_") (mlvector_concat (MAP
       escape_sym_char (explode name))))
       (implode "_")) (mlint_toString (ix)) in
     (ix + 1,APPEND appl [(name,label,start',len)]))`;;

let get_sym_labels_def = new_definition
  `get_sym_labels syms =
     SND (FOLDL get_sym_label (0,[]) syms)`;;

let emit_symbol_def = new_definition
  `emit_symbol appl (name,label,start',len) =
     misc_Append appl (misc_List
       [(\x y. strcat x y) ((\x y. strcat x y) ((\x y. strcat x y)
         ((\x y. strcat x y) ((\x y. strcat x y) ((\x y. strcat x y)
         (implode "    makesym(") label) (implode ", ")) (mlint_toString
         (start'))) (implode ", "))
       (mlint_toString (len))) (implode ")\n")])`;;

let emit_symbols_def = new_definition
  `emit_symbols lsyms =
     FOLDL emit_symbol misc_Nil lsyms`;;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
