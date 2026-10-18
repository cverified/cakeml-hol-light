(* ======================================================== *)
(*  export: ported from HOL4's
    compiler/backend/exportScript.sml  *)
(* ======================================================== *)

(*
  Some common helper functions for writing the final byte list ->
  string exporter.
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlstring.ml";;
needs "basis/pure/mlvector.ml";;
needs "compiler/backend/data_space.ml";;
needs "lib/integer_word.ml";;
needs "lib/regexp_compiler.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;

(* HOL4 exportScript.sml:17-20: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let split16_def = cake_define_try_tac (fun () ->
  `MEASURE (LENGTH o SND)`)
  CHEAT_TAC
  `split16 f xs =
        match xs with
          [] -> misc_Nil
        | xs ->
        (let xs1 = TAKE 16 xs in
        let xs2 = DROP 16 xs in
          SmartAppend (f xs1) (split16 f xs2))`;;

(* HOL4 exportScript.sml:22-72: ML code, not ported *)
let preamble_def = cake_define
  `preamble = ((MAP (\n. implode (n ++ "\n"))
       [("/* Preprocessor to get around Mac OS, Windows, and" ++
         " Linux differences in naming and calling conventio" ++
         "ns */");
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
        ("# define makesym(name,base,len) _makesym name, bas" ++
          "e, len");
        "#elif defined(__WIN32)";
        ".macro _makesym name, base, len";
        ".set \\name, cake_main+\\base";
        ".endm";
        ("# define makesym(name,base,len) _makesym name, bas" ++
          "e, len");
        "#else";
        ".macro _makesym name, base, len";
        ".local \\name";
        ".set \\name, cake_main+\\base";
        ".size \\name, \\len";
        ".type \\name, function";
        ".endm";
        ("# define makesym(name,base,len) _makesym name, bas" ++
          "e, len");
        "#endif";
        "";
        "#define DATA_BUFFER_SIZE    65536";
        "#define CODE_BUFFER_SIZE  5242880";
        "";
        "     .file        \"cake.S\"";
        ""]))`;;

let data_section_def = cake_define
  `data_section word_directive ret =
      MAP (\n. implode (n ++ "\n"))
        (["     .data";
         "     .p2align 3";
         "cdecl(cml_heap): " ++ word_directive ++ " 0";
         "cdecl(cml_stack): " ++ word_directive ++ " 0";
         "cdecl(cml_stackend): " ++ word_directive ++ " 0"] ++
         (if ret then
           ["ret_base: " ++ word_directive ++ " 0";
            "ret_stack: " ++ word_directive ++ " 0";
            "ret_stackend: " ++ word_directive ++ " 0";
            "can_enter: " ++ word_directive ++ " 0"] else []) ++
         ["     .p2align 3";
         "cake_bitmaps:"])`;;

let data_buffer_def = cake_define
  `data_buffer =
      MAP (\n. implode (n ++ "\n"))
        ["     .globl cdecl(cake_bitmaps_buffer_begin)";
         "cdecl(cake_bitmaps_buffer_begin):";
         "#if defined(EVAL)";
         "     .space DATA_BUFFER_SIZE";
         "#endif";
         "     .globl cdecl(cake_bitmaps_buffer_end)";
         "cdecl(cake_bitmaps_buffer_end):"]`;;

let code_buffer_def = cake_define
  `code_buffer =
      MAP (\n. implode (n ++ "\n"))
        ["     .globl cdecl(cake_codebuffer_begin)";
         "cdecl(cake_codebuffer_begin):";
         "#if defined(EVAL)";
         "     .space CODE_BUFFER_SIZE";
         "#endif";
         "     .p2align 12";
         "     .globl cdecl(cake_codebuffer_end)";
         "cdecl(cake_codebuffer_end):";
         "     .space 4096"]`;;

let comm_strlit_def = cake_define
  `comm_strlit = (implode ",")`;;
let newl_strlit_def = cake_define
  `newl_strlit = (implode "\n")`;;

let comma_cat_def = cake_define
  `comma_cat f x =
     (match x with [] -> [newl_strlit] | [x] -> [f x; newl_strlit]
       | (x :: xs) -> f x :: comm_strlit :: comma_cat f xs)`;;

let words_line_def = cake_define
  `words_line word_directive to_string ls =
     misc_List (word_directive :: comma_cat to_string ls)`;;

let word_to_string_def = cake_define
  `word_to_string w = toString (w2n w)`;;

let byte_to_string_def = cake_define
  `byte_to_string (b:word8) =
     implode (
                  "0x" ++ [EL (w2n b DIV 16) "0123456789ABCDEF"]
                    ++ [EL (w2n b MOD 16) "0123456789ABCDEF"])`;;

let all_bytes_def = cake_define
  `all_bytes = Vector (GENLIST (\n. byte_to_string (n2w n)) 256)`;;

(* gas allows 0-9a-zA-Z_$. in labels as long as the first is _A-Za-z *)
(* we prefix labels and reserve $; . is special *)

let escape_sym_char_def = cake_define
  `escape_sym_char ch = (let code = ORD ch in
     if code >= 97 /\ code <= 122 \/ code >= 65 /\ code <= 90 \/
        code >= 48 /\ code <= 57 \/ code = 95 then toString ch else
          (\x y. strcat x y) ((\x y. strcat x y)
     (implode "$") (toString (code))) (implode "_"))`;;

let get_sym_label_def = cake_define
  `get_sym_label (ix,appl) (name,start',len) =
     (let label = (\x y. strcat x y) ((\x y. strcat x y) ((\x y.
       strcat x y)
       (implode "cml_") (concat (MAP escape_sym_char (explode
         name))))
       (implode "_")) (toString (ix)) in
     (ix + 1,appl ++ [(name,label,start',len)]))`;;

let get_sym_labels_def = cake_define
  `get_sym_labels syms =
     SND (FOLDL get_sym_label (0,[]) syms)`;;

let emit_symbol_def = cake_define
  `emit_symbol appl (name,label,start',len) =
     misc_Append appl (misc_List
       [(\x y. strcat x y) ((\x y. strcat x y) ((\x y. strcat x y)
         ((\x y. strcat x y) ((\x y. strcat x y) ((\x y. strcat x y)
         (implode "    makesym(") label) (implode ", ")) (toString
         (start'))) (implode ", "))
       (toString (len))) (implode ")\n")])`;;

let emit_symbols_def = cake_define
  `emit_symbols lsyms =
     FOLDL emit_symbol misc_Nil lsyms`;;
