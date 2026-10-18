(* ======================================================== *)
(*  compiler: ported from HOL4's
    compiler/compilerScript.sml  *)
(* ======================================================== *)

(*
  Definition of the CakeML compiler as a function that takes a list of
    command
  line arguments and a string corresponding to standard input, and
    produces a
  pair of output strings for standard error and standard output (the
    latter
  containing the generated machine code if successful).
*)

needs "basis/pure/mlint.ml";;
needs "basis/pure/mlsexp.ml";;
needs "basis/pure/mlstring.ml";;
needs "compiler/backend/ag32/ag32_config.ml";;
needs "compiler/backend/ag32/export_ag32.ml";;
needs "compiler/backend/arm7/arm7_config.ml";;
needs "compiler/backend/arm7/export_arm7.ml";;
needs "compiler/backend/arm8/arm8_config.ml";;
needs "compiler/backend/arm8/export_arm8.ml";;
needs "compiler/backend/backend.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/data_to_word.ml";;
needs "compiler/backend/flat_pattern.ml";;
needs "compiler/backend/mips/export_mips.ml";;
needs "compiler/backend/mips/mips_config.ml";;
needs "compiler/backend/riscv/export_riscv.ml";;
needs "compiler/backend/riscv/riscv_config.ml";;
needs "compiler/backend/x64/export_x64.ml";;
needs "compiler/backend/x64/x64_config.ml";;
needs "compiler/encoders/asm/asm.ml";;
needs "compiler/inference/infer.ml";;
needs "compiler/parsing/cmlParse.ml";;
needs "compiler/parsing/fromSexp.ml";;
needs "compiler/parsing/lexer_impl.ml";;
needs "lib/errorMonad.ml";;
needs "lib/integer_word.ml";;
needs "lib/location.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexpParse.ml";;
needs "misc/misc.ml";;
needs "pancake/panLang.ml";;
needs "semantics/ast.ml";;
needs "semantics/lexer_fun.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;
(* HOL4 ancestors outside the port: basisProg panPtreeConversion
   pan_to_target panStatic pan_passes *)

let staterr_INDUCT,staterr_RECURSION = define_datatype
  "staterr = ScopeErr (mlstring) | WarningErr (mlstring) \
             | GenErr (mlstring) | ShapeErr (mlstring)";;

(* HOL4 ML code, not ported:
val help_string = (* beginning of --help string *) ‘

Usage:  cake [OPTIONS] < input_file > output_file

The cake executable is usually invoked as shown above. The different
OPTIONS are described in the OPTIONS listing below.

One can also run the cake execuable as follows to print a listing of
the type of each top-level binding (including the bindings made in
the standard basis library).

Usage:  cake --types < input_file

One can invoke the cake executable to print this help message (--help)
or version information (--version) without an input_file:

Usage:  cake --version
Usage:  cake --help

OPTIONS:

  --repl        starts an interactive read-eval-print loop; all other
                flags are ignored, when the --repl flag is present

  --reg_alg=N   N is a natural number that specifies the register
                allocation algorithm to use:
                   0   - simple allocator, no spill heuristics
                   1   - simple allocator, spill heuristics
                   2   - IRC allocator, no spill heuristics (default)
                   3   - IRC allocator, spill heuristics
                   >=4 - linear scan allocator

  --gc=G        specifies garbage collector type; here G is one of:
                   none   - no garbage collector is used
                   simple - a non-generational Cheney (default)
                   genN   - a generational Cheney garbage collector is
                            used; the size of the nursery generation is
                            N machine words (example: --gc=gen5000)
                This option has no effect under --pancake; the Pancake
                compiler always uses gc=none.

  --target=T    specifies that compilation should produce code for
    target
                T, where T can be one of x64, arm8, mips, riscv for
                the 64-bit compiler; for the 32-bit compiler T can be
                one of arm7 and ag32.

  --sexp=B      B can be either true or false; here false means that the
                input will be parsed as normal CakeML concrete syntax;
                true means that the input is parsed as an s-expression.

  --print_sexp  causes the cake to print the given program in
                s-expression format; with this option, the compiler
                does not generate machine code.

  --exclude_prelude=B   here B can be either true or false; the default
                is false; setting this to true causes the compiler not
                to include the standard basis library.

  --skip_type_inference=B   here B can be either true or false; the
                default is false; true will make the compiler skip
                type inference. There are no gurantees of safety if
                the type inferencer is skipped.

  --explore     outputs intermediate forms of the compiled program

  --pancake     takes a pancake program as input

  --no_warn     silences pancake warning output

  --main_return=B   here B can be either true or false; the default is
                false; setting this to true causes the main function to
                return to caller instead of exit; this option is
                required to use multiple entry points with Pancake.

ADDITIONAL OPTIONS:

Optimisations can be configured using the following advanced options.

  --jump=B    true means conditional jumps to be used for out-of-stack
    checks
  --multi=B   true means clos_to_bvl phase is to use multi optimisation
  --known=B   true means clos_to_bvl phase is to use known optimisation
  --call=B    true means clos_to_bvl phase is to use call optimisation
  --tmc=B     true means tail-call modulo cons optimisations is used
  --tailrec=B true means attempts to turn functions into tail-rec form
  --inline_factor=N  threshold used by for ClosLang inliner in known
    pass
  --max_body_size=N  threshold used by for ClosLang inliner in known
    pass
  --max_app=N   max number of optimised curried applications in multi
    pass
  --inline_size=N  threshold used by for BVL inliner pass
  --exp_cut=N  threshold for when to cut large expression into
    subfunctions
  --split=B  true means main expression will be split at sequencing (;)
  --tag_bits=N  number of tag bits in every pointer
  --len_bits=N  number of length bits in every pointer
  --pad_bits=N  number of zero padding in every pointer
  --len_size=N  size of length field in heap object header cells
  --emit_empty_ffi=B  true emits debugging FFI calls for use with
    DEBUG_FFI
  --hash_size=N  size of the memoization table used by instruction
    encoder
  --perf_callgraph=B  unverified: emit C-stack shadowing so `perf record
                --call-graph fp` produces correct call graphs (x64 only)

’ (* end of --help string *)
*)

(* == Build info
   =========================================================== *)

(* HOL4 ML code, not ported:
val current_version_tm = mlstring_from_proc "git" ["rev-parse", "HEAD"]
*)
(*"" *)

(* HOL4 ML code, not ported:
val date_str = Date.toString (Date.fromTimeUniv (Time.now ())) ^
  " UTC\n"
val date_tm = Term `strlit^(stringSyntax.fromMLstring date_str)`
*)

let print_option_def = cake_define
  `print_option h x =
     (match x with
       NONE -> (implode "") | SOME y -> (\x y. strcat x y) ((\x y.
         strcat x y) ((\x y. strcat x y) h (implode " ")) y) (implode
         "\n"))`;;

(* HOL4 ML code, not ported:
val current_build_info_str_tm = EVAL ``
    let commit = print_option «CakeML:» ^current_version_tm in
    let hol    = print_option «HOL4:  » ^hol_version_tm in
    let poly   = print_option «PolyML:» ^poly_version_tm in
      concat
        [ «The CakeML compiler\n\n»
        ; «Version details:\n»
        ; ^date_tm; «\n»
        ; commit; hol; poly ]``
  |> concl |> rhs
*)

let current_build_info_str_def = cake_define
  `current_build_info_str =
     (let commit = print_option (implode "CakeML:")
                     (NONE:mlstring option) in
     let hol = print_option (implode "HOL4:  ")
                 (NONE:mlstring option) in
     let poly = print_option (implode "PolyML:")
                  (NONE:mlstring option) in
       mlstring_concat
         [implode "The CakeML compiler\n\n";
          implode "Version details:\n"; implode "";
          implode "\n"; commit; hol; poly])`;;

(* =====================================================================
   ==== *)

let compiler_config_FIELDS = define_record "compiler_config"
  ["inferencer_config","inf_env";
   "backend_config","backend_config";
   "asm_config","'a asm_config";
   "input_is_sexp","bool";
   "exclude_prelude","bool";
   "skip_type_inference","bool";
   "only_print_types","bool";
   "only_print_sexp","bool"];;

(* HOL4 ML code, not ported:
fun drop_until p [] = []
  | drop_until p (x::xs) = if p x then x::xs else drop_until p xs;
*)

(* HOL4 ML code, not ported:
val help_string_tm =
  help_string |> hd |> (fn QUOTE s => s) |> explode
  |> drop_until (fn c => c = #"\n") |> tl |> implode
  |> stringSyntax.fromMLstring;
*)

(* HOL4 takes this string from the quotation of the --help text at
   the head of the source, without its first line (the ML code of
   help_string_tm above).  The port writes the text out and makes
   the term of it, because a string literal of HOL Light holds the
   characters that are in it, and this text has newlines and a
   backquote in it. *)

let help_string_def = cake_define
  (mk_eq(`help_string:mlstring`,
         mk_comb(`implode`, mk_string
  ("\n" ^
   "Usage:  cake [OPTIONS] < input_file > output_file\n" ^
   "\n" ^
   "The cake executable is usually invoked as shown above. The d" ^
   "ifferent\n" ^
   "OPTIONS are described in the OPTIONS listing below.\n" ^
   "\n" ^
   "One can also run the cake execuable as follows to print a li" ^
   "sting of\n" ^
   "the type of each top-level binding (including the bindings m" ^
   "ade in\n" ^
   "the standard basis library).\n" ^
   "\n" ^
   "Usage:  cake --types < input_file\n" ^
   "\n" ^
   "One can invoke the cake executable to print this help messag" ^
   "e (--help)\n" ^
   "or version information (--version) without an input_file:\n" ^
   "\n" ^
   "Usage:  cake --version\n" ^
   "Usage:  cake --help\n" ^
   "\n" ^
   "OPTIONS:\n" ^
   "\n" ^
   "  --repl        starts an interactive read-eval-print loop; " ^
   "all other\n" ^
   "                flags are ignored, when the --repl flag is p" ^
   "resent\n" ^
   "\n" ^
   "  --reg_alg=N   N is a natural number that specifies the reg" ^
   "ister\n" ^
   "                allocation algorithm to use:\n" ^
   "                   0   - simple allocator, no spill heuristi" ^
   "cs\n" ^
   "                   1   - simple allocator, spill heuristics" ^
   "\n" ^
   "                   2   - IRC allocator, no spill heuristics " ^
   "(default)\n" ^
   "                   3   - IRC allocator, spill heuristics\n" ^
   "                   >=4 - linear scan allocator\n" ^
   "\n" ^
   "  --gc=G        specifies garbage collector type; here G is " ^
   "one of:\n" ^
   "                   none   - no garbage collector is used\n" ^
   "                   simple - a non-generational Cheney (defau" ^
   "lt)\n" ^
   "                   genN   - a generational Cheney garbage co" ^
   "llector is\n" ^
   "                            used; the size of the nursery ge" ^
   "neration is\n" ^
   "                            N machine words (example: --gc=g" ^
   "en5000)\n" ^
   "                This option has no effect under --pancake; t" ^
   "he Pancake\n" ^
   "                compiler always uses gc=none.\n" ^
   "\n" ^
   "  --target=T    specifies that compilation should produce co" ^
   "de for target\n" ^
   "                T, where T can be one of x64, arm8, mips, ri" ^
   "scv for\n" ^
   "                the 64-bit compiler; for the 32-bit compiler" ^
   " T can be\n" ^
   "                one of arm7 and ag32.\n" ^
   "\n" ^
   "  --sexp=B      B can be either true or false; here false me" ^
   "ans that the\n" ^
   "                input will be parsed as normal CakeML concre" ^
   "te syntax;\n" ^
   "                true means that the input is parsed as an s-" ^
   "expression.\n" ^
   "\n" ^
   "  --print_sexp  causes the cake to print the given program i" ^
   "n\n" ^
   "                s-expression format; with this option, the c" ^
   "ompiler\n" ^
   "                does not generate machine code.\n" ^
   "\n" ^
   "  --exclude_prelude=B   here B can be either true or false; " ^
   "the default\n" ^
   "                is false; setting this to true causes the co" ^
   "mpiler not\n" ^
   "                to include the standard basis library.\n" ^
   "\n" ^
   "  --skip_type_inference=B   here B can be either true or fal" ^
   "se; the\n" ^
   "                default is false; true will make the compile" ^
   "r skip\n" ^
   "                type inference. There are no gurantees of sa" ^
   "fety if\n" ^
   "                the type inferencer is skipped.\n" ^
   "\n" ^
   "  --explore     outputs intermediate forms of the compiled p" ^
   "rogram\n" ^
   "\n" ^
   "  --pancake     takes a pancake program as input\n" ^
   "\n" ^
   "  --no_warn     silences pancake warning output\n" ^
   "\n" ^
   "  --main_return=B   here B can be either true or false; the " ^
   "default is\n" ^
   "                false; setting this to true causes the main " ^
   "function to\n" ^
   "                return to caller instead of exit; this optio" ^
   "n is\n" ^
   "                required to use multiple entry points with P" ^
   "ancake.\n" ^
   "\n" ^
   "ADDITIONAL OPTIONS:\n" ^
   "\n" ^
   "Optimisations can be configured using the following advanced" ^
   " options.\n" ^
   "\n" ^
   "  --jump=B    true means conditional jumps to be used for ou" ^
   "t-of-stack checks\n" ^
   "  --multi=B   true means clos_to_bvl phase is to use multi o" ^
   "ptimisation\n" ^
   "  --known=B   true means clos_to_bvl phase is to use known o" ^
   "ptimisation\n" ^
   "  --call=B    true means clos_to_bvl phase is to use call op" ^
   "timisation\n" ^
   "  --tmc=B     true means tail-call modulo cons optimisations" ^
   " is used\n" ^
   "  --tailrec=B true means attempts to turn functions into tai" ^
   "l-rec form\n" ^
   "  --inline_factor=N  threshold used by for ClosLang inliner " ^
   "in known pass\n" ^
   "  --max_body_size=N  threshold used by for ClosLang inliner " ^
   "in known pass\n" ^
   "  --max_app=N   max number of optimised curried applications" ^
   " in multi pass\n" ^
   "  --inline_size=N  threshold used by for BVL inliner pass\n" ^
   "  --exp_cut=N  threshold for when to cut large expression in" ^
   "to subfunctions\n" ^
   "  --split=B  true means main expression will be split at seq" ^
   "uencing (;)\n" ^
   "  --tag_bits=N  number of tag bits in every pointer\n" ^
   "  --len_bits=N  number of length bits in every pointer\n" ^
   "  --pad_bits=N  number of zero padding in every pointer\n" ^
   "  --len_size=N  size of length field in heap object header c" ^
   "ells\n" ^
   "  --emit_empty_ffi=B  true emits debugging FFI calls for use" ^
   " with DEBUG_FFI\n" ^
   "  --hash_size=N  size of the memoization table used by instr" ^
   "uction encoder\n" ^
   "  --perf_callgraph=B  unverified: emit C-stack shadowing so " ^
   "`perf record\n" ^
   "                --call-graph fp` produces correct call graph" ^
   "s (x64 only)\n" ^
   "\n"))));;

let compile_error_INDUCT,compile_error_RECURSION = define_datatype
  "compile_error = ParseError (mlstring) | TypeError (mlstring) | \
   AssembleError | ConfigError (mlstring) | StaticError (staterr)";;

let find_next_newline_def = cake_define_wf
  `MEASURE (\(n,s). strlen s - n)`
  `find_next_newline n s =
     (if strlen s <= n then n else
       if strsub s n = (CHR 10) then n else
         find_next_newline (n + 1) s)`;;

let safe_substring_def = cake_define
  `safe_substring s n l =
     (let k = strlen s in
       if k <= n then (implode "") else
         if n + l <= k then
           substring s n l else substring s n (k - n))`;;

let get_nth_line_def = cake_define
  `get_nth_line k s n =
     (if k = 0 then
       let n1 = find_next_newline n s in
         safe_substring s n (n1 - n) else
       get_nth_line (k - (1:num)) s (find_next_newline n s + 1))`;;

let locs_to_string_def = cake_define
  `locs_to_string input x2 =
        match x2 with
          NONE -> implode "unknown location"
        | (SOME (Locs startl endl)) ->
       (match startl with POSN r c ->
          (let line = get_nth_line r input 0 in
           let len = strlen line in
           let stop =
             (match endl with POSN r1 c1 -> (if r1 = r then c1 else
               len) | _3 -> len) in
           let underline =
             concat (REPLICATE c (implode " ") ++ REPLICATE ((stop -
               c) + 1) (implode [CHR 94])) in
             concat [(implode "line "); toString (r + 1); (implode
               "\n\n");
                     line; (implode "\n");
                     underline; (implode "\n")]) | _4 -> implode
                       "unknown location")`;;

(* this is a rather annoying feature of peg_exec requiring locs... *)
(* HOL4 overload (expanded in the port):
     add_locs = MAP (λc. (c,unknown_loc)) *)

let parse_sexp_input_def = cake_define
  `parse_sexp_input input =
     (let err = (implode "Parsing of sexp syntax failed") in
       match parse_sexp ((MAP (\c. (c,unknown_loc))) input) with
         NONE -> INL err | SOME x -> (match sexplist sexpdec x with
         NONE -> INL err | SOME x -> INR x))`;;

let parse_cml_input_def = cake_define
  `parse_cml_input input =
     (match parse_prog (lexer_fun input) with peg_Failure l _5 ->
       INL ((\x y. strcat x y) (implode "Parsing failed at ")
       (locs_to_string (implode input) (SOME l))) | Success _6 x _7
       -> INR x)`;;

let compile_def = cake_define
  `compiler_compile c prelude input =
     (let _8 = empty_ffi (implode "finished: start up") in
     match
       (if compiler_config_input_is_sexp c then parse_sexp_input
         input else parse_cml_input input) with INL msg -> (M_failure
         (ParseError msg),misc_Nil) | INR prog ->
        (let _9 = empty_ffi (implode "finished: lexing and parsing")
          in
        let full_prog = (if compiler_config_exclude_prelude c then
          prog else prelude ++ prog) in
        match
          (if compiler_config_skip_type_inference c then M_success
            (compiler_config_inferencer_config c) else infertype_prog
            (compiler_config_inferencer_config c) full_prog) with
            M_failure (locs,msg) ->
            (M_failure (TypeError (concat [msg; (implode " at ");
                locs_to_string (implode input) locs])),misc_Nil) |
                  M_success ic ->
           (let _10 = empty_ffi (implode "finished: type inference")
             in
           if compiler_config_only_print_types c then
             (M_failure (TypeError (concat ([(implode "\n")] ++
                              inf_env_to_types_string ic ++
                              [(implode "\n")]))),misc_Nil) else if
                                compiler_config_only_print_sexp c then
             (M_failure (TypeError (implode
                ("\n" ++ print_sexp (listsexp (MAP decsexp
                  full_prog))))),misc_Nil) else
           match compile_tap (compiler_config_asm_config c)
             (compiler_config_backend_config c) full_prog with
             (NONE,td) -> (M_failure AssembleError,td) | (SOME
             (bytes,data,c),td) -> (M_success (bytes,data,c),td))))`;;
hol4_overload "compile" "compiler_compile";;

cake_declare "parse_topdecs_to_ast"
  `:string -> (('a)decl)list + (mlstring#locs)list`;;
cake_declare "static_check"
  `:(('a)decl)list -> (1,staterr)errorMonad_error#(staterr)list`;;
cake_declare "pan_compile_tap"
  `:('a)asm_config -> backend_config -> (('a)decl)list ->
    ((((8)word)list#(('a)word)list#backend_config)option)#
    (mlstring)app_list`;;

let compile_pancake_def = cake_define
  `compile_pancake asm_conf c input =
   (let _11 = empty_ffi (implode "finished: start up") in
   match parse_topdecs_to_ast input with INR errs ->
     ((M_failure (ParseError (concat
        (MAP (\(msg,loc). concat [msg; (implode " at ");
                              locs_to_string (implode input) (SOME
                                loc); (implode "\n")])
            errs)))),misc_Nil,[]) | INL funs ->
       (match static_check funs with (errorMonad_error e,warns) ->
         (M_failure (StaticError e),misc_Nil,MAP StaticError warns) |
         (errorMonad_return one,warns) ->
           (let _12 = empty_ffi (implode
             "finished: lexing and parsing") in
           match pan_compile_tap asm_conf c funs with (NONE,td) ->
             (M_failure AssembleError,td,MAP StaticError warns) |
             (SOME (bytes,data,c),td) -> (M_success
             (bytes,data,c),td,MAP StaticError warns))))`;;

(* The top-level compiler *)
let error_to_str_def = cake_define_list
  [`error_to_str (ParseError s) =
         concat [(implode "### ERROR: parse error\n"); s;
           (implode "\n")]`;
   `error_to_str (TypeError s) =
         (if (if strlen s = 0 then T else
             if strsub s 0 = (CHR 10) then F else T) then
           concat [(implode "### ERROR: type error\n"); s;
             (implode "\n")] else s)`;
   `error_to_str (ConfigError s) = concat [(implode
  "### ERROR: config error\n"); s; (implode "\n")]`;
   `error_to_str AssembleError = (implode
  "### ERROR: assembly error\n")`;
   `error_to_str (StaticError e) =
        (match e with
          ScopeErr s -> concat [(implode
            "### ERROR: scope error\n"); s; (implode "\n")] |
            WarningErr s -> concat [(implode "# WARNING:\n"); s;
            (implode "\n")] | GenErr s -> concat [(implode
            "### ERROR: static error\n"); s; (implode "\n")] |
            ShapeErr s -> concat [(implode
            "### ERROR: shape error\n"); s; (implode "\n")])`];;

let is_error_msg_def = cake_define
  `is_error_msg x = isPrefix (implode "###") x`;;

(* TODO: translator fails inside mlstringLib.mlstring_case_conv
  when the following definition just matches against (strlit str)
    directly *)
let parse_num_def = cake_define
  `parse_num str =
   (let str = explode str in
   if EVERY isDigit str then
     SOME (num_from_dec_string_alt str) else NONE)`;;

let parse_bool_def = cake_define
  `parse_bool str =
   (if str = (implode "true") then SOME T else if str = (implode
     "false") then SOME F else NONE)`;;

(* Finds the first occurence of the flag and
  returns the rest of the string after it *)
let find_str_def = cake_define_list
  [`find_str flag [] = NONE`;
   `find_str flag (x :: xs) =
        (if isPrefix flag x then
          SOME (extract x (strlen flag) NONE) else
          find_str flag xs)`];;

(* Finds all occurences of the flag as a prefix, returning
   the remainder in each occurence. *)
let find_strs_def = cake_define_list
  [`find_strs flag [] = []`;
   `find_strs flag (x :: xs) =
        (if isPrefix flag x then
          (extract x (strlen flag) NONE) :: find_strs flag xs else
          find_strs flag xs)`];;

(* If flag is not present then F, else if it is present then
   we should not get any config string afterwards *)
let find_bool_def = cake_define
  `find_bool flag ls default =
   (match find_str flag ls with
     NONE -> INL default | SOME rest ->
     (match parse_bool rest with
       SOME b -> INL b | NONE -> INR (concat [(implode
         "Unable to parse as bool: "); rest; (implode " for flag: ");
         flag])))`;;

(* If flag is not present then INL default, else if it is present then
   the rest of the config string should be a number *)
let find_num_def = cake_define
  `find_num flag ls default =
   (match find_str flag ls with
     NONE -> INL default | SOME rest ->
   (match parse_num rest with
     SOME n -> INL n | NONE -> INR (concat [(implode
       "Unable to parse as num: "); rest; (implode " for flag: ");
       flag])))`;;

let get_err_str_def = cake_define_list
  [`get_err_str (INL n) = (implode "")`;
   `get_err_str (INR n) = concat [n; (implode "\n")]`];;

(* All the numbers must parse *)
let parse_num_list_def = cake_define_list
  [`parse_num_list [] = INL []`;
   `parse_num_list (x :: xs) =
         (match parse_num x with
           NONE -> INR (concat [(implode
             "Unable to parse as num: "); x]) | SOME n ->
           (match parse_num_list xs with
             INR s -> INR s | INL ns -> INL (n :: ns)))`];;

let comma_tokens_def = cake_define_list
  [`comma_tokens acc (xs:string) [] = (if NULL xs then acc else acc
  ++ [implode xs])`;
   `comma_tokens acc (xs:string) (c :: (cs:string)) =
        (if c = (CHR 44) then
          comma_tokens (acc ++ (if NULL xs then [] else [implode
            xs])) [] cs else
          comma_tokens acc (STRCAT xs [c]) cs)`];;


let parse_nums_def = cake_define
  `parse_nums str = (parse_num_list (comma_tokens [] [] (explode
  str)))`;;

(*
  EVAL``find_bool «--mul=» [«asf»;«--mul=fse»] F``
  EVAL``find_bool «--nomul» [«asf»;«--nomul=fdsa»] T``
  EVAL``find_num «--fl» [«asf»;«--f1234»] 5n``
*)

(*
  Each of these is a helper function that extends a conf
  It either returns an INL extended_conf or INR error_string
  TODO: use pmatch for this...
*)

(* clos_conf *)
let parse_clos_conf_def = cake_define
  `parse_clos_conf ls clos =
   (let multi = find_bool (implode "--multi=") ls
     (clos_to_bvl_config_do_mti clos) in
   let known' = find_bool (implode "--known=") ls (IS_SOME
     (clos_to_bvl_config_known_conf clos)) in
   let inline_factor = find_num (implode "--inline_factor=") ls
     default_inline_factor in
   let call = find_bool (implode "--call=") ls
     (clos_to_bvl_config_do_call clos) in
   let maxapp = find_num (implode "--max_app=") ls
     (clos_to_bvl_config_max_app clos) in
   match (multi,known',inline_factor,call,maxapp) with
     (INL m,INL k,INL i,INL c,INL n) ->
     (if k then
     (let max_body_size = find_num (implode "--max_body_size=") ls
       (default_max_body_size n i) in
      match max_body_size with
       (INL x) ->
       INL
         (clos_to_bvl_config_max_app_fupd (K n)
           (clos_to_bvl_config_do_call_fupd (K c)
           (clos_to_bvl_config_known_conf_fupd (K (SOME (mk_config x
           i))) (clos_to_bvl_config_do_mti_fupd (K m) clos)))) | _13 ->
           INR (concat [get_err_str max_body_size])) else
     (INL
       (clos_to_bvl_config_max_app_fupd (K n)
         (clos_to_bvl_config_do_call_fupd (K c)
         (clos_to_bvl_config_known_conf_fupd (K NONE)
         (clos_to_bvl_config_do_mti_fupd (K m) clos)))))) | _14 ->
     INR (concat [get_err_str multi;
                  get_err_str known';
                  get_err_str inline_factor;
                  get_err_str call;
                  get_err_str maxapp]))`;;

(* bvl *)
let parse_bvl_conf_def = cake_define
  `parse_bvl_conf ls bvl =
   (let inlinesz = find_num (implode "--inline_size=") ls
     (bvl_to_bvi_config_inline_size_limit bvl) in
   let expcut = find_num (implode "--exp_cut=") ls
     (bvl_to_bvi_config_exp_cut bvl) in
   let tmc = find_bool (implode "--tmc=") ls
     (bvl_to_bvi_config_do_tmc bvl) in
   let tailrec = find_bool (implode "--tailrec=") ls
     (bvl_to_bvi_config_do_tailrec bvl) in
   let splitmain = find_bool (implode "--split=") ls
     (bvl_to_bvi_config_split_main_at_seq bvl) in
   match (inlinesz,expcut,splitmain,tmc,tailrec) with
     (INL i,INL e,INL m,INL do_tmc,INL do_tailrec) ->
     INL
       (bvl_to_bvi_config_do_tailrec_fupd (K do_tailrec)
         (bvl_to_bvi_config_do_tmc_fupd (K do_tmc)
         (bvl_to_bvi_config_split_main_at_seq_fupd (K m)
         (bvl_to_bvi_config_exp_cut_fupd (K e)
         (bvl_to_bvi_config_inline_size_limit_fupd (K i) bvl))))) | _15
         ->
     INR (concat [get_err_str inlinesz;
                  get_err_str expcut;
                  get_err_str splitmain;
                  get_err_str tmc;
                  get_err_str tailrec]))`;;

(* wtw *)
let parse_wtw_conf_def = cake_define
  `parse_wtw_conf ls wtw =
     (let regalg = find_num (implode "--reg_alg=") ls
       (word_to_word_config_reg_alg wtw) in
       match regalg with
         INL r -> INL (word_to_word_config_reg_alg_fupd (K r) wtw)
           | INR s -> INR (get_err_str regalg))`;;

let parse_gc_def = cake_define
  `parse_gc ls default =
   (match find_str (implode "--gc=") ls with
     NONE -> INL default | SOME rest ->
     (if rest = (implode "none") then INL None else if rest =
       (implode "simple") then INL Simple else if isPrefix (implode
       "gen") rest then
       match parse_nums (extract rest (strlen (implode "gen")) NONE)
         with
         INL ls -> INL (data_to_word_Generational ls) | INR s ->
         INR (concat [(implode "Error parsing GenGC argument: ");
           s]) else INR (concat [(implode
           "Unrecognized GC option: "); rest])))`;;

(*
EVAL ``parse_gc [«--gc=gen1234,1234,1234»] def``
*)

(* Copy of conf_ok from data_to_word *)
let conf_ok_check_def = cake_define
  `conf_ok_check (:'a) c <=>
     shift_length c < dimindex (:'a) /\
     backend_common_word_shift (:'a) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 < dimindex (:'a)`;;

(* data *)
let parse_data_conf_def = cake_define
  `parse_data_conf ls data =
   (let tag_bits = find_num (implode "--tag_bits=") ls
     (data_to_word_config_tag_bits data) in
   let len_bits = find_num (implode "--len_bits=") ls
     (data_to_word_config_len_bits data) in
   let pad_bits = find_num (implode "--pad_bits=") ls
     (data_to_word_config_pad_bits data) in
   let len_size = find_num (implode "--len_size=") ls
     (data_to_word_config_len_size data) in
   let empty_FFI = find_bool (implode "--emit_empty_ffi=") ls
     (data_to_word_config_call_empty_ffi data) in
   let gc' = parse_gc ls (data_to_word_config_gc_kind data) in
   match (tag_bits,len_bits,pad_bits,len_size,gc',empty_FFI) with
     (INL tb,INL lb,INL pb,INL ls,INL gc',INL empty_FFI) ->
       INL (data_to_word_config_call_empty_ffi_fupd (K empty_FFI)
         (data_to_word_config_gc_kind_fupd (K gc')
         (data_to_word_config_len_size_fupd (K ls)
         (data_to_word_config_pad_bits_fupd (K pb)
         (data_to_word_config_len_bits_fupd (K lb)
         (data_to_word_config_tag_bits_fupd (K tb) data)))))) | _16 ->
      INR (concat [get_err_str tag_bits;
                   get_err_str len_bits;
                   get_err_str pad_bits;
                   get_err_str len_size;
                   get_err_str gc';
                   get_err_str empty_FFI]))`;;

(* stack *)
let parse_stack_conf_def = cake_define
  `parse_stack_conf ls stack' =
   (let jump = find_bool (implode "--jump=") ls
     (stack_to_lab_config_jump stack') in
   let perf = find_bool (implode "--perf_callgraph=") ls
     (stack_to_lab_config_perf_calls stack') in
   match (jump,perf) with
     (INL j,INL p) -> INL (stack_to_lab_config_perf_calls_fupd (K
       p) (stack_to_lab_config_jump_fupd (K j) stack')) | (INR s,_17)
       -> INR s | (_18,INR s) -> INR s)`;;

(* tap *)
let parse_tap_conf_def = cake_define
  `parse_tap_conf ls stack' =
     INL (mk_tap_config (MEMBER (implode "--explore") ls))`;;

(* lab *)
let parse_lab_conf_def = cake_define
  `parse_lab_conf ls lab =
     (let hs = find_num (implode "--hash_size=") ls
       (lab_to_target_config_hash_size lab) in
       match hs with
         INL r -> INL (lab_to_target_config_hash_size_fupd (K r)
           lab) | INR s -> INR s)`;;

let extend_conf_def = cake_define
  `extend_conf ls conf =
   (let clos = parse_clos_conf ls (backend_config_clos_conf conf) in
   let bvl = parse_bvl_conf ls (backend_config_bvl_conf conf) in
   let wtw = parse_wtw_conf ls (backend_config_word_to_word_conf
     conf) in
   let data = parse_data_conf ls (backend_config_data_conf conf) in
   let stack' = parse_stack_conf ls (backend_config_stack_conf conf)
     in
   let tap = parse_tap_conf ls (backend_config_tap_conf conf) in
   let lab = parse_lab_conf ls (backend_config_lab_conf conf) in
   match (clos,bvl,wtw,data,stack',tap,lab) with
     (INL clos,INL bvl,INL wtw,INL data,INL stack',INL tap,INL lab)
       ->
       INL (backend_config_lab_conf_fupd (K lab)
         (backend_config_tap_conf_fupd (K tap)
         (backend_config_stack_conf_fupd (K stack')
         (backend_config_data_conf_fupd (K data)
         (backend_config_word_to_word_conf_fupd (K wtw)
         (backend_config_bvl_conf_fupd (K bvl)
         (backend_config_clos_conf_fupd (K clos) conf))))))) | _19 ->
       INR (concat [get_err_str clos;
                get_err_str bvl;
                get_err_str wtw;
                get_err_str data;
                get_err_str stack';
                get_err_str tap;
                get_err_str lab]))`;;

(* Defaults to x64 if no target given *)
cake_declare "x64_config" `:(64)asm_config`;;
cake_declare "arm8_config" `:(64)asm_config`;;
cake_declare "mips_config" `:(64)asm_config`;;
cake_declare "riscv_config" `:(64)asm_config`;;
cake_declare "arm7_config" `:(32)asm_config`;;
cake_declare "ag32_config" `:(32)asm_config`;;

let parse_target_64_def = cake_define
  `parse_target_64 ls =
   (match find_str (implode "--target=") ls with
     NONE -> INL (x64_backend_config,x64_export,x64_config) | SOME
       rest ->
     (if rest = (implode "x64") then INL
       (x64_backend_config,x64_export,x64_config) else if rest =
       (implode "arm8") then INL
       (arm8_backend_config,arm8_export,arm8_config) else if rest =
       (implode "mips") then INL
       (mips_backend_config,mips_export,mips_config) else if rest =
       (implode "riscv") then INL
       (riscv_backend_config,riscv_export,riscv_config) else INR
       (concat [(implode "Unrecognized 64-bit target option: ");
       rest])))`;;

(* Defaults to arm7 if no target given *)
let parse_target_32_def = cake_define
  `parse_target_32 ls =
   (match find_str (implode "--target=") ls with
     NONE -> INL (arm7_backend_config,arm7_export,arm7_config) | SOME
       rest ->
     (if rest = (implode "arm7") then INL
       (arm7_backend_config,arm7_export,arm7_config) else if rest =
       (implode "ag32") then INL
       (ag32_backend_config,ag32_export,ag32_config) else INR (concat
       [(implode "Unrecognized 32-bit target option: "); rest])))`;;

let parse_top_config_def = cake_define
  `parse_top_config ls =
   (let sexp = find_bool (implode "--sexp=") ls F in
   let prelude = find_bool (implode "--exclude_prelude=") ls F in
   let typeinference = find_bool (implode "--skip_type_inference=")
     ls F in
   let sexpprint = MEMBER (implode "--print_sexp") ls in
   let onlyprinttypes = MEMBER (implode "--types") ls in
   let nowarnings = MEMBER (implode "--no_warn") ls in
   let mainreturn = find_bool (implode "--main_return=") ls F in
   match (sexp,prelude,typeinference,mainreturn) with
     (INL sexp,INL prelude,INL typeinference,INL mainreturn) ->
       INL
         (sexp,prelude,typeinference,onlyprinttypes,sexpprint,mainreturn
         ,nowarnings) | _20 -> INR (concat [
                get_err_str sexp;
                get_err_str prelude;
                get_err_str typeinference;
                get_err_str mainreturn]))`;;

(* Check for version flag *)
let has_version_flag_def = cake_define
  `has_version_flag ls = MEM (implode "--version") ls`;;

(* Check for version help *)
let has_help_flag_def = cake_define
  `has_help_flag ls = MEM (implode "--help") ls`;;

(* Check for pancake flag *)
let has_pancake_flag_def = cake_define
  `has_pancake_flag ls = MEM (implode "--pancake") ls`;;

let format_compiler_result_def = cake_define_list
  [`format_compiler_result bytes_export (M_failure err) =
      ((List []:mlstring app_list),error_to_str err)`;
   `format_compiler_result bytes_export (M_success ((bytes:word8
  list),(data:('a word) list),(c:backend_config))) =
      (bytes_export (the [] (lab_to_target_config_ffi_names
        (backend_config_lab_conf c))) bytes data,implode "")`];;

(* FIXME TODO: this is an awful workaround to avoid implementing a file
   writer
   right now. *)
let add_tap_output_def = cake_define
  `add_tap_output td out =
     (if td = misc_Nil then out else td:mlstring app_list)`;;

(* The top-level compiler with everything instantiated except it doesn't
   do exporting *)

(* The top-level compiler with almost everything instantiated except the
   top-level configuration *)
cake_declare "basis" `:dec list`;;

let compile_64_def = cake_define
  `compile_64 cl input =
   (let confexp = parse_target_64 cl in
   let topconf = parse_top_config cl in
   match (confexp,topconf) with
     (INL (conf,export,aconf),INL
       (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret,nowarn))
       ->
     (let ext_conf = extend_conf cl conf in
     match ext_conf with
       INL ext_conf ->
         (let compiler_conf =
           mk_compiler_config init_config ext_conf aconf sexp prelude
             typeinfer onlyprinttypes sexpprint in
         (match compiler_compile compiler_conf basis input with
           (M_success (bytes,data,c),td) ->
             (add_tap_output td (export
               (
                 ffinames_to_string_list (the []
                   (lab_to_target_config_ffi_names
                   (backend_config_lab_conf c))))
                 bytes data (backend_config_symbols c)
                   (backend_config_exported c) mainret F),
               implode "") | (M_failure err,td) -> (add_tap_output td
                 (List []),error_to_str err))) | INR err ->
     (List [],error_to_str (ConfigError (get_err_str ext_conf)))) |
       _21 ->
     (List [],error_to_str (ConfigError (concat [get_err_str
       confexp; get_err_str topconf]))))`;;

let pancake_backend_conf_def = cake_define
  `pancake_backend_conf c = backend_config_data_conf_fupd (K
  (data_to_word_config_gc_kind_fupd (K None) (backend_config_data_conf
  c)))
     c`;;

let compile_pancake_64_def = cake_define
  `compile_pancake_64 cl input =
   (let confexp = parse_target_64 cl in
   match confexp with INR err -> (List [],error_to_str (ConfigError
     err)) | INL (conf,export,aconf) ->
       (let topconf = parse_top_config cl in
       match (topconf) with INR err -> (List [],error_to_str
         (ConfigError err)) | INL
         (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret
         ,nowarn) ->
           (let ext_conf = extend_conf cl conf in
           match ext_conf with INR err ->
               (List [],error_to_str (ConfigError (get_err_str
                 ext_conf))) | INL ext_conf ->
               (let ext_conf = pancake_backend_conf ext_conf in
               match compile_pancake aconf ext_conf input with
                 (M_failure err,td,warns) ->
                   (List [],concat (MAP error_to_str (err :: (if
                     nowarn then [] else warns)))) | (M_success
                     (bytes,data,c),td,warns) ->
                   (add_tap_output td
                     (export (ffinames_to_string_list
                       (the [] (lab_to_target_config_ffi_names
                         (backend_config_lab_conf c)))) bytes data
                         (backend_config_symbols c)
                         (backend_config_exported
                       c) mainret T),
                    concat (MAP error_to_str (if nowarn then []
                      else warns)))))))`;;

(* PENDING: the file system of the basis library, which the port does
not have (add_stdout, add_stderr, fastForwardFD)
Definition full_compile_64_def:
  full_compile_64 cl inp fs =
  if has_help_flag cl then
    add_stdout fs help_string
  else if has_version_flag cl then
    add_stdout fs current_build_info_str
  else
    let (out, err) =
        if has_pancake_flag cl then
          compile_pancake_64 cl inp
        else
          compile_64 cl inp
    in
      add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out)))
        err
End *)

let compile_32_def = cake_define
  `compile_32 cl input =
   (let confexp = parse_target_32 cl in
   let topconf = parse_top_config cl in
   match (confexp,topconf) with
     (INL (conf,export,aconf),INL
       (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret,nowarn))
       ->
     (let ext_conf = extend_conf cl conf in
     match ext_conf with
       INL ext_conf ->
         (let compiler_conf =
           mk_compiler_config init_config ext_conf aconf sexp prelude
             typeinfer onlyprinttypes sexpprint in
         (match compiler_compile compiler_conf basis input with
           (M_success (bytes,data,c),td) ->
             (add_tap_output td (export
               (ffinames_to_string_list
                 (the [] (lab_to_target_config_ffi_names
                   (backend_config_lab_conf c))))
                 bytes data (backend_config_symbols c)
                   (backend_config_exported c) mainret F),
               implode "") | (M_failure err,td) -> (List
                 [],error_to_str err))) | INR err ->
     (List [],error_to_str (ConfigError (get_err_str ext_conf)))) |
       _22 ->
     (List [],error_to_str (ConfigError (concat [get_err_str
       confexp; get_err_str topconf]))))`;;

let compile_pancake_32_def = cake_define
  `compile_pancake_32 cl input =
   (let confexp = parse_target_32 cl in
   match confexp with INR err -> (List [],error_to_str (ConfigError
     err)) | INL (conf,export,aconf) ->
       (let topconf = parse_top_config cl in
       match (topconf) with INR err -> (List [],error_to_str
         (ConfigError err)) | INL
         (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret
         ,nowarn) ->
           (let ext_conf = extend_conf cl conf in
           match ext_conf with INR err ->
               (List [],error_to_str (ConfigError (get_err_str
                 ext_conf))) | INL ext_conf ->
               (let ext_conf = pancake_backend_conf ext_conf in
               match compile_pancake aconf ext_conf input with
                 (M_failure err,td,warns) ->
                   (List [],concat (MAP error_to_str (err :: (if
                     nowarn then [] else warns)))) | (M_success
                     (bytes,data,c),td,warns) ->
                   (add_tap_output td
                     (export (ffinames_to_string_list
                       (the [] (lab_to_target_config_ffi_names
                         (backend_config_lab_conf c)))) bytes data
                         (backend_config_symbols c)
                         (backend_config_exported
                       c) mainret T),
                    concat (MAP error_to_str (if nowarn then []
                      else warns)))))))`;;

(* PENDING: the file system of the basis library, which the port does
not have (add_stdout, add_stderr, fastForwardFD)
Definition full_compile_32_def:
  full_compile_32 cl inp fs =
  if has_help_flag cl then
    add_stdout fs help_string
  else if has_version_flag cl then
    add_stdout fs current_build_info_str
  else
    let (out, err) =
        if has_pancake_flag cl then
          compile_pancake_32 cl inp
        else
          compile_32 cl inp
    in
      add_stderr (add_stdout (fastForwardFD fs 0) (concat (append out)))
        err
End *)
