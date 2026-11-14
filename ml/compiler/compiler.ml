(* ======================================================== *)
(*  compiler: ported from HOL4's
    compiler/compilerScript.sml
    A definition theory, with 48 definitions, 2 datatypes and no
    theorems.  Needed by compilerProof.ml.  *)
(* ======================================================== *)

(*
  Definition of the CakeML compiler as a function that takes a list of command
  line arguments and a string corresponding to standard input, and produces a
  pair of output strings for standard error and standard output (the latter
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
needs "compiler/backend/backend_passes.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/data_to_word.ml";;
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
needs "lib/location.ml";;
needs "lib/multiword.ml";;
needs "lib/peg.ml";;
needs "lib/pegexec.ml";;
needs "lib/simpleSexpParse.ml";;
needs "misc/misc.ml";;
needs "pancake/panLang.ml";;
needs "semantics/ast.ml";;
needs "semantics/lexer_fun.ml";;
needs "translator/monadic/monad_base/ml_monadBase.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "compiler"
  ["ag32_config"; "arm7_config"; "arm8_config"; "backend";
   "backend_passes"; "cmlParse"; "evaluateProps"; "export_ag32";
   "export_arm7"; "export_arm8"; "export_mips"; "export_riscv";
   "export_x64"; "fromSexp"; "infer"; "lexer_fun"; "lexer_impl";
   "mips_config"; "mlint"; "mlstring"; "panLang"; "primSemEnv";
   "riscv_config"; "semanticPrimitivesProps"; "semantics";
   "typeSoundInvariants"; "typeSysProps"; "x64_config"];;
(* HOL4 ancestors outside the port: basisProg panPtreeConversion
   pan_to_target panStatic pan_passes *)

let staterr_INDUCT,staterr_RECURSION = define_datatype
  "staterr = ScopeErr (mlstring) | WarningErr (mlstring) \
             | GenErr (mlstring) | ShapeErr (mlstring)";;

(* HOL4 compilerScript.sml:18-117: ML code, not ported *)

(* == Build info =========================================================== *)

(* HOL4 compilerScript.sml:121: ML code, not ported *)
(*"" *)

(* HOL4 compilerScript.sml:126-127: ML code, not ported *)

let print_option_def = new_definition
  `print_option h x =
     (match x with
       NONE -> (implode "") | SOME y -> (\x y. strcat x y) ((\x y.
         strcat x y) ((\x y. strcat x y) h (implode " ")) y) (implode
         "\n"))`;;

(* HOL4 compilerScript.sml:136-145: the ML values that the
   definitions below antiquote *)

let current_build_info_str_def = new_definition
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

(* ========================================================================= *)

let compiler_config_FIELDS = define_record "compiler_config"
  ["inferencer_config","inf_env";
   "backend_config","backend_config";
   "asm_config","'a asm_config";
   "input_is_sexp","bool";
   "exclude_prelude","bool";
   "skip_type_inference","bool";
   "only_print_types","bool";
   "only_print_sexp","bool"];;

(* HOL4 compilerScript.sml:166-167: ML code, not ported *)

(* HOL4 compilerScript.sml:169-172: ML code, not ported *)

(* HOL4 takes this string from the quotation of the --help text at
   the head of the source, without its first line (the ML code of
   help_string_tm above).  The port writes the text out and makes
   the term of it, because a string literal of HOL Light holds the
   characters that are in it, and this text has newlines and a
   backquote in it. *)

let help_string_def = new_definition
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

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let find_next_newline_def,find_next_newline_ind = define_wf
  `MEASURE (\(n,s). strlen s - n)`
  [`find_next_newline n s =
     (if strlen s <= n then n else
       if strsub s n = (CHR 10) then n else
         find_next_newline (n + 1) s)`];;

let safe_substring_def = new_definition
  `safe_substring s n l =
     (let k = strlen s in
       if k <= n then (implode "") else
         if n + l <= k then
           substring s n l else substring s n (k - n))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let get_nth_line_def,get_nth_line_ind = define_wf
  `MEASURE (\(x0,x1,x2). (\n. n) x0)`
  [`get_nth_line k s n =
     (if k = 0 then
       let n1 = find_next_newline n s in
         safe_substring s n (n1 - n) else
       get_nth_line (k - (1:num)) s (find_next_newline n s + 1))`];;

let locs_to_string_def = new_definition
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
             mlstring_concat (APPEND (REPLICATE c (implode " "))
               (REPLICATE ((stop - c) + 1) (implode [CHR 94]))) in
             mlstring_concat [(implode "line "); mlint_toString (r +
               (&1)); (implode "\n\n");
                     line; (implode "\n");
                     underline; (implode "\n")]) | _4 -> implode
                       "unknown location")`;;

(* this is a rather annoying feature of peg_exec requiring locs... *)
(* HOL4 compilerScript.sml:231: the overload add_locs, which the port
   expands *)

let parse_sexp_input_def = new_definition
  `parse_sexp_input input =
     (let err = (implode "Parsing of sexp syntax failed") in
       match parse_sexp ((MAP (\c. (c,unknown_loc))) input) with
         NONE -> INL err | SOME x -> (match sexplist sexpdec x with
         NONE -> INL err | SOME x -> INR x))`;;

let parse_cml_input_def = new_definition
  `parse_cml_input input =
     (match parse_prog (lexer_fun input) with peg_Failure l _5 ->
       INL ((\x y. strcat x y) (implode "Parsing failed at ")
       (locs_to_string (implode input) (SOME l))) | peg_Success _6 x
       _7 -> INR x)`;;

let compiler_compile_def = new_definition
  `compiler_compile c prelude input =
     (let _8 = empty_ffi (implode "finished: start up") in
     match
       (if compiler_config_input_is_sexp c then parse_sexp_input
         input else parse_cml_input input) with INL msg -> (M_failure
         (ParseError msg),misc_Nil) | INR prog ->
        (let _9 = empty_ffi (implode "finished: lexing and parsing")
          in
        let full_prog = (if compiler_config_exclude_prelude c then
          prog else APPEND prelude prog) in
        match
          (if compiler_config_skip_type_inference c then M_success
            (compiler_config_inferencer_config c) else infertype_prog
            (compiler_config_inferencer_config c) full_prog) with
            M_failure (locs,msg) ->
            (M_failure (TypeError (mlstring_concat [msg; (implode
              " at ");
                locs_to_string (implode input) locs])),misc_Nil) |
                  M_success ic ->
           (let _10 = empty_ffi (implode "finished: type inference")
             in
           if compiler_config_only_print_types c then
             (M_failure (TypeError (mlstring_concat (APPEND (APPEND
               [(implode "\n")]
                              (inf_env_to_types_string ic))
                              [(implode "\n")]))),misc_Nil) else if
                                compiler_config_only_print_sexp c then
             (M_failure (TypeError (implode
                (APPEND "\n" (print_sexp (listsexp (MAP decsexp
                  full_prog)))))),misc_Nil) else
           match compile_tap (compiler_config_asm_config c)
             (compiler_config_backend_config c) full_prog with
             (NONE,td) -> (M_failure AssembleError,td) | (SOME
             (bytes,data,c),td) -> (M_success (bytes,data,c),td))))`;;

cake_declare "parse_topdecs_to_ast"
  `:string -> (('a)decl)list + (mlstring#locs)list`;;
cake_declare "static_check"
  `:(('a)decl)list -> (1,staterr)errorMonad_error#(staterr)list`;;
cake_declare "pan_compile_tap"
  `:('a)asm_config -> backend_config -> (('a)decl)list ->
    ((((8)word)list#(('a)word)list#backend_config)option)#
    (mlstring)app_list`;;

let compile_pancake_def = new_definition
  `compile_pancake asm_conf c input =
   (let _11 = empty_ffi (implode "finished: start up") in
   match parse_topdecs_to_ast input with INR errs ->
     ((M_failure (ParseError (mlstring_concat
        (MAP (\(msg,loc). mlstring_concat [msg; (implode " at ");
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
let error_to_str_def = define_cases
  [`error_to_str (ParseError s) =
         mlstring_concat [(implode "### ERROR: parse error\n");
           s; (implode "\n")]`;
   `error_to_str (TypeError s) =
         // if the first char in the message is a newline char then it isn't an error
         (if (if strlen s = 0 then T else
             if strsub s 0 = (CHR 10) then F else T) then
           mlstring_concat [(implode "### ERROR: type error\n");
             s; (implode "\n")] else s)`;
   `error_to_str (ConfigError s) = mlstring_concat [(implode
  "### ERROR: config error\n"); s; (implode "\n")]`;
   `error_to_str AssembleError = (implode
  "### ERROR: assembly error\n")`;
   `error_to_str (StaticError e) =
        (match e with
          ScopeErr s -> mlstring_concat [(implode
            "### ERROR: scope error\n"); s; (implode "\n")] |
            WarningErr s -> mlstring_concat [(implode
            "# WARNING:\n"); s; (implode "\n")] | GenErr s ->
            mlstring_concat [(implode "### ERROR: static error\n");
            s; (implode "\n")] | ShapeErr s -> mlstring_concat
            [(implode "### ERROR: shape error\n"); s; (implode
            "\n")])`];;

let is_error_msg_def = new_definition
  `is_error_msg x = isPrefix (implode "###") x`;;

(* TODO: translator fails inside mlstringLib.mlstring_case_conv
  when the following definition just matches against (strlit str) directly *)
let parse_num_def = new_definition
  `parse_num str =
   (let str = explode str in
   if ALL isDigit str then
     SOME (num_from_dec_string_alt str) else NONE)`;;

let parse_bool_def = new_definition
  `parse_bool str =
   (if str = (implode "true") then SOME T else if str = (implode
     "false") then SOME F else NONE)`;;

(* Finds the first occurence of the flag and
  returns the rest of the string after it *)
let find_str_def,find_str_ind = define_rec
  [`find_str flag [] = NONE`;
   `find_str flag (CONS x xs) =
        (if isPrefix flag x then
          SOME (mlstring_extract x (strlen flag) NONE) else
          find_str flag xs)`];;

(* Finds all occurences of the flag as a prefix, returning
   the remainder in each occurence. *)
let find_strs_def,find_strs_ind = define_rec
  [`find_strs flag [] = []`;
   `find_strs flag (CONS x xs) =
        (if isPrefix flag x then CONS (mlstring_extract x (strlen
          flag) NONE) (find_strs flag xs) else
          find_strs flag xs)`];;

(* If flag is not present then F, else if it is present then
   we should not get any config string afterwards *)
let find_bool_def = new_definition
  `find_bool flag ls default =
   (match find_str flag ls with
     NONE -> INL default | SOME rest ->
     (match parse_bool rest with
       SOME b -> INL b | NONE -> INR (mlstring_concat [(implode
         "Unable to parse as bool: "); rest; (implode " for flag: ");
         flag])))`;;

(* If flag is not present then INL default, else if it is present then
   the rest of the config string should be a number *)
let find_num_def = new_definition
  `find_num flag ls default =
   (match find_str flag ls with
     NONE -> INL default | SOME rest ->
   (match parse_num rest with
     SOME n -> INL n | NONE -> INR (mlstring_concat [(implode
       "Unable to parse as num: "); rest; (implode " for flag: ");
       flag])))`;;

let get_err_str_def = define_cases
  [`get_err_str (INL n) = (implode "")`;
   `get_err_str (INR n) = mlstring_concat [n; (implode "\n")]`];;

(* All the numbers must parse *)
let parse_num_list_def,parse_num_list_ind = define_rec
  [`parse_num_list [] = INL []`;
   `parse_num_list (CONS x xs) =
         (match parse_num x with
           NONE -> INR (mlstring_concat [(implode
             "Unable to parse as num: "); x]) | SOME n ->
           (match parse_num_list xs with
             INR s -> INR s | INL ns -> INL (CONS n ns)))`];;

let comma_tokens_def,comma_tokens_ind = define_rec
  [`comma_tokens acc (xs:string) [] = (if NULL xs then acc else
  APPEND acc [implode xs])`;
   `comma_tokens acc (xs:string) (CONS c (cs:string)) =
        (if c = (CHR 44) then
          comma_tokens (APPEND acc (if NULL xs then [] else [implode
            xs])) [] cs else
          comma_tokens acc (APPEND xs [c]) cs)`];;


let parse_nums_def = new_definition
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
let parse_clos_conf_def = new_definition
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
           INR (mlstring_concat [get_err_str max_body_size])) else
     (INL
       (clos_to_bvl_config_max_app_fupd (K n)
         (clos_to_bvl_config_do_call_fupd (K c)
         (clos_to_bvl_config_known_conf_fupd (K NONE)
         (clos_to_bvl_config_do_mti_fupd (K m) clos)))))) | _14 ->
     INR (mlstring_concat [get_err_str multi;
                  get_err_str known';
                  get_err_str inline_factor;
                  get_err_str call;
                  get_err_str maxapp]))`;;

(* bvl *)
let parse_bvl_conf_def = new_definition
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
     INR (mlstring_concat [get_err_str inlinesz;
                  get_err_str expcut;
                  get_err_str splitmain;
                  get_err_str tmc;
                  get_err_str tailrec]))`;;

(* wtw *)
let parse_wtw_conf_def = new_definition
  `parse_wtw_conf ls wtw =
     (let regalg = find_num (implode "--reg_alg=") ls
       (word_to_word_config_reg_alg wtw) in
       match regalg with
         INL r -> INL (word_to_word_config_reg_alg_fupd (K r) wtw)
           | INR s -> INR (get_err_str regalg))`;;

let parse_gc_def = new_definition
  `parse_gc ls default =
   (match find_str (implode "--gc=") ls with
     NONE -> INL default | SOME rest ->
     (if rest = (implode "none") then INL data_to_word_None else if
       rest = (implode "simple") then INL data_to_word_Simple else if
       isPrefix (implode "gen") rest then
       match parse_nums (mlstring_extract rest (strlen (implode
         "gen")) NONE) with
         INL ls -> INL (data_to_word_Generational ls) | INR s ->
         INR (mlstring_concat [(implode
           "Error parsing GenGC argument: "); s]) else INR
           (mlstring_concat [(implode "Unrecognized GC option: ");
           rest])))`;;

(*
EVAL ``parse_gc [«--gc=gen1234,1234,1234»] def``
*)

(* Copy of conf_ok from data_to_word *)
let conf_ok_check_def = new_definition
  `conf_ok_check (:'a) c <=>
     shift_length c < dimindex (:'a) /\
     backend_common_word_shift (:'a) <= shift_length c /\
       ~(data_to_word_config_len_size c = 0) /\
       data_to_word_config_len_size
     c + 7 < dimindex (:'a)`;;

(* data *)
let parse_data_conf_def = new_definition
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
       // TODO: check conf_ok here and raise error if violated
       INL (data_to_word_config_call_empty_ffi_fupd (K empty_FFI)
         (data_to_word_config_gc_kind_fupd (K gc')
         (data_to_word_config_len_size_fupd (K ls)
         (data_to_word_config_pad_bits_fupd (K pb)
         (data_to_word_config_len_bits_fupd (K lb)
         (data_to_word_config_tag_bits_fupd (K tb) data)))))) | _16 ->
      INR (mlstring_concat [get_err_str tag_bits;
                   get_err_str len_bits;
                   get_err_str pad_bits;
                   get_err_str len_size;
                   get_err_str gc';
                   get_err_str empty_FFI]))`;;

(* stack *)
let parse_stack_conf_def = new_definition
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
let parse_tap_conf_def = new_definition
  `parse_tap_conf ls stack' =
     INL (mk_tap_config (MEMBER (implode "--explore") ls))`;;

(* lab *)
let parse_lab_conf_def = new_definition
  `parse_lab_conf ls lab =
     (let hs = find_num (implode "--hash_size=") ls
       (lab_to_target_config_hash_size lab) in
       match hs with
         INL r -> INL (lab_to_target_config_hash_size_fupd (K r)
           lab) | INR s -> INR s)`;;

let extend_conf_def = new_definition
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
       INR (mlstring_concat [get_err_str clos;
                get_err_str bvl;
                get_err_str wtw;
                get_err_str data;
                get_err_str stack';
                get_err_str tap;
                get_err_str lab]))`;;

(* Defaults to x64 if no target given *)
(* HOL4 x64_targetScript.sml:226-248, arm8_targetScript.sml:298-341,
   mips_targetScript.sml:118-337, riscv_targetScript.sml:88-303,
   arm7_targetScript.sml:263-293 and ag32_targetScript.sml:243-265:
   the asm configuration of the six targets.  Every field of one of
   them is data, except the encoder -- and the valid_imm of arm8 and
   of arm7, which needs the model as well (arm8's is data but for
   the EncodeBitMask of it, arm7's is IS_SOME o EncodeARMImmediate).
   Those get an implicit definition, which says nothing about their
   value; the configurations themselves are definitions of the port.
   The fields of an asm_config, in the order in which the port
   declares them (compiler/encoders/asm/asm.ml), are ISA, encode,
   big_endian, code_alignment, link_reg, avoid_regs, reg_count,
   fp_reg_count, two_reg_arith, valid_imm, addr_offset, hw_offset,
   byte_offset, jump_offset, cjump_offset and loc_offset; the
   comments below name the ones of every line.  Where the source
   antiquotes a word that its ML computes, the port writes the
   expression that the ML evaluates, as it does everywhere else *)

cake_declare "x64_enc" `:(64)asm->word8 list`;;
cake_declare "arm8_enc" `:(64)asm->word8 list`;;
cake_declare "mips_enc" `:(64)asm->word8 list`;;
cake_declare "riscv_enc" `:(64)asm->word8 list`;;
cake_declare "arm7_enc" `:(32)asm->word8 list`;;
cake_declare "ag32_enc" `:(32)asm->word8 list`;;
cake_declare "arm8_valid_immediate" `:binop+cmp->(64)word->bool`;;
cake_declare "arm7_valid_immediate" `:(32)word->bool`;;

let x64_config_def = new_definition
  `x64_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       x86_64 x64_enc F 0 NONE [4; 5]
       // reg_count fp_reg_count two_reg_arith
       16 8 T
       // valid_imm
       (\b i. sw2sw (INT_MINw:(32)word) <= i /\
              i <= sw2sw (INT_MAXw:(32)word))
       // addr_offset hw_offset byte_offset
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(32)word) + n2w 13,
        sw2sw (INT_MAXw:(32)word) + n2w 5)
       (sw2sw (INT_MINw:(32)word) + n2w 13,
        sw2sw (INT_MAXw:(32)word) + n2w 5)
       (sw2sw (INT_MINw:(32)word) + n2w 7,
        sw2sw (INT_MAXw:(32)word) + n2w 7)`;;

let arm8_config_def = new_definition
  `arm8_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg
       ARMv8 arm8_enc F 2 (SOME 30)
       // avoid_regs: register x18 is reserved on some platforms,
       // e.g., Apple platforms
       [18; 26; 31]
       // reg_count fp_reg_count two_reg_arith valid_imm
       32 0 F arm8_valid_immediate
       // addr_offset hw_offset, each (-off_max12 + off_min9,
       // off_max12 + off_max9)
       (--(w2w (UINT_MAXw:(12)word)) + sw2sw (INT_MINw:(9)word),
        w2w (UINT_MAXw:(12)word) + sw2sw (INT_MAXw:(9)word))
       (--(w2w (UINT_MAXw:(12)word)) + sw2sw (INT_MINw:(9)word),
        w2w (UINT_MAXw:(12)word) + sw2sw (INT_MAXw:(9)word))
       // byte_offset
       (sw2sw (INT_MINw:(9)word),w2w (UINT_MAXw:(12)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(28)word),sw2sw (INT_MAXw:(28)word))
       (sw2sw (INT_MINw:(21)word) + n2w 4,
        sw2sw (INT_MAXw:(21)word) + n2w 4)
       (sw2sw (INT_MINw:(32)word),sw2sw (INT_MAXw:(32)word))`;;

let mips_config_def = new_definition
  `mips_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       MIPS mips_enc T 2 (SOME 31) [0; 1; 25; 26; 27; 28; 29; 30]
       // reg_count fp_reg_count two_reg_arith
       32
       // 32
       0 F
       // valid_imm
       (\b i. if b IN {INL And,INL Or,INL Xor,INR Test,
                       INR NotTest}
              then n2w 0 <= i /\ i <= w2w (UINT_MAXw:(16)word)
              else (if b = INL Sub then sw2sw (INT_MINw:(16)word) < i
                    else sw2sw (INT_MINw:(16)word) <= i) /\
                   i <= sw2sw (INT_MAXw:(16)word))
       // addr_offset hw_offset byte_offset
       (sw2sw (INT_MINw:(16)word),sw2sw (INT_MAXw:(16)word))
       (sw2sw (INT_MINw:(16)word),sw2sw (INT_MAXw:(16)word))
       (sw2sw (INT_MINw:(16)word),sw2sw (INT_MAXw:(16)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(32)word) + n2w 12,
        sw2sw (INT_MAXw:(32)word) + n2w 8)
       (sw2sw (INT_MINw:(18)word) + n2w 8,
        sw2sw (INT_MAXw:(18)word) + n2w 4)
       (sw2sw (INT_MINw:(32)word) + n2w 12,
        sw2sw (INT_MAXw:(32)word) + n2w 8)`;;

let riscv_config_def = new_definition
  `riscv_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg
       RISC_V riscv_enc F 2 (SOME 1)
       // avoid_regs: calling conventions:
       // https://riscv.org/specifications/, p109
       // 0 - hardwired zero
       // 2 - stack pointer
       // 3 - global pointer
       // 4 - thread pointer
       // 31 - used by encoder above
       [0; 2; 3; 4; 31]
       // reg_count fp_reg_count two_reg_arith
       32 0 F
       // valid_imm
       (\b i. (if b = INL Sub then sw2sw (INT_MINw:(12)word) < i
               else sw2sw (INT_MINw:(12)word) <= i) /\
              i <= sw2sw (INT_MAXw:(12)word))
       // addr_offset hw_offset byte_offset
       (sw2sw (INT_MINw:(12)word),sw2sw (INT_MAXw:(12)word))
       (sw2sw (INT_MINw:(12)word),sw2sw (INT_MAXw:(12)word))
       (sw2sw (INT_MINw:(12)word),sw2sw (INT_MAXw:(12)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(32)word),n2w 2147481599)
       (sw2sw (INT_MINw:(21)word) + n2w 8,
        sw2sw (INT_MAXw:(21)word) + n2w 4)
       (sw2sw (INT_MINw:(32)word),n2w 2147481599)`;;

let arm7_config_def = new_definition
  `arm7_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       ARMv7 arm7_enc F 2 (SOME 14) [13; 15]
       // reg_count fp_reg_count two_reg_arith
       16 32 F
       // valid_imm
       (\c i. arm7_valid_immediate i)
       // addr_offset
       (--(w2w (UINT_MAXw:(12)word)),w2w (UINT_MAXw:(12)word))
       // hw_offset
       (--(w2w (UINT_MAXw:(8)word)),w2w (UINT_MAXw:(8)word))
       // byte_offset
       (--(w2w (UINT_MAXw:(12)word)),w2w (UINT_MAXw:(12)word))
       // jump_offset cjump_offset loc_offset
       (sw2sw (INT_MINw:(26)word) + n2w 8,
        sw2sw (INT_MAXw:(26)word) + n2w 8)
       (sw2sw (INT_MINw:(26)word) + n2w 12,
        sw2sw (INT_MAXw:(26)word) + n2w 12)
       (INT_MINw,INT_MAXw)`;;

let ag32_config_def = new_definition
  `ag32_config =
     mk_asm_config
       // ISA encode big_endian code_alignment link_reg avoid_regs
       Ag32 ag32_enc F 2 (SOME 0) [63]
       // reg_count fp_reg_count two_reg_arith
       64 0 F
       // valid_imm
       (\i n. if ISL i
              then --(n2w 8388607) <= n /\ n < n2w 8388607
              else --(n2w 32) <= n /\ n < n2w 32)
       // addr_offset hw_offset byte_offset
       (--(n2w 8388607),n2w 8388607)
       (--(n2w 8388607),n2w 8388607)
       (--(n2w 32),n2w 31)
       // jump_offset cjump_offset loc_offset
       (--(n2w 2147483647) + n2w 4,n2w 2147483647)
       (--(n2w 2147483647) + n2w 4,n2w 2147483647)
       (--(n2w 2147483647) + n2w 4,n2w 2147483647)`;;

let parse_target_64_def = new_definition
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
       (mlstring_concat [(implode
       "Unrecognized 64-bit target option: "); rest])))`;;

(* Defaults to arm7 if no target given *)
let parse_target_32_def = new_definition
  `parse_target_32 ls =
   (match find_str (implode "--target=") ls with
     NONE -> INL (arm7_backend_config,arm7_export,arm7_config) | SOME
       rest ->
     (if rest = (implode "arm7") then INL
       (arm7_backend_config,arm7_export,arm7_config) else if rest =
       (implode "ag32") then INL
       (ag32_backend_config,ag32_export,ag32_config) else INR
       (mlstring_concat [(implode
       "Unrecognized 32-bit target option: "); rest])))`;;

let parse_top_config_def = new_definition
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
         ,nowarnings) | _20 -> INR (mlstring_concat [
                get_err_str sexp;
                get_err_str prelude;
                get_err_str typeinference;
                get_err_str mainreturn]))`;;

(* Check for version flag *)
let has_version_flag_def = new_definition
  `has_version_flag ls = MEM (implode "--version") ls`;;

(* Check for version help *)
let has_help_flag_def = new_definition
  `has_help_flag ls = MEM (implode "--help") ls`;;

(* Check for pancake flag *)
let has_pancake_flag_def = new_definition
  `has_pancake_flag ls = MEM (implode "--pancake") ls`;;

let format_compiler_result_def = define_cases
  [`format_compiler_result bytes_export (M_failure err) =
      ((misc_List []:mlstring app_list),error_to_str err)`;
   `format_compiler_result bytes_export (M_success ((bytes:word8
  list),(data:('a word) list),(c:backend_config))) =
      (bytes_export (the [] (lab_to_target_config_ffi_names
        (backend_config_lab_conf c))) bytes data,implode "")`];;

(* FIXME TODO: this is an awful workaround to avoid implementing a file writer
   right now. *)
let add_tap_output_def = new_definition
  `add_tap_output td out =
     (if td = misc_Nil then out else td:mlstring app_list)`;;

(* The top-level compiler with everything instantiated except it doesn't do exporting *)

(* The top-level compiler with almost everything instantiated except the top-level configuration *)
cake_declare "basis" `:dec list`;;

let compile_64_def = new_definition
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
           mk_compiler_config infer_init_config ext_conf aconf sexp
             prelude typeinfer onlyprinttypes sexpprint in
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
                 (misc_List []),error_to_str err))) | INR err ->
     (misc_List [],error_to_str (ConfigError (get_err_str
       ext_conf)))) | _21 ->
     (misc_List [],error_to_str (ConfigError (mlstring_concat
       [get_err_str confexp; get_err_str topconf]))))`;;

let pancake_backend_conf_def = new_definition
  `pancake_backend_conf c = backend_config_data_conf_fupd (K
  (data_to_word_config_gc_kind_fupd (K data_to_word_None)
  (backend_config_data_conf c)))
     c`;;

let compile_pancake_64_def = new_definition
  `compile_pancake_64 cl input =
   (let confexp = parse_target_64 cl in
   match confexp with INR err -> (misc_List [],error_to_str
     (ConfigError err)) | INL (conf,export,aconf) ->
       (let topconf = parse_top_config cl in
       match (topconf) with INR err -> (misc_List [],error_to_str
         (ConfigError err)) | INL
         (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret
         ,nowarn) ->
           (let ext_conf = extend_conf cl conf in
           match ext_conf with INR err ->
               (misc_List [],error_to_str (ConfigError (get_err_str
                 ext_conf))) | INL ext_conf ->
               (let ext_conf = pancake_backend_conf ext_conf in
               match compile_pancake aconf ext_conf input with
                 (M_failure err,td,warns) ->
                   (misc_List [],mlstring_concat (MAP error_to_str
                     (CONS err (if nowarn then [] else warns)))) |
                     (M_success (bytes,data,c),td,warns) ->
                   (add_tap_output td
                     (export (ffinames_to_string_list
                       (the [] (lab_to_target_config_ffi_names
                         (backend_config_lab_conf c)))) bytes data
                         (backend_config_symbols c)
                         (backend_config_exported
                       c) mainret T),
                    mlstring_concat (MAP error_to_str (if nowarn
                      then [] else warns)))))))`;;

(* PENDING: the file system of the basis library, which the port does
   not have (add_stdout, add_stderr, fastForwardFD) *)
(* HOL4 compilerScript.sml:759-773: the definition *)

let compile_32_def = new_definition
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
           mk_compiler_config infer_init_config ext_conf aconf sexp
             prelude typeinfer onlyprinttypes sexpprint in
         (match compiler_compile compiler_conf basis input with
           (M_success (bytes,data,c),td) ->
             (add_tap_output td (export
               (ffinames_to_string_list
                 (the [] (lab_to_target_config_ffi_names
                   (backend_config_lab_conf c))))
                 bytes data (backend_config_symbols c)
                   (backend_config_exported c) mainret F),
               implode "") | (M_failure err,td) -> (misc_List
                 [],error_to_str err))) | INR err ->
     (misc_List [],error_to_str (ConfigError (get_err_str
       ext_conf)))) | _22 ->
     (misc_List [],error_to_str (ConfigError (mlstring_concat
       [get_err_str confexp; get_err_str topconf]))))`;;

let compile_pancake_32_def = new_definition
  `compile_pancake_32 cl input =
   (let confexp = parse_target_32 cl in
   match confexp with INR err -> (misc_List [],error_to_str
     (ConfigError err)) | INL (conf,export,aconf) ->
       (let topconf = parse_top_config cl in
       match (topconf) with INR err -> (misc_List [],error_to_str
         (ConfigError err)) | INL
         (sexp,prelude,typeinfer,onlyprinttypes,sexpprint,mainret
         ,nowarn) ->
           (let ext_conf = extend_conf cl conf in
           match ext_conf with INR err ->
               (misc_List [],error_to_str (ConfigError (get_err_str
                 ext_conf))) | INL ext_conf ->
               (let ext_conf = pancake_backend_conf ext_conf in
               match compile_pancake aconf ext_conf input with
                 (M_failure err,td,warns) ->
                   (misc_List [],mlstring_concat (MAP error_to_str
                     (CONS err (if nowarn then [] else warns)))) |
                     (M_success (bytes,data,c),td,warns) ->
                   (add_tap_output td
                     (export (ffinames_to_string_list
                       (the [] (lab_to_target_config_ffi_names
                         (backend_config_lab_conf c)))) bytes data
                         (backend_config_symbols c)
                         (backend_config_exported
                       c) mainret T),
                    mlstring_concat (MAP error_to_str (if nowarn
                      then [] else warns)))))))`;;

(* PENDING: the file system of the basis library, which the port does
   not have (add_stdout, add_stderr, fastForwardFD) *)
(* HOL4 compilerScript.sml:835-849: the definition *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
