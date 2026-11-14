(* ======================================================== *)
(*  semanticPrimitives: ported from HOL4's
    semantics/semanticPrimitivesScript.sml
    A definition theory, with 101 definitions, 15 datatypes and no
    theorems.  Needed by 73 files of the port.  *)
(* ======================================================== *)

(*
  Definitions of semantic primitives (e.g., values, and functions for doing
  primitive operations) used in the semantics.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "lib/binary_ieee.ml";;
needs "lib/integer_word.ml";;
needs "lib/machine_ieee.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;
needs "semantics/ffi/ffi.ml";;
needs "semantics/fpSem.ml";;
needs "semantics/namespace.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "semanticPrimitives"
  ["ast"; "ffi"; "fpSem"; "misc"; "mlstring"; "namespace"];;

(* Constructors and exceptions need unique identities, which we represent by stamps. *)
let stamp_INDUCT,stamp_RECURSION = define_datatype
  "stamp = \
   // Each type gets a unique number, and the constructor name must be unique\n\
   // inside of the type\n\
   TypeStamp (mlstring) (num) | ExnStamp (num)";;

let sem_env_FIELDS = define_record "sem_env"
  ["v","(mlstring,mlstring,'v)namespace";
   (* Lexical mapping of constructor idents to arity, stamp pairs *)
   "c","(mlstring,mlstring,num#stamp)namespace"];;

(* Value forms *)
let semanticPrimitives_v_INDUCT,semanticPrimitives_v_RECURSION =
  define_datatype
  "semanticPrimitives_v = semanticPrimitives_Litv (lit) | \
   // Constructor application. Can be a tuple or a given constructor of a given type\n\
   semanticPrimitives_Conv (stamp option) (semanticPrimitives_v list) \
   | \
   // Function closures\n\
   // The environment is used for the free variables in the function\n\
   semanticPrimitives_Closure (semanticPrimitives_v sem_env) \
   (mlstring) (ast_exp) | \
   // Function closure for recursive functions\n\
   // * See Closure and Letrec above\n\
   // * The last variable name indicates which function from the mutually\n\
   // * recursive bundle this closure value represents\n\
   semanticPrimitives_Recclosure (semanticPrimitives_v sem_env) \
   ((mlstring#mlstring#ast_exp) list) (mlstring) | \
   semanticPrimitives_Loc (bool) (num) \
   // = is allowed\n\
   // address\n\
   | semanticPrimitives_Vectorv (semanticPrimitives_v list) | \
   // Environment value for Eval, and its numeric identifier\n\
   semanticPrimitives_Env (semanticPrimitives_v sem_env) (num#num)";;

new_type_abbrev("env_ctor",`: (mlstring,mlstring,num#stamp)namespace`);;
new_type_abbrev("env_val",`:
   (mlstring,mlstring,semanticPrimitives_v)namespace`);;

let bind_stamp_def = new_definition
  `bind_stamp = ExnStamp 0`;;
let chr_stamp_def = new_definition
  `chr_stamp = ExnStamp 1`;;
let div_stamp_def = new_definition
  `div_stamp = ExnStamp 2`;;
let subscript_stamp_def = new_definition
  `subscript_stamp = ExnStamp 3`;;

let bind_exn_v_def = new_definition
  `semanticPrimitives_bind_exn_v = semanticPrimitives_Conv (SOME
  bind_stamp) []`;;
let chr_exn_v_def = new_definition
  `semanticPrimitives_chr_exn_v = semanticPrimitives_Conv (SOME
  chr_stamp) []`;;
let div_exn_v_def = new_definition
  `semanticPrimitives_div_exn_v = semanticPrimitives_Conv (SOME
  div_stamp) []`;;
let sub_exn_v_def = new_definition
  `sub_exn_v = semanticPrimitives_Conv (SOME subscript_stamp) []`;;

let bool_type_num_def = new_definition
  `bool_type_num = 0`;;
let list_type_num_def = new_definition
  `list_type_num = 1`;;
let option_type_num_def = new_definition
  `option_type_num = 2`;;
let lit_type_num_def = new_definition
  `lit_type_num = 3`;;
let id_type_num_def = new_definition
  `id_type_num = 4`;;
let ast_t_type_num_def = new_definition
  `ast_t_type_num = 5`;;
let pat_type_num_def = new_definition
  `pat_type_num = 6`;;
let lop_type_num_def = new_definition
  `lop_type_num = 7`;;
let opn_type_num_def = new_definition
  `opn_type_num = 8`;;
let opb_type_num_def = new_definition
  `opb_type_num = 9`;;
let opw_type_num_def = new_definition
  `opw_type_num = 10`;;
let shift_type_num_def = new_definition
  `shift_type_num = 11`;;
let word_size_type_num_def = new_definition
  `word_size_type_num = 12`;;
let fp_uop_type_num_def = new_definition
  `fp_uop_type_num = 13`;;
let fp_bop_type_num_def = new_definition
  `fp_bop_type_num = 14`;;
let fp_top_type_num_def = new_definition
  `fp_top_type_num = 15`;;
let fp_cmp_type_num_def = new_definition
  `fp_cmp_type_num = 16`;;

let op_type_num_def = new_definition
  `op_type_num = 20`;;
let locn_type_num_def = new_definition
  `locn_type_num = 21`;;
let locs_type_num_def = new_definition
  `locs_type_num = 22`;;
let exp_type_num_def = new_definition
  `exp_type_num = 24`;;
let dec_type_num_def = new_definition
  `dec_type_num = 25`;;

(* The result of evaluation *)
let semanticPrimitives_abort_INDUCT,semanticPrimitives_abort_RECURSION =
  define_datatype
  "semanticPrimitives_abort = Rtype_error | Rtimeout_error | \
   Rffi_error (final_event)";;

let error_result_INDUCT,error_result_RECURSION = define_datatype
  "error_result = Rraise ('a) \
   // Should only be a value of type exn\n\
   | Rabort (semanticPrimitives_abort)";;

let semanticPrimitives_result_INDUCT,
    semanticPrimitives_result_RECURSION =
  define_datatype
  "semanticPrimitives_result = Rval ('a) | Rerr ('b error_result)";;

(* Stores *)
let store_v_INDUCT,store_v_RECURSION = define_datatype
  "store_v = \
   // A ref cell\n\
   semanticPrimitives_Refv ('a) | \
   // A byte array\n\
   semanticPrimitives_W8array (word8 list) | \
   // An array of values\n\
   semanticPrimitives_Varray ('a list) | \
   // Thunk\n\
   semanticPrimitives_Thunk (thunk_mode) ('a)";;

let store_v_same_type_def = new_definition
  `store_v_same_type v1 v2 =
     (match ((v1:'a store_v),(v2:'a store_v)) with
       (semanticPrimitives_Refv _1,semanticPrimitives_Refv _2) -> T |
       (semanticPrimitives_W8array _3,semanticPrimitives_W8array _4)
       -> T | (semanticPrimitives_Varray _5,semanticPrimitives_Varray
       _6) -> T | (semanticPrimitives_Thunk NotEvaluated
       _7,semanticPrimitives_Thunk _8 _9) -> T | _10 -> F)`;;

(* The nth item in the list is the value at location n *)
(* HOL4 semanticPrimitivesScript.sml:189: the type abbreviation
   store, which the port expands *)

let empty_store_def = new_definition
  `empty_store = ([]:('a store_v) list)`;;

let store_lookup_def = new_definition
  `store_lookup l (st:('a store_v) list) =
     (if l < LENGTH st then SOME (EL l st) else NONE)`;;

let store_alloc_def = new_definition
  `store_alloc (v:'a store_v) st = (APPEND st [v],LENGTH st)`;;

let store_assign_def = new_definition
  `store_assign n (v:'a store_v) st =
     (if n < LENGTH st /\ store_v_same_type (EL n st) v then
       SOME (LUPDATE v n st) else NONE)`;;

(* Compiler checker for Eval. The current design requires the compiler
   to be run (as regular code within the semantics) before Eval is called,
   and these config parameters specify how to interpret the declarations to
   be evaluated and check that the compiler was run correctly.

   Before attempting build a state of this type, find out about
   mk_init_eval_state in source_evalProof.
*)
new_type_abbrev("compiler_args",`: (num#num)#semanticPrimitives_v#dec
   list`);;
new_type_abbrev("compiler_fun",`: (num#num)#semanticPrimitives_v#dec
   list->(semanticPrimitives_v#word8 list#word64 list) option`);;

let eval_decs_state_FIELDS = define_record "eval_decs_state"
  ["compiler","(num#num)#semanticPrimitives_v#dec \
   list->(semanticPrimitives_v#word8 list#word64 list) option";
   (* state must be encoded as v somehow *)
   "compiler_state","semanticPrimitives_v";
   "env_id_counter","num#num#num";
   (* decs must also be encoded as v *)
   "decode_decs","semanticPrimitives_v->(dec list) option"];;

(* Alternative mode for Eval including an oracle.
   This is only for use in the compiler proof. *)
new_type_abbrev("eval_oracle_fun",`:
   num->(num#num)#semanticPrimitives_v#dec list`);;

let eval_oracle_state_FIELDS = define_record "eval_oracle_state"
  ["oracle","num->(num#num)#semanticPrimitives_v#dec list";
   "custom_do_eval","semanticPrimitives_v \
   list->(num->(num#num)#semanticPrimitives_v#dec \
   list)->((num#num)#(num->(num#num)#semanticPrimitives_v#dec \
   list)#dec list) option";
   "envs","((semanticPrimitives_v sem_env) list) list";
   "generation","num"];;

let eval_state_INDUCT,eval_state_RECURSION = define_datatype
  "eval_state = EvalDecs (eval_decs_state) | EvalOracle \
   (eval_oracle_state)";;

let semanticPrimitives_state_FIELDS =
  define_record "semanticPrimitives_state"
  ["clock","num";
   "refs","(semanticPrimitives_v store_v) list";
   "ffi","'ffi ffi_state";
   "next_type_stamp","num";
   "next_exn_stamp","num";
   "eval_state","eval_state option"];;

(* Other primitives *)
(* Check that a constructor is properly applied *)
let do_con_check_def = new_definition
  `do_con_check (cenv:(mlstring,mlstring,num#stamp)namespace) n_opt l
  <=>
     (match n_opt with
       NONE -> T | SOME n -> (match nsLookup cenv n with NONE -> F
         | SOME (l',v2) -> l = l'))`;;

let one_con_check_def = new_definition
  `one_con_check envc x2 =
      match x2 with
        (ast_Con cn es:ast_exp) -> do_con_check envc cn (LENGTH es)
      | _11 -> T`;;

let build_conv_def = new_definition
  `build_conv (envC:(mlstring,mlstring,num#stamp)namespace) cn vs =
   (match cn with
     NONE -> SOME (semanticPrimitives_Conv NONE vs) | SOME id' ->
       (match nsLookup envC id' with
         NONE -> NONE | SOME (len,stamp) -> SOME
           (semanticPrimitives_Conv (SOME stamp) vs)))`;;

let lit_same_type_def = new_definition
  `lit_same_type l1 l2 <=>
      (match (l1,l2) with (ast_IntLit _12,ast_IntLit _13) -> T |
        (ast_Char _14,ast_Char _15) -> T | (ast_StrLit _16,ast_StrLit
        _17) -> T | (ast_Word8 _18,ast_Word8 _19) -> T | (ast_Word64
        _20,ast_Word64 _21) -> T | (ast_Float64 _22,ast_Float64 _23)
        -> T | _24 -> F)`;;

let match_result_INDUCT,match_result_RECURSION = define_datatype
  "match_result = No_match | Match_type_error | Match ('a)";;

let same_type_def = new_definition
  `same_type x1 x2 =
        match (x1,x2) with
          (TypeStamp v0 n1,TypeStamp v1 n2) -> n1 = n2
        | ((ExnStamp v2),(ExnStamp v3)) -> T
        | (_25,_26) -> F`;;

let same_ctor_def = new_definition
  `same_ctor stamp1 stamp2 <=> stamp1 = (stamp2:stamp)`;;

let ctor_same_type_def = new_definition
  `semanticPrimitives_ctor_same_type c1 c2 <=>
    (match (c1,c2) with
      (NONE,NONE) -> T | (SOME stamp1,SOME stamp2) -> same_type
        stamp1 stamp2 | _27 -> F)`;;

let boolv_def = new_definition
  `semanticPrimitives_Boolv b =
     (if b then semanticPrimitives_Conv (SOME (TypeStamp (implode
       "True") bool_type_num)) [] else semanticPrimitives_Conv (SOME
       (TypeStamp (implode "False") bool_type_num)) [])`;;

(* A big-step pattern matcher.  If the value matches the pattern, return an
 * environment with the pattern variables bound to the corresponding sub-terms
 * of the value; this environment extends the environment given as an argument.
 * No_match is returned when there is no match, but any constructors
 * encountered in determining the match failure are applied to the correct
 * number of arguments, and constructors in corresponding positions in the
 * pattern and value come from the same type.  Match_type_error is returned
 * when one of these conditions is violated *)
let pmatch_def,pmatch_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`semanticPrimitives_pmatch envC s (ast_Pany:ast_pat) v' env =
  Match env`;
   `semanticPrimitives_pmatch envC s (ast_Pvar x:ast_pat) v' env =
  Match (CONS (x,v') env)`;
   `semanticPrimitives_pmatch envC s (ast_Plit l:ast_pat)
  (semanticPrimitives_Litv l':semanticPrimitives_v) env =
    (if l = l' then Match env else if lit_same_type l l' then
      No_match else Match_type_error)`;
   `semanticPrimitives_pmatch envC s (ast_Pcon (SOME n) ps:ast_pat)
  (semanticPrimitives_Conv (SOME stamp') vs:semanticPrimitives_v) env =
    (match nsLookup envC n with
       NONE -> Match_type_error | SOME (l,stamp) ->
         (if same_type stamp stamp' /\ LENGTH ps = l then
           if same_ctor stamp stamp' then
             if LENGTH vs = l then semanticPrimitives_pmatch_list
               envC s ps vs env else Match_type_error else No_match
               else Match_type_error))`;
   `semanticPrimitives_pmatch envC s (ast_Pcon NONE ps:ast_pat)
  (semanticPrimitives_Conv NONE vs:semanticPrimitives_v) env =
    (if LENGTH ps = LENGTH vs then semanticPrimitives_pmatch_list
      envC s ps vs env else Match_type_error)`;
   `semanticPrimitives_pmatch envC s (ast_Pref p:ast_pat)
  (semanticPrimitives_Loc _33 lnum:semanticPrimitives_v) env =
    (match store_lookup lnum s with
       NONE -> Match_type_error | SOME (semanticPrimitives_Refv
         v) -> semanticPrimitives_pmatch envC s p v env | SOME _34 ->
         Match_type_error)`;
   `semanticPrimitives_pmatch envC s (ast_Pas p i:ast_pat) v env =
  semanticPrimitives_pmatch envC s p v (CONS (i,v) env)`;
   `semanticPrimitives_pmatch envC s (ast_Ptannot p t) v env =
  semanticPrimitives_pmatch envC s p v env`;
   `semanticPrimitives_pmatch envC s _35 _36 env = Match_type_error`;
   `semanticPrimitives_pmatch_list envC s [] [] env = Match env`;
   `semanticPrimitives_pmatch_list envC s (CONS p ps) (CONS v vs) env =
    (match semanticPrimitives_pmatch envC s p v env with
       No_match ->
         (match semanticPrimitives_pmatch_list envC s ps vs env with
            No_match -> No_match | Match_type_error ->
              Match_type_error | Match v1 -> No_match) |
              Match_type_error -> Match_type_error | Match env' ->
              semanticPrimitives_pmatch_list envC s ps vs env')`;
   `semanticPrimitives_pmatch_list envC s _37 _38 env =
  Match_type_error`];;

let can_pmatch_all_def,can_pmatch_all_ind = define_rec
  [`can_pmatch_all envC refs [] v <=> T`;
   `can_pmatch_all envC refs (CONS p ps) v <=>
         (if semanticPrimitives_pmatch envC refs p v [] =
           Match_type_error then F else can_pmatch_all envC refs ps
           v)`];;

(* Bind each function of a mutually recursive set of functions to its closure *)
let build_rec_env_def = new_definition
  `(semanticPrimitives_build_rec_env:(mlstring#mlstring#ast_exp)
  list->semanticPrimitives_v
  sem_env->(mlstring,mlstring,semanticPrimitives_v)namespace->(mlstring
  ,mlstring,semanticPrimitives_v)namespace) funs cl_env add_to_env =
   ITLIST (\(f,x,e) env'. nsBind f (semanticPrimitives_Recclosure
     cl_env funs f) env') funs
         add_to_env`;;

(* Lookup in the list of mutually recursive functions *)
let find_recfun_def,find_recfun_ind = define_shaped_rec
  "match"
  [`(find_recfun:mlstring->(mlstring#'a#'b) list->('a#'b) option) n funs
  =
   (match funs with
     [] -> NONE | CONS (f,x,e) funs' -> (if f = n then SOME
       (x,e) else find_recfun n funs'))`];;

let eq_result_INDUCT,eq_result_RECURSION = define_datatype
  "eq_result = Eq_val (bool) | Eq_type_error";;

(* the clauses of do_eq_list overlap -- the last one says Eq_val F
   of the two lists that the first two have already given a value
   -- and HOL4 takes the first that matches, so the port writes
   them as a match, which takes the first arm (see ml/lib/define.ml,
   "A definition whose clauses overlap").  As a list of clauses they
   would be inconsistent. *)
let do_eq_def,do_eq_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`semanticPrimitives_do_eq (semanticPrimitives_Litv
  l1:semanticPrimitives_v) (semanticPrimitives_Litv
  l2:semanticPrimitives_v) =
      (if lit_same_type l1 l2 then Eq_val (l1 = l2) else
        Eq_type_error)`;
   `semanticPrimitives_do_eq (semanticPrimitives_Loc b1
  l1:semanticPrimitives_v) (semanticPrimitives_Loc b2
  l2:semanticPrimitives_v) =
      (if b1 /\ b2 then Eq_val (l1 = l2) else Eq_type_error)`;
   `semanticPrimitives_do_eq (semanticPrimitives_Conv cn1
  vs1:semanticPrimitives_v) (semanticPrimitives_Conv cn2
  vs2:semanticPrimitives_v) =
      (if cn1 = cn2 /\ LENGTH vs1 = LENGTH vs2 then
        semanticPrimitives_do_eq_list vs1 vs2 else if
        semanticPrimitives_ctor_same_type cn1 cn2 then Eq_val F else
        Eq_type_error)`;
   `semanticPrimitives_do_eq (semanticPrimitives_Vectorv
  vs1:semanticPrimitives_v) (semanticPrimitives_Vectorv
  vs2:semanticPrimitives_v) =
      (if LENGTH vs1 = LENGTH vs2 then
        semanticPrimitives_do_eq_list vs1 vs2 else Eq_val F)`;
   `semanticPrimitives_do_eq (semanticPrimitives_Closure v0 v3
  v4:semanticPrimitives_v) (semanticPrimitives_Closure v5 v6
  v7:semanticPrimitives_v) = Eq_val T`;
   `semanticPrimitives_do_eq (semanticPrimitives_Closure v8 v9
  v10:semanticPrimitives_v) (semanticPrimitives_Recclosure v11 v12
  v13:semanticPrimitives_v) = Eq_val T`;
   `semanticPrimitives_do_eq (semanticPrimitives_Recclosure v14 v15
  v16:semanticPrimitives_v) (semanticPrimitives_Closure v17 v18
  v19:semanticPrimitives_v) = Eq_val T`;
   `semanticPrimitives_do_eq (semanticPrimitives_Recclosure v20 v21
  v22:semanticPrimitives_v) (semanticPrimitives_Recclosure v23 v24
  v25:semanticPrimitives_v) = Eq_val T`;
   `semanticPrimitives_do_eq (semanticPrimitives_Env v26
  (gen1,id1):semanticPrimitives_v) (semanticPrimitives_Env v27
  (gen2,id2):semanticPrimitives_v) =
      Eq_val (gen1 = gen2 /\ id1 = id2)`;
   `semanticPrimitives_do_eq _41 _42 = Eq_type_error`;
   `semanticPrimitives_do_eq_list x1 x2 =
       match (x1,x2) with
         ([],[]) -> Eq_val T
       | ((CONS v1 vs1),(CONS v2 vs2)) ->
      (match semanticPrimitives_do_eq v1 v2 with
         Eq_val r -> (if ~r then Eq_val F else
           semanticPrimitives_do_eq_list vs1 vs2) | Eq_type_error ->
           Eq_type_error)
       | (_39,_40) -> Eq_val F`];;

(* Do an application *)
let do_opapp_def = new_definition
  `semanticPrimitives_do_opapp vs =
      (match vs with [semanticPrimitives_Closure env n e; v] -> SOME
        (sem_env_v_fupd (K (nsBind n v (sem_env_v env))) env,e) |
        [semanticPrimitives_Recclosure env' funs n'; v] ->
        (if ALL_DISTINCT (MAP (\(f,x,e). f) funs) then
          match find_recfun n' funs with
            NONE -> NONE | SOME (n,e) ->
            SOME
              (sem_env_v_fupd (K (nsBind n v
                (semanticPrimitives_build_rec_env funs env'
                (sem_env_v env')))) env',e) else NONE) | _43 -> NONE)`;;

(* If a value represents a list, get that list. Otherwise return Nothing *)
let _ = size_thms "semanticPrimitives_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let v_to_list_def,v_to_list_ind = define_wf
  `MEASURE (\x0. semanticPrimitives_v_size x0)`
  [`semanticPrimitives_v_to_list x1 =
      match x1 with
        (semanticPrimitives_Conv (SOME stamp)
          []:semanticPrimitives_v) ->
     (if stamp = TypeStamp (implode "[]") list_type_num then SOME []
       else NONE)
      | (semanticPrimitives_Conv (SOME stamp) [v1; v2]) ->
     (if stamp = TypeStamp (implode "::") list_type_num then
        match semanticPrimitives_v_to_list v2 with NONE -> NONE |
          SOME vs -> SOME (CONS v1 vs) else NONE)
      | _44 -> NONE`];;

let list_to_v_def,list_to_v_ind = define_rec
  [`semanticPrimitives_list_to_v [] = semanticPrimitives_Conv (SOME
  (TypeStamp (implode "[]") list_type_num)) []`;
   `semanticPrimitives_list_to_v (CONS x xs) =
  semanticPrimitives_Conv (SOME (TypeStamp (implode "::")
  list_type_num)) [x; semanticPrimitives_list_to_v xs]`];;

let _ = size_thms "semanticPrimitives_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let v_to_char_list_def,v_to_char_list_ind = define_wf
  `MEASURE (\x0. semanticPrimitives_v_size x0)`
  [`semanticPrimitives_v_to_char_list x1 =
      match x1 with
        (semanticPrimitives_Conv (SOME stamp)
          []:semanticPrimitives_v) ->
     (if stamp = TypeStamp (implode "[]") list_type_num then SOME ""
       else NONE)
      | (semanticPrimitives_Conv (SOME stamp)
        [semanticPrimitives_Litv (ast_Char c); v]) ->
     (if stamp = TypeStamp (implode "::") list_type_num then
        match semanticPrimitives_v_to_char_list v with NONE -> NONE
          | SOME cs -> SOME (CONS c cs) else NONE)
      | _45 -> NONE`];;

let _ = size_thms "semanticPrimitives_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let vs_to_string_def,vs_to_string_ind = define_wf
  `MEASURE (\x0. semanticPrimitives_v_size3 x0)`
  [`semanticPrimitives_vs_to_string x1 =
      match x1 with
        [] -> SOME (implode "")
      | CONS (semanticPrimitives_Litv (ast_StrLit
        s1):semanticPrimitives_v) vs ->
     (match semanticPrimitives_vs_to_string vs with NONE -> NONE |
       SOME s2 -> SOME (strcat s1 s2))
      | (CONS _46 v1) -> NONE`];;

let maybe_to_v_def = define_cases
  [`maybe_to_v NONE = semanticPrimitives_Conv (SOME (TypeStamp
  (implode "None") option_type_num)) []`;
   `maybe_to_v (SOME v) = semanticPrimitives_Conv (SOME (TypeStamp
  (implode "Some") option_type_num)) [v]`];;

let _ = size_thms "semanticPrimitives_v";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let v_to_id_def,v_to_id_ind = define_wf
  `MEASURE (\x0. semanticPrimitives_v_size x0)`
  [`v_to_id x1 =
      match x1 with
        (semanticPrimitives_Conv (SOME stamp)
          [semanticPrimitives_Litv (ast_StrLit
          s)]:semanticPrimitives_v) ->
      (if stamp = TypeStamp (implode "Short") id_type_num then
         SOME (Short s) else NONE)
      | (semanticPrimitives_Conv (SOME stamp)
        [semanticPrimitives_Litv (ast_StrLit s); v]) ->
      (if stamp = TypeStamp (implode "Long") id_type_num then
         match v_to_id v with NONE -> NONE | SOME id' -> SOME (Long
           s id') else NONE)
      | _47 -> NONE`];;

let nat_to_v_def = new_definition
  `nat_to_v n = semanticPrimitives_Litv (ast_IntLit (&n))`;;

let maybe_all_list_def,maybe_all_list_ind = define_shaped_rec
  "match"
  [`maybe_all_list v =
     (match v with
       [] -> SOME [] | CONS NONE vs -> NONE | CONS (SOME x) vs ->
         (match maybe_all_list vs with NONE -> NONE | SOME xs ->
           SOME (CONS x xs)))`];;

let v_to_word8_def = new_definition
  `v_to_word8 v =
     (match v with semanticPrimitives_Litv (ast_Word8 w) -> SOME w
       | _48 -> NONE)`;;

let v_to_word8_list_def = new_definition
  `v_to_word8_list v =
     (match semanticPrimitives_v_to_list v with NONE -> NONE |
       SOME xs -> maybe_all_list (MAP v_to_word8 xs))`;;

let v_to_word64_def = new_definition
  `v_to_word64 v =
     (match v with semanticPrimitives_Litv (ast_Word64 w) -> SOME
       w | _49 -> NONE)`;;

let v_to_word64_list_def = new_definition
  `v_to_word64_list v =
     (match semanticPrimitives_v_to_list v with NONE -> NONE |
       SOME xs -> maybe_all_list (MAP v_to_word64 xs))`;;

let lookup_env_def = new_definition
  `lookup_env s (i,j) =
     (match oEL i (eval_oracle_state_envs s) with NONE -> NONE |
       SOME gen_envs -> oEL j gen_envs)`;;

let add_decs_generation_def = new_definition
  `add_decs_generation s =
     (match eval_decs_state_env_id_counter s with
       (cur_gen,next_id,next_gen) ->
         eval_decs_state_env_id_counter_fupd (K (next_gen,0,next_gen +
         1))
         s)`;;

let add_env_generation_def = new_definition
  `add_env_generation s = eval_oracle_state_envs_fupd (K (APPEND
  (eval_oracle_state_envs s) [[]])) (eval_oracle_state_generation_fupd
  (K (LENGTH (eval_oracle_state_envs s)))
     s)`;;

let declare_env_def = new_definition
  `declare_env es env =
     (match es with NONE -> NONE | SOME (EvalDecs s) ->
       (match eval_decs_state_env_id_counter s with
          (cur_gen,next_id,next_gen) ->
            SOME
              (semanticPrimitives_Env env (cur_gen,next_id),
               SOME
                 (EvalDecs
                    (eval_decs_state_env_id_counter_fupd (K
                      (cur_gen,next_id + 1,next_gen)) s)))) | SOME
                      (EvalOracle s') ->
       (match oEL (eval_oracle_state_generation s')
         (eval_oracle_state_envs s') with NONE -> NONE | SOME gen_envs
         ->
         SOME
           (semanticPrimitives_Conv NONE [nat_to_v
             (eval_oracle_state_generation s'); nat_to_v (LENGTH
             gen_envs)],
            SOME
              (EvalOracle
                 (eval_oracle_state_envs_fupd (K (LUPDATE (APPEND
                   gen_envs [env]) (eval_oracle_state_generation s')
                   (eval_oracle_state_envs s'))) s')))))`;;

(* Concrete, or first-order values, which do not contain code closures and
   are unchanged by many compiler phases. *)
let concrete_v_def,concrete_v_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`concrete_v v <=>
         (match v with semanticPrimitives_Loc _50 _51 -> T |
           semanticPrimitives_Litv _52 -> T | semanticPrimitives_Conv
           v_ vs -> concrete_v_list vs | semanticPrimitives_Vectorv
           vs -> concrete_v_list vs | _53 -> F)`;
   `concrete_v_list [] <=> T`;
   `concrete_v_list (CONS v vs) <=> concrete_v v /\ concrete_v_list
  vs`];;

let compiler_agrees_def = new_definition
  `compiler_agrees (f:(num#num)#semanticPrimitives_v#dec
  list->(semanticPrimitives_v#word8 list#word64 list) option)
       args (st_v,bs_v,ws_v) <=>
     (match (f args,args,v_to_word8_list bs_v,v_to_word64_list ws_v)
       with (SOME (st,c_bs,c_ws),(v16,prev_st_v,_54),SOME bs,SOME ws) ->
         st = st_v /\ c_bs = bs /\ c_ws = ws /\ concrete_v st_v /\
         concrete_v prev_st_v | _55 -> F)`;;

(* get the declarations to be evaluated in the various Eval semantics *)
let do_eval_def = new_definition
  `semanticPrimitives_do_eval vs es =
     (match (es,vs) with (SOME (EvalDecs s),[semanticPrimitives_Env
       env id'; st_v; decs_v; st_v2; bs_v; ws_v]) ->
       (match eval_decs_state_decode_decs s decs_v with
          NONE -> NONE | SOME decs ->
          (if
            st_v = eval_decs_state_compiler_state s /\ concrete_v
              decs_v /\
            compiler_agrees (eval_decs_state_compiler s)
              (id',st_v,decs) (st_v2,bs_v,ws_v) then
            SOME
              (env,decs,
               SOME
                 (EvalDecs
                    (add_decs_generation
                      (eval_decs_state_compiler_state_fupd (K st_v2)
                      s)))) else NONE)) | (SOME (EvalOracle s'),vs) ->
       (match eval_oracle_state_custom_do_eval s' vs
         (eval_oracle_state_oracle s') with
          NONE -> NONE | SOME (env_id,oracle',decs) ->
            (match lookup_env s' env_id with
              NONE -> NONE | SOME env ->
                SOME
                (env,decs,
                 SOME
                 (EvalOracle (add_env_generation
                   (eval_oracle_state_oracle_fupd (K oracle')
                   s')))))) | _56 -> NONE)`;;

(* conclude an Eval generation *)

let reset_env_generation_def = new_definition
  `reset_env_generation prior_es es =
     (match (prior_es,es) with (SOME (EvalDecs prior_s'),SOME
       (EvalDecs s')) ->
       (match (eval_decs_state_env_id_counter
         prior_s',eval_decs_state_env_id_counter s') with
          ((cur_gen,next_id,v5),v6,v8,next_gen) ->
            SOME
              (EvalDecs
                 (eval_decs_state_env_id_counter_fupd (K
                   (cur_gen,next_id,next_gen)) s'))) | (SOME (EvalOracle
                   prior_s),SOME (EvalOracle s)) ->
       SOME (EvalOracle (eval_oracle_state_generation_fupd (K
         (eval_oracle_state_generation prior_s)) s)) | _57 -> es)`;;

let copy_array_def = new_definition
  `copy_array (src,srcoff) len d =
     (if
       srcoff < (&0) \/ len < (&0) \/ LENGTH src < num_of_int (abs (I
         (srcoff + len))) then
       NONE else
       (let
          copied =
            TAKE (num_of_int (abs (I len))) (DROP (num_of_int (abs (I
              srcoff))) src) in
          match d with
            NONE -> SOME copied | SOME (dst,dstoff) ->
            (if dstoff < (&0) \/ LENGTH dst < num_of_int (abs (I
              (dstoff + len))) then
              NONE else
              SOME
                (APPEND (APPEND (TAKE (num_of_int (abs (I dstoff)))
                  dst) copied)
                 (DROP (num_of_int (abs (I (dstoff + len))))
                   dst)))))`;;

let ws_to_chars_def = new_definition
  `ws_to_chars (ws:word8 list) = MAP (\w. CHR (w2n w)) ws`;;

let chars_to_ws_def = new_definition
  `chars_to_ws cs = (MAP (\c. i2w (&(ORD c))) cs:word8 list)`;;

(* HOL4 semanticPrimitivesScript.sml:700-737: code that the source
   has in a comment *)

let shift8_lookup_def = new_definition
  `shift8_lookup sh =
     (match sh with Lsl -> word_lsl | Lsr -> word_lsr | Asr ->
       word_asr | Ror -> (word_ror:word8->num->word8))`;;

let shift64_lookup_def = new_definition
  `shift64_lookup sh =
     (match sh with Lsl -> word_lsl | Lsr -> word_lsr | Asr ->
       word_asr | Ror -> (word_ror:word64->num->word64))`;;

let exp_or_val_INDUCT,exp_or_val_RECURSION = define_datatype
  "exp_or_val = Exp (ast_exp) | Val (semanticPrimitives_v)";;

(* HOL4 semanticPrimitivesScript.sml:761: the type abbreviation
   store_ffi, which the port expands *)

(* HOL4 semanticPrimitivesScript.sml:763: the overload w64lit, which
   the port expands *)
(* HOL4 semanticPrimitivesScript.sml:764: the overload f64lit, which
   the port expands *)

let xor_bytes_def,xor_bytes_ind = define_guess
  [`xor_bytes bs1 bs2 =
      match (bs1,bs2) with
        ([],bs2) -> SOME (bs2:word8 list)
      | (bs1,[]) -> NONE
      | ((CONS b1 bs1),(CONS b2 bs2)) ->
     (match xor_bytes bs1 bs2 with NONE -> NONE | SOME rest ->
       SOME (CONS (word_xor b1 b2) rest))`];;

(* With `dest_thunk` we check 3 things:
     - The values contain exactly one reference
     - The reference is valid
     - The reference points to a thunk
   We distinguish between `BadRef` and `NotThunk` instead of returning an option
   with `NONE` for both, because we want `update_thunk` to succeed when
   `dest_thunk` fails but only when the reference actually exists and points to
   something other than a thunk. *)
let semanticPrimitives_dest_thunk_ret_INDUCT,
    semanticPrimitives_dest_thunk_ret_RECURSION =
  define_datatype
  "semanticPrimitives_dest_thunk_ret = semanticPrimitives_BadRef | \
   semanticPrimitives_NotThunk | semanticPrimitives_IsThunk \
   (thunk_mode) (semanticPrimitives_v)";;

let dest_thunk_def = new_definition
  `semanticPrimitives_dest_thunk vs st =
      match vs with
        [(semanticPrimitives_Loc b n:semanticPrimitives_v)] ->
     (match store_lookup n st with NONE -> semanticPrimitives_BadRef
       | SOME (semanticPrimitives_Thunk Evaluated v) ->
          (if b then semanticPrimitives_BadRef else
            semanticPrimitives_IsThunk Evaluated v) | SOME
            (semanticPrimitives_Thunk NotEvaluated v) ->
          (if b then semanticPrimitives_BadRef else
            semanticPrimitives_IsThunk NotEvaluated v) | SOME _58 ->
            semanticPrimitives_NotThunk)
      | vs -> semanticPrimitives_NotThunk`;;

let update_thunk_def = new_definition
  `semanticPrimitives_update_thunk x1 st x3 =
      match (x1,x3) with
        ([(semanticPrimitives_Loc F n:semanticPrimitives_v)],[v]) ->
     (match semanticPrimitives_dest_thunk [v] st with
       semanticPrimitives_NotThunk -> store_assign n
       (semanticPrimitives_Thunk Evaluated v) st | _59 -> NONE)
      | (_60,_61) -> NONE`;;

let bad_thunk_update_def = new_definition
  `semanticPrimitives_bad_thunk_update m v st <=>
     m = Evaluated /\ ~(semanticPrimitives_dest_thunk [v] st =
       semanticPrimitives_NotThunk)`;;

let thunk_op_def = new_definition
  `semanticPrimitives_thunk_op ((s:(semanticPrimitives_v store_v)
  list),(t:'ffi ffi_state)) th_op vs =
     (match (th_op,vs) with (AllocThunk m,[v]) ->
         (if semanticPrimitives_bad_thunk_update m v s then NONE else
          let (s',n) = store_alloc (semanticPrimitives_Thunk m v) s
            in
            SOME ((s',t),Rval (semanticPrimitives_Loc F n))) |
              (UpdateThunk m,[semanticPrimitives_Loc F lnum; v]) ->
         (if semanticPrimitives_bad_thunk_update m v s then NONE else
          match store_assign lnum (semanticPrimitives_Thunk m v) s
            with SOME s' -> SOME ((s',t),Rval
            (semanticPrimitives_Conv NONE [])) | NONE -> NONE) | _62
            -> NONE)`;;

let check_type_def = new_definition
  `semanticPrimitives_check_type x1 v =
      match x1 with
        ast_BoolT -> (v = semanticPrimitives_Boolv T \/ v =
          semanticPrimitives_Boolv F)
      | ast_IntT -> (?i. v = semanticPrimitives_Litv (ast_IntLit i))
      | ast_CharT -> (?c. v = semanticPrimitives_Litv (ast_Char c))
      | ast_StrT -> (?s. v = semanticPrimitives_Litv (ast_StrLit s))
      | (ast_WordT ast_W8) -> (?w. v = semanticPrimitives_Litv
        (ast_Word8 w))
      | (ast_WordT ast_W64) -> (?w. v = semanticPrimitives_Litv
        (ast_Word64 w))
      | ast_Float64T -> (?w. v = semanticPrimitives_Litv
        (ast_Float64 w))`;;

let dest_Litv_def = new_definition
  `semanticPrimitives_dest_Litv x1 =
      match x1 with
        (semanticPrimitives_Litv v:semanticPrimitives_v) -> SOME v
      | _63 -> NONE`;;

let the_Litv_IntLit_def = define_general
  [`the_Litv_IntLit (semanticPrimitives_Litv (ast_IntLit
  i):semanticPrimitives_v) = i`];;

let the_Litv_Word8_def = define_general
  [`the_Litv_Word8 (semanticPrimitives_Litv (ast_Word8
  w):semanticPrimitives_v) = w`];;

let the_Litv_Word64_def = define_general
  [`the_Litv_Word64 (semanticPrimitives_Litv (ast_Word64
  w):semanticPrimitives_v) = w`];;

let the_Litv_Float64_def = define_general
  [`semanticPrimitives_the_Litv_Float64 (semanticPrimitives_Litv
  (ast_Float64 w):semanticPrimitives_v) = w`];;

let the_Litv_Char_def = define_general
  [`the_Litv_Char (semanticPrimitives_Litv (ast_Char
  c):semanticPrimitives_v) = c`];;

let the_Boolv_def = new_definition
  `the_Boolv v = (v = semanticPrimitives_Boolv T)`;;

let num_cmp_def = define_cases
  [`semanticPrimitives_num_cmp (ast_Lt:opb) i (j:num) = (i < (j:num))`;
   `semanticPrimitives_num_cmp ast_Leq i (j:num) = (i <= j)`;
   `semanticPrimitives_num_cmp ast_Gt i (j:num) = (i > j)`;
   `semanticPrimitives_num_cmp ast_Geq i (j:num) = (i >= j)`];;

let int_cmp_def = define_cases
  [`semanticPrimitives_int_cmp (ast_Lt:opb) i (j:int) = (i < (j:int))`;
   `semanticPrimitives_int_cmp ast_Leq i (j:int) = (i <= j)`;
   `semanticPrimitives_int_cmp ast_Gt i (j:int) = (i > j)`;
   `semanticPrimitives_int_cmp ast_Geq i (j:int) = (i >= j)`];;

let str_cmp_def = new_definition
  `str_cmp x1 x2 i j =
      match (x1,x2) with
        (F,(ast_Lt:opb)) -> mlstring_lt i j
      | (F,ast_Leq) -> mlstring_le i j
      | (F,ast_Gt) -> mlstring_gt i j
      | (F,ast_Geq) -> mlstring_ge i j
      | (T,ast_Lt) -> fast_lt i j
      | (T,ast_Leq) -> fast_le i j
      | (T,ast_Gt) -> fast_gt i j
      | (T,ast_Geq) -> fast_ge i j`;;

let do_test_def = define_cases
  [`// TODO: extend with more cases
    semanticPrimitives_do_test (ast_Equal:test) ty v1 v2 =
      (if semanticPrimitives_check_type ty v1 /\
        semanticPrimitives_check_type ty v2 then
         (if ty = ast_Float64T then Eq_val (fp64_equal
           (semanticPrimitives_the_Litv_Float64 v1)
           (semanticPrimitives_the_Litv_Float64 v2)) else
           semanticPrimitives_do_eq v1 v2) else Eq_type_error)`;
   `semanticPrimitives_do_test (ast_Compare cmp) ty v1 v2 =
      (match (ty,semanticPrimitives_dest_Litv
        v1,semanticPrimitives_dest_Litv v2) with (ast_IntT,SOME
        (ast_IntLit i),SOME (ast_IntLit j)) -> Eq_val
        (semanticPrimitives_int_cmp cmp i j) | (ast_CharT,SOME
        (ast_Char c),SOME (ast_Char d)) -> Eq_val
        (semanticPrimitives_num_cmp cmp (ORD c) (ORD d)) | (ast_WordT
        ast_W8,SOME (ast_Word8 w),SOME (ast_Word8 v)) -> Eq_val
        (semanticPrimitives_num_cmp cmp (w2n w) (w2n v)) |
        (ast_Float64T,SOME (ast_Float64 w),SOME (ast_Float64 v)) ->
        Eq_val (fp_cmp cmp w v) | (ast_StrT,SOME (ast_StrLit s),SOME
        (ast_StrLit t)) -> Eq_val (str_cmp F cmp s t) | _66 ->
        Eq_type_error)`;
   `semanticPrimitives_do_test (ast_AltCompare cmp) ty v1 v2 =
      (match (ty,semanticPrimitives_dest_Litv
        v1,semanticPrimitives_dest_Litv v2) with (ast_StrT,SOME
        (ast_StrLit s),SOME (ast_StrLit t)) -> Eq_val (str_cmp T
        cmp s t) | _67 -> Eq_type_error)`];;

let do_arith_def = new_definition
  `do_arith a x2 vals =
        match x2 with
          ast_Float64T ->
        (match (a,MAP semanticPrimitives_the_Litv_Float64 vals) with
          (ast_Abs,[v1]) -> SOME (INR (semanticPrimitives_Litv
          (ast_Float64 (fp64_abs v1)))) | (ast_Neg,[v1]) -> SOME (INR
          (semanticPrimitives_Litv (ast_Float64 (fp64_negate v1)))) |
          (ast_Sqrt,[v1]) -> SOME (INR (semanticPrimitives_Litv
          (ast_Float64 (fp64_sqrt roundTiesToEven v1)))) | (ast_Add,[v1;
          v2]) -> SOME (INR (semanticPrimitives_Litv (ast_Float64
          (fp64_add roundTiesToEven v1 v2)))) | (ast_Sub,[v1; v2]) ->
          SOME (INR (semanticPrimitives_Litv (ast_Float64 (fp64_sub
          roundTiesToEven v1 v2)))) | (ast_Mul,[v1; v2]) -> SOME (INR
          (semanticPrimitives_Litv (ast_Float64 (fp64_mul
          roundTiesToEven v1 v2)))) | (ast_Div,[v1; v2]) -> SOME (INR
          (semanticPrimitives_Litv (ast_Float64 (fp64_div
          roundTiesToEven v1 v2)))) | (ast_FMA,[v1; v2; v3]) -> SOME
          (INR (semanticPrimitives_Litv (ast_Float64 (fp64_mul_add
          roundTiesToEven v2 v3 v1)))) | _68 -> NONE)
        | ast_IntT ->
        (match (a,MAP the_Litv_IntLit vals) with (ast_Add,[v1; v2])
          -> SOME (INR (semanticPrimitives_Litv (ast_IntLit (v1 + v2))))
          | (ast_Sub,[v1; v2]) -> SOME (INR (semanticPrimitives_Litv
          (ast_IntLit (v1 - v2)))) | (ast_Mul,[v1; v2]) -> SOME (INR
          (semanticPrimitives_Litv (ast_IntLit (v1 * v2)))) |
          (ast_Div,[v1; v2]) -> SOME (if v2 = (&0) then INL
          semanticPrimitives_div_exn_v else
                              INR (semanticPrimitives_Litv
                                (ast_IntLit (v1 / v2)))) | (ast_Mod,[v1;
                                v2]) -> SOME (if v2 = (&0) then INL
                                semanticPrimitives_div_exn_v else
                              INR (semanticPrimitives_Litv
                                (ast_IntLit (v1 % v2)))) | _69 -> NONE)
        | (ast_WordT ast_W8) ->
        (match (a,MAP the_Litv_Word8 vals) with (ast_Add,[v1; v2]) ->
          SOME (INR (semanticPrimitives_Litv (ast_Word8 (word_add v1
          v2)))) | (ast_Sub,[v1; v2]) -> SOME (INR
          (semanticPrimitives_Litv (ast_Word8 (word_sub v1 v2)))) |
          (ast_And,[v1; v2]) -> SOME (INR (semanticPrimitives_Litv
          (ast_Word8 (word_and v1 v2)))) | (ast_Or,[v1; v2]) -> SOME
          (INR (semanticPrimitives_Litv (ast_Word8 (word_or v1 v2)))) |
          (ast_Xor,[v1; v2]) -> SOME (INR (semanticPrimitives_Litv
          (ast_Word8 (word_xor v1 v2)))) | _70 -> NONE)
        | (ast_WordT ast_W64) ->
        (match (a,MAP the_Litv_Word64 vals) with (ast_Add,[v1; v2])
          -> SOME (INR (semanticPrimitives_Litv (ast_Word64 (word_add v1
          v2)))) | (ast_Sub,[v1; v2]) -> SOME (INR
          (semanticPrimitives_Litv (ast_Word64 (word_sub v1 v2)))) |
          (ast_And,[v1; v2]) -> SOME (INR (semanticPrimitives_Litv
          (ast_Word64 (word_and v1 v2)))) | (ast_Or,[v1; v2]) -> SOME
          (INR (semanticPrimitives_Litv (ast_Word64 (word_or v1 v2)))) |
          (ast_Xor,[v1; v2]) -> SOME (INR (semanticPrimitives_Litv
          (ast_Word64 (word_xor v1 v2)))) | _71 -> NONE)
        | ast_BoolT ->
        (match (a,vals) with (ast_Not,[v1]) -> SOME (INR
          (semanticPrimitives_Boolv (~(the_Boolv v1)))) | _72 -> NONE)
        | _73 -> NONE`;;

let do_conversion_def = new_definition
  `do_conversion v x2 x3 =
        match (x2,x3) with
          // Word to Int conversions
        ((ast_WordT ast_W8:prim_type),(ast_IntT:prim_type)) ->
        SOME (INR (semanticPrimitives_Litv (ast_IntLit (&(w2n
          (the_Litv_Word8 v))))))
        | ((ast_WordT ast_W64),ast_IntT) ->
        SOME (INR (semanticPrimitives_Litv (ast_IntLit (&(w2n
          (the_Litv_Word64 v))))))
        // Int to Word conversions
        | (ast_IntT,(ast_WordT ast_W8)) ->
        SOME (INR (semanticPrimitives_Litv (ast_Word8 (i2w
          (the_Litv_IntLit v)))))
        | (ast_IntT,(ast_WordT ast_W64)) ->
        SOME (INR (semanticPrimitives_Litv (ast_Word64 (i2w
          (the_Litv_IntLit v)))))
        // Char/Int conversions
        | (ast_CharT,ast_IntT) ->
        SOME (INR (semanticPrimitives_Litv (ast_IntLit (&(ORD
          (the_Litv_Char v))))))
        | (ast_IntT,ast_CharT) ->
        (let i = the_Litv_IntLit v in
          if i < (&0) \/ i > (&255) then SOME (INL
            semanticPrimitives_chr_exn_v) else SOME (INR
            (semanticPrimitives_Litv (ast_Char (CHR (num_of_int (abs
            i)))))))
        // Char/Word8 conversions
        | (ast_CharT,(ast_WordT ast_W8)) ->
        SOME (INR (semanticPrimitives_Litv (ast_Word8 (char_to_word8
          (the_Litv_Char v)))))
        | ((ast_WordT ast_W8),ast_CharT) ->
        SOME (INR (semanticPrimitives_Litv (ast_Char (word8_to_char
          (the_Litv_Word8 v)))))
        // Float64/Word64 conversions (bit reinterpretation)
        | (ast_Float64T,(ast_WordT ast_W64)) ->
        SOME (INR (semanticPrimitives_Litv (ast_Word64
          (semanticPrimitives_the_Litv_Float64 v))))
        | ((ast_WordT ast_W64),ast_Float64T) ->
        SOME (INR (semanticPrimitives_Litv (ast_Float64
          (the_Litv_Word64 v))))
        | (_74,_75) -> NONE`;;

let do_app_def = new_definition
  `semanticPrimitives_do_app ((s:(semanticPrimitives_v store_v)
  list),(t:'ffi ffi_state)) op vs =
     (match (op,vs) with
       (ast_ListAppend,[x1; x2]) ->
       (match (semanticPrimitives_v_to_list
         x1,semanticPrimitives_v_to_list x2) with
           (SOME xs,SOME ys) -> SOME ((s,t),Rval
             (semanticPrimitives_list_to_v (APPEND xs ys))) | _76 ->
             NONE) | (ast_Shift ast_W8 op n,[semanticPrimitives_Litv
             (ast_Word8 w)]) ->
         SOME ((s,t),Rval (semanticPrimitives_Litv (ast_Word8
           (shift8_lookup op w n)))) | (ast_Shift ast_W64 op
           n,[semanticPrimitives_Litv (ast_Word64 w)]) ->
         SOME ((s,t),Rval (semanticPrimitives_Litv (ast_Word64
           (shift64_lookup op w n)))) | (ast_Equality,[v1; v2]) ->
         (match semanticPrimitives_do_eq v1 v2 with
             Eq_type_error -> NONE | Eq_val b -> SOME ((s,t),Rval
               (semanticPrimitives_Boolv b))) |
               (ast_Opassign,[semanticPrimitives_Loc b lnum; v]) ->
         (match store_assign lnum (semanticPrimitives_Refv v) s with
             SOME s' -> SOME ((s',t),Rval (semanticPrimitives_Conv
               NONE [])) | NONE -> NONE) | (ast_Opref,[v]) ->
         (let (s',n) = (store_alloc (semanticPrimitives_Refv v) s) in
           SOME ((s',t),Rval (semanticPrimitives_Loc T n))) |
             (ast_Opderef,[semanticPrimitives_Loc b n]) ->
         (match store_lookup n s with
             SOME (semanticPrimitives_Refv v) -> SOME ((s,t),Rval v)
               | _77 -> NONE) | (ast_Aw8alloc,[semanticPrimitives_Litv
               (ast_IntLit n); semanticPrimitives_Litv (ast_Word8 w)])
               ->
         (if n < ((&0):int) then
           SOME ((s,t),Rerr (Rraise sub_exn_v)) else
           let (s',lnum) =
             (store_alloc (semanticPrimitives_W8array (REPLICATE
               (num_of_int (abs (I n))) w)) s) in
             SOME ((s',t),Rval (semanticPrimitives_Loc T lnum))) |
               (ast_Aw8sub,[semanticPrimitives_Loc _78 lnum;
               semanticPrimitives_Litv (ast_IntLit i)]) ->
         (match store_lookup lnum s with
             SOME (semanticPrimitives_W8array ws) ->
               (if i < ((&0):int) then
                 SOME ((s,t),Rerr (Rraise sub_exn_v)) else
                 let n = (num_of_int (abs (I i))) in
                   if n >= LENGTH ws then
                     SOME ((s,t),Rerr (Rraise sub_exn_v)) else
                     SOME ((s,t),Rval (semanticPrimitives_Litv
                       (ast_Word8 (EL n ws))))) | _79 -> NONE) |
                       (ast_Aw8sub_unsafe,[semanticPrimitives_Loc _80
                       lnum; semanticPrimitives_Litv (ast_IntLit i)]) ->
         (match store_lookup lnum s with
             SOME (semanticPrimitives_W8array ws) ->
               (if i < ((&0):int) then
                 NONE else
                 let n = (num_of_int (abs (I i))) in
                   if n >= LENGTH ws then
                     NONE else
                     SOME ((s,t),Rval (semanticPrimitives_Litv
                       (ast_Word8 (EL n ws))))) | _81 -> NONE) |
                       (ast_Aw8length,[semanticPrimitives_Loc _82 n]) ->
         (match store_lookup n s with
             SOME (semanticPrimitives_W8array ws) ->
               SOME ((s,t),Rval (semanticPrimitives_Litv (ast_IntLit
                 (int_of_num (LENGTH ws))))) | _83 -> NONE) |
                 (ast_Aw8update,[semanticPrimitives_Loc _84 lnum;
                 semanticPrimitives_Litv (ast_IntLit i);
                 semanticPrimitives_Litv (ast_Word8 w)]) ->
         (match store_lookup lnum s with
           SOME (semanticPrimitives_W8array ws) ->
             (if i < ((&0):int) then
               SOME ((s,t),Rerr (Rraise sub_exn_v)) else
               let n = (num_of_int (abs (I i))) in
                 if n >= LENGTH ws then
                   SOME ((s,t),Rerr (Rraise sub_exn_v)) else
                   (match store_assign lnum
                     (semanticPrimitives_W8array (LUPDATE w n ws)) s
                     with
                       NONE -> NONE | SOME s' -> SOME ((s',t),Rval
                         (semanticPrimitives_Conv NONE [])))) | _85 ->
                         NONE) |
                         (ast_Aw8update_unsafe,[semanticPrimitives_Loc
                         _86 lnum; semanticPrimitives_Litv (ast_IntLit
                         i); semanticPrimitives_Litv (ast_Word8 w)]) ->
         (match store_lookup lnum s with
           SOME (semanticPrimitives_W8array ws) ->
             (if i < ((&0):int) then
               NONE else
               let n = (num_of_int (abs (I i))) in
                 if n >= LENGTH ws then
                   NONE else
                   (match store_assign lnum
                     (semanticPrimitives_W8array (LUPDATE w n ws)) s
                     with
                       NONE -> NONE | SOME s' -> SOME ((s',t),Rval
                         (semanticPrimitives_Conv NONE [])))) | _87 ->
                         NONE) |
                         (ast_CopyStrStr,[semanticPrimitives_Litv
                         (ast_StrLit str); semanticPrimitives_Litv
                         (ast_IntLit off); semanticPrimitives_Litv
                         (ast_IntLit len)]) ->
         SOME ((s,t),
         (match copy_array (explode str,off) len NONE with
           NONE -> Rerr (Rraise sub_exn_v) | SOME cs -> Rval
             (semanticPrimitives_Litv (ast_StrLit (implode (cs)))))) |
             (ast_CopyStrAw8,[semanticPrimitives_Litv (ast_StrLit str);
             semanticPrimitives_Litv (ast_IntLit off);
             semanticPrimitives_Litv (ast_IntLit len);
                     semanticPrimitives_Loc _88 dst;
                       semanticPrimitives_Litv (ast_IntLit dstoff)]) ->
         (match store_lookup dst s with
           SOME (semanticPrimitives_W8array ws) ->
             (match copy_array (explode str,off) len (SOME
               (ws_to_chars ws,dstoff)) with
               NONE -> SOME ((s,t),Rerr (Rraise sub_exn_v)) | SOME cs
                 ->
               (match store_assign dst (semanticPrimitives_W8array
                 (chars_to_ws cs)) s with
                 SOME s' -> SOME ((s',t),Rval
                   (semanticPrimitives_Conv NONE [])) | _89 -> NONE)) |
                   _90 -> NONE) |
                   (ast_CopyAw8Str,[semanticPrimitives_Loc _91 src;
                   semanticPrimitives_Litv (ast_IntLit off);
                   semanticPrimitives_Litv (ast_IntLit len)]) ->
       (match store_lookup src s with
         SOME (semanticPrimitives_W8array ws) ->
         SOME ((s,t),
               (match copy_array (ws,off) len NONE with
                  NONE -> Rerr (Rraise sub_exn_v) | SOME ws -> Rval
                    (semanticPrimitives_Litv (ast_StrLit (implode
                    (ws_to_chars ws)))))) | _92 -> NONE) |
                    (ast_CopyAw8Aw8,[semanticPrimitives_Loc _93 src;
                    semanticPrimitives_Litv (ast_IntLit off);
                    semanticPrimitives_Litv (ast_IntLit len);
                     semanticPrimitives_Loc _94 dst;
                       semanticPrimitives_Litv (ast_IntLit dstoff)]) ->
       (match (store_lookup src s,store_lookup dst s) with
         (SOME (semanticPrimitives_W8array ws),SOME
           (semanticPrimitives_W8array ds)) ->
           (match copy_array (ws,off) len (SOME (ds,dstoff)) with
             NONE -> SOME ((s,t),Rerr (Rraise sub_exn_v)) | SOME ws
               ->
               (match store_assign dst (semanticPrimitives_W8array
                 ws) s with
                 SOME s' -> SOME ((s',t),Rval
                   (semanticPrimitives_Conv NONE [])) | _95 -> NONE)) |
                   _96 -> NONE) |
                   (ast_XorAw8Str_unsafe,[semanticPrimitives_Loc _97
                   dst; semanticPrimitives_Litv (ast_StrLit str_arg)])
                   ->
         (match store_lookup dst s with
           SOME (semanticPrimitives_W8array bs) ->
             (match xor_bytes (MAP (n2w o ORD) (explode str_arg)) bs
               with NONE -> NONE | SOME new_bs ->
                 (match store_assign dst (semanticPrimitives_W8array
                   new_bs) s with NONE -> NONE | SOME s' -> SOME
                   ((s',t),Rval (semanticPrimitives_Conv NONE [])))) |
                   _98 -> NONE) | (ast_Implode,[v]) ->
           (match semanticPrimitives_v_to_char_list v with
             SOME ls ->
               SOME ((s,t),Rval (semanticPrimitives_Litv (ast_StrLit
                 (implode ls)))) | NONE -> NONE) | (ast_Explode,[v]) ->
           (match v with
             semanticPrimitives_Litv (ast_StrLit str) ->
               SOME ((s,t),Rval (semanticPrimitives_list_to_v (MAP
                 (\c. semanticPrimitives_Litv (ast_Char c)) (explode
                 str)))) | _99 -> NONE) |
                 (ast_Strsub,[semanticPrimitives_Litv (ast_StrLit str);
                 semanticPrimitives_Litv (ast_IntLit i)]) ->
         (if i < ((&0):int) then
           SOME ((s,t),Rerr (Rraise sub_exn_v)) else
           let n = (num_of_int (abs (I i))) in
             if n >= strlen str then
               SOME ((s,t),Rerr (Rraise sub_exn_v)) else
               SOME ((s,t),Rval (semanticPrimitives_Litv (ast_Char
                 (EL n (explode str)))))) |
                 (ast_Strlen,[semanticPrimitives_Litv (ast_StrLit str)])
                 ->
         SOME ((s,t),Rval (semanticPrimitives_Litv (ast_IntLit
           (int_of_num (strlen str))))) | (ast_Strcat,[v]) ->
         (match semanticPrimitives_v_to_list v with
           SOME vs ->
             (match semanticPrimitives_vs_to_string vs with
               SOME str ->
                 SOME ((s,t),Rval (semanticPrimitives_Litv
                   (ast_StrLit str))) | _100 -> NONE) | _101 -> NONE) |
                   (ast_VfromList,[v]) ->
           (match semanticPrimitives_v_to_list v with
               SOME vs ->
                 SOME ((s,t),Rval (semanticPrimitives_Vectorv vs)) |
                   NONE -> NONE) |
                   (ast_Vsub_unsafe,[semanticPrimitives_Vectorv vs;
                   semanticPrimitives_Litv (ast_IntLit i)]) ->
         (if ((&0):int) <= i /\ num_of_int i < LENGTH vs then
           SOME ((s,t),Rval (EL (num_of_int i) vs)) else
           NONE) | (ast_Vsub,[semanticPrimitives_Vectorv vs;
             semanticPrimitives_Litv (ast_IntLit i)]) ->
         (if i < ((&0):int) then
           SOME ((s,t),Rerr (Rraise sub_exn_v)) else
           let n = (num_of_int (abs (I i))) in
             if n >= LENGTH vs then
               SOME ((s,t),Rerr (Rraise sub_exn_v)) else
               SOME ((s,t),Rval (EL n vs))) |
                 (ast_Vlength,[semanticPrimitives_Vectorv vs]) ->
         SOME ((s,t),Rval (semanticPrimitives_Litv (ast_IntLit
           (int_of_num (LENGTH vs))))) |
           (ast_Aalloc,[semanticPrimitives_Litv (ast_IntLit n); v]) ->
         (if n < ((&0):int) then
           SOME ((s,t),Rerr (Rraise sub_exn_v)) else
           let (s',lnum) =
             (store_alloc (semanticPrimitives_Varray (REPLICATE
               (num_of_int (abs (I n))) v)) s) in
             SOME ((s',t),Rval (semanticPrimitives_Loc T lnum))) |
               (ast_AallocEmpty,[semanticPrimitives_Conv NONE []]) ->
         (let (s',lnum) = (store_alloc (semanticPrimitives_Varray [])
           s) in
           SOME ((s',t),Rval (semanticPrimitives_Loc T lnum))) |
             (ast_AallocFixed,vs) ->
         (let (s',lnum) =
           (store_alloc (semanticPrimitives_Varray vs) s) in
           SOME ((s',t),Rval (semanticPrimitives_Loc T lnum))) |
             (ast_Asub,[semanticPrimitives_Loc _102 lnum;
             semanticPrimitives_Litv (ast_IntLit i)]) ->
         (match store_lookup lnum s with
             SOME (semanticPrimitives_Varray vs) ->
               (if i < ((&0):int) then
                 SOME ((s,t),Rerr (Rraise sub_exn_v)) else
                 let n = (num_of_int (abs (I i))) in
                   if n >= LENGTH vs then
                     SOME ((s,t),Rerr (Rraise sub_exn_v)) else
                     SOME ((s,t),Rval (EL n vs))) | _103 -> NONE) |
                       (ast_Asub_unsafe,[semanticPrimitives_Loc _104
                       lnum; semanticPrimitives_Litv (ast_IntLit i)]) ->
         (match store_lookup lnum s with
             SOME (semanticPrimitives_Varray vs) ->
               (if i < ((&0):int) then
                 NONE else
                 let n = (num_of_int (abs (I i))) in
                   if n >= LENGTH vs then
                     NONE else
                     SOME ((s,t),Rval (EL n vs))) | _105 -> NONE) |
                       (ast_Alength,[semanticPrimitives_Loc _106 n]) ->
         (match store_lookup n s with
             SOME (semanticPrimitives_Varray ws) ->
               SOME ((s,t),Rval (semanticPrimitives_Litv (ast_IntLit
                 (int_of_num (LENGTH ws))))) | _107 -> NONE) |
                 (ast_Aupdate,[semanticPrimitives_Loc _108 lnum;
                 semanticPrimitives_Litv (ast_IntLit i); v]) ->
         (match store_lookup lnum s with
           SOME (semanticPrimitives_Varray vs) ->
             (if i < ((&0):int) then
               SOME ((s,t),Rerr (Rraise sub_exn_v)) else
               let n = (num_of_int (abs (I i))) in
                 if n >= LENGTH vs then
                   SOME ((s,t),Rerr (Rraise sub_exn_v)) else
                   (match store_assign lnum
                     (semanticPrimitives_Varray (LUPDATE v n vs)) s with
                       NONE -> NONE | SOME s' -> SOME ((s',t),Rval
                         (semanticPrimitives_Conv NONE [])))) | _109 ->
                         NONE) |
                         (ast_Aupdate_unsafe,[semanticPrimitives_Loc
                         _110 lnum; semanticPrimitives_Litv (ast_IntLit
                         i); v]) ->
         (match store_lookup lnum s with
           SOME (semanticPrimitives_Varray vs) ->
             (if i < ((&0):int) then
               NONE else
               let n = (num_of_int (abs (I i))) in
                 if n >= LENGTH vs then
                   NONE else
                   (match store_assign lnum
                     (semanticPrimitives_Varray (LUPDATE v n vs)) s with
                       NONE -> NONE | SOME s' -> SOME ((s',t),Rval
                         (semanticPrimitives_Conv NONE [])))) | _111 ->
                         NONE) | (ast_ConfigGC,[semanticPrimitives_Litv
                         (ast_IntLit i); semanticPrimitives_Litv
                         (ast_IntLit j)]) ->
         SOME ((s,t),Rval (semanticPrimitives_Conv NONE [])) |
           (ast_FFI n,[semanticPrimitives_Litv (ast_StrLit conf);
           semanticPrimitives_Loc _112 lnum]) ->
         (match store_lookup lnum s with
           SOME (semanticPrimitives_W8array ws) ->
             (match call_FFI t (ffi_ExtCall n) (MAP (n2w o ORD)
               (explode conf)) ws with
               FFI_return t' ws' ->
                (match store_assign lnum (semanticPrimitives_W8array
                  ws') s with
                  SOME s' -> SOME ((s',t'),Rval
                    (semanticPrimitives_Conv NONE [])) | NONE -> NONE) |
                    FFI_final outcome ->
                SOME ((s,t),Rerr (Rabort (Rffi_error outcome)))) |
                  _113 -> NONE) | (ast_Env_id,[semanticPrimitives_Env
                  env (gen,id')]) -> SOME ((s,t),
             Rval (semanticPrimitives_Conv NONE [nat_to_v gen;
               nat_to_v id'])) | (ast_Env_id,[semanticPrimitives_Conv
               NONE [gen; id']]) -> SOME ((s,t),
             Rval (semanticPrimitives_Conv NONE [gen; id'])) |
               (ast_ThunkOp th_op,vs) -> semanticPrimitives_thunk_op
               (s,t) th_op vs | (ast_Arith a ty,vs) ->
         (if ALL (semanticPrimitives_check_type ty) vs then
            (match do_arith a ty vs with SOME (INR res) -> SOME
              ((s,t),Rval res) | SOME (INL exn) -> SOME ((s,t),Rerr
              (Rraise exn)) | NONE -> NONE) else NONE) | (ast_FromTo ty1
              ty2,[v]) ->
         (if semanticPrimitives_check_type ty1 v then
            (match do_conversion v ty1 ty2 with SOME (INR res) ->
              SOME ((s,t),Rval res) | SOME (INL exn) -> SOME ((s,t),Rerr
              (Rraise exn)) | NONE -> NONE) else NONE) | (ast_Test test
              test_ty,[v1; v2]) ->
         (match semanticPrimitives_do_test test test_ty v1 v2 with
             Eq_type_error -> NONE | Eq_val b -> SOME ((s,t),Rval
               (semanticPrimitives_Boolv b))) | _114 -> NONE)`;;

(* Do a logical operation *)
let do_log_def = new_definition
  `do_log l v e =
     (if l = Andalso /\ v = semanticPrimitives_Boolv T \/ l =
       Orelse /\ v = semanticPrimitives_Boolv F then SOME (Exp e)
       else if l = Andalso /\ v = semanticPrimitives_Boolv F \/ l =
       Orelse /\ v = semanticPrimitives_Boolv T then SOME (Val v)
       else NONE)`;;

(* Do an if-then-else *)
let do_if_def = new_definition
  `semanticPrimitives_do_if v e1 e2 =
     (if v = semanticPrimitives_Boolv T then SOME e1 else if v =
       semanticPrimitives_Boolv F then SOME e2 else NONE)`;;

(* Semantic helpers for definitions *)

let build_constrs_def = new_definition
  `build_constrs stamp condefs =
     MAP (\(conN,ts). (conN,LENGTH ts,TypeStamp conN stamp))
       condefs`;;

(* Build a constructor environment for the type definition tds *)
let build_tdefs_def,build_tdefs_ind = define_rec
  [`build_tdefs next_stamp ([]:(mlstring list#mlstring#(mlstring#ast_t
  list) list) list) =
      ((alist_to_ns []):(mlstring,mlstring,num#stamp)namespace)`;
   `build_tdefs next_stamp (CONS (tvs,tn,condefs) tds) =
      ((nsAppend (build_tdefs (next_stamp + 1) tds)
        (alist_to_ns (REVERSE (build_constrs next_stamp
          condefs)))):(mlstring,mlstring,num#stamp)namespace)`];;

(* Checks that no constructor is defined twice in a type *)
let check_dup_ctors_def = new_definition
  `check_dup_ctors ((tvs,tn,condefs):mlstring
  list#mlstring#(mlstring#ast_t list) list) <=>
     ALL_DISTINCT
       (let x2 = [] in
          ITLIST (\(n,ts) x2. if T then CONS n x2 else x2) condefs
            x2)`;;

let combine_dec_result_def = new_definition
  `combine_dec_result env (r:(semanticPrimitives_v
  sem_env,'a)semanticPrimitives_result) =
     (match r with Rval env' -> Rval (mk_sem_env (nsAppend
       (sem_env_v env') (sem_env_v env)) (nsAppend (sem_env_c env')
       (sem_env_c env))) | Rerr e -> Rerr e)`;;

let extend_dec_env_def = new_definition
  `extend_dec_env new_env (env:semanticPrimitives_v sem_env) =
     mk_sem_env (nsAppend (sem_env_v new_env) (sem_env_v env))
       (nsAppend (sem_env_c new_env) (sem_env_c env))`;;

(* HOL4 semanticPrimitivesScript.sml:1376: ML code, not ported *)
(* HOL4 semanticPrimitivesScript.sml:1377: the overload +++, which
   the port writes as an application of extend_dec_env *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
