(* ======================================================== *)
(*  clos_to_bvl: ported from HOL4's
    compiler/backend/clos_to_bvlScript.sml
    A definition theory, with 45 definitions, 1 datatype and 24
    theorems.  Needed by 10 files of the port.  *)
(* ======================================================== *)

(*
  This compiler phase performs closure conversion.  This phase puts
  all of the code into a table of first-order, closed, multi-argument
  functions.

  The table is indexed by natural numbers, and each entry
  is a pair of a number (the function's arity) and a BVL expression
  (the function's body). The table has the following layout.

  Entry i in the range 0 to max_app - 1 (inclusive):
    generic application of a closure to i+1 arguments. Takes i+2 arguments
    (the arguments and the closure). The closure might expect more or less
    than i+1 arguments, and this code would then allocate a partial application
    closure, or make repeated applications.

  Entries in the range max_app to max_app + (max_app * (max_app - 1) DIV 2) - 1 (inclusive) :
    code to fully apply a partially applied closure wrapper.
    For a closure expecting tot number of arguments, which has already been
    given prev number of arguments, the wrapper is in location
    max_app + tot * (tot - 1) DIV 2 + prev
    and takes tot - prev + 1 arguments

  The next entry initialises a global variable that contains a jump table used
  by the generic application stubs (0 argument).

  The num_stubs function gives the total number of these functions.

  Starting at index num_stubs, there are 0 argument functions that evaluate
  each expression that should be evaluated, and then call the next function.

  Following these functions, at even numbers there are the bodies of
  functions in the program, with one extra argument for the closure value to be
  passed in to them. The odd entries are the bodies of the functions that have
  no free variables, and so they don't have any extra arguments. Their
  correcponding odd entries just indirect to the even ones. (clos_call)
  One entry might be skipped in between the expressions and the source-level
  function bodies to get the alignment right.

*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_jump.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/clos_annotate.ml";;
needs "compiler/backend/clos_call.ml";;
needs "compiler/backend/clos_known.ml";;
needs "compiler/backend/clos_mti.ml";;
needs "compiler/backend/clos_number.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "clos_to_bvl"
  ["backend_common"; "bvl"; "bvl_jump"; "closLang"; "clos_annotate";
   "clos_call"; "clos_known"; "clos_mti"; "clos_number"];;

let _ = do_list hide_constant ["pmatch"];;

(* HOL4 clos_to_bvlScript.sml:50-51: a theorem that HOL4 states as
   the value of an ML expression: partial_app_tag_neq_closure_tag *)

(* HOL4 clos_to_bvlScript.sml:53-54: a theorem that HOL4 states as
   the value of an ML expression: clos_tag_shift_nil_tag *)

(* HOL4 clos_to_bvlScript.sml:56-57: a theorem that HOL4 states as
   the value of an ML expression: clos_tag_shift_cons_tag *)

let clos_tag_shift_inj = prove
 (`clos_tag_shift n1 = clos_tag_shift n2 ==> n1 = n2`,
  CHEAT_TAC);;

(* Constant flattening *)

(* HOL4 clos_to_bvlScript.sml:67: the overload PRIME, which the port
   expands *)

let part_hash_def = define_cases
  [`part_hash (Int i:const_part) = num_of_int (abs i) MOD
  (999983:num)`;
   `part_hash (closLang_Str s:const_part) =
      (strlen s + 3 * SUM (MAP ORD (explode s))) MOD (999983:num)`;
   `part_hash (W64 w:const_part) = (17 + w2n w) MOD (999983:num)`;
   `part_hash (Con t ns:const_part) = (18 + 5 * t + 7 * SUM ns) MOD
  (999983:num)`];;

let add_part_def = new_definition
  `add_part n p aux acc =
     (let h = part_hash p in
       match sptree_lookup h aux with NONE -> (n + 1,n,sptree_insert
         h [(p,n)] aux,p :: acc) | SOME bucket ->
           (match ALOOKUP bucket p with NONE -> (n +
             1,n,sptree_insert h ((p,n) :: bucket) aux,p :: acc) |
             SOME k -> (n,k,aux,acc)))`;;

let add_parts_def = define_mutual_rec
  [`add_parts (ConstInt i) n aux acc = add_part n (Int i) aux acc`;
   `add_parts (ConstStr s) n aux acc = add_part n (closLang_Str s)
  aux acc`;
   `add_parts (ConstWord64 w) n aux acc = add_part n (W64 w) aux acc`;
   `add_parts (ConstCons t cs) n aux acc =
      (let (n,rs,aux,acc) = add_parts_list cs n aux acc in
         add_part n (Con (clos_tag_shift t) rs) aux acc)`;
   `add_parts_list [] n aux acc = (n,[],aux,acc)`;
   `add_parts_list (c :: cs) n aux acc =
      (let (n,r,aux,acc) = add_parts c n aux acc in
      let (n,rs,aux,acc) = add_parts_list cs n aux acc in
        (n,r :: rs,aux,acc))`];;

let compile_const_def = define_cases
  [`compile_const (ConstInt i) = closLang_IntOp (closLang_Const i)`;
   `compile_const (ConstStr s) = closLang_BlockOp (closLang_Build
  [closLang_Str s])`;
   `compile_const (ConstWord64 w) = closLang_BlockOp (closLang_Build
  [W64 w])`;
   `compile_const (ConstCons t cs) =
      (if NULL cs then closLang_BlockOp (closLang_Cons
        (clos_tag_shift t)) else
        let (n,rs,aux,acc) = add_parts_list cs 0 LN [] in
          closLang_BlockOp (closLang_Build (REVERSE ((Con
            (clos_tag_shift t) rs) :: acc))))`];;

(* / Constant flattening *)

let num_added_globals_def = new_definition
  `num_added_globals = 1`;;

let partial_app_label_table_loc_def = new_definition
  `partial_app_label_table_loc = 0`;;

let clos_to_bvl_compile_op_def = new_definition
  `clos_to_bvl_compile_op x =
      match x with
        closLang_BlockOp (closLang_Cons tag) -> closLang_BlockOp
          (closLang_Cons (clos_tag_shift tag))
      | (closLang_BlockOp (closLang_ConsExtend tag)) ->
        closLang_BlockOp (closLang_ConsExtend (clos_tag_shift tag))
      | (closLang_BlockOp (closLang_TagEq tag)) -> closLang_BlockOp
        (closLang_TagEq (clos_tag_shift tag))
      | (closLang_BlockOp (closLang_TagLenEq tag a)) ->
        closLang_BlockOp (closLang_TagLenEq (clos_tag_shift tag) a)
      | (closLang_BlockOp (closLang_FromList tag)) ->
        closLang_BlockOp (closLang_FromList (clos_tag_shift tag))
      | (closLang_MemOp closLang_LengthByteVec) -> closLang_MemOp
        closLang_LengthByte
      | (closLang_MemOp closLang_DerefByteVec) -> closLang_MemOp
        closLang_DerefByte
      | (closLang_GlobOp (closLang_SetGlobal n)) -> closLang_GlobOp
        (closLang_SetGlobal (n + num_added_globals))
      | (closLang_GlobOp (closLang_Global n)) -> closLang_GlobOp
        (closLang_Global (n + num_added_globals))
      | (closLang_BlockOp (closLang_Constant c)) -> compile_const c
      | x -> x`;;
hol4_overload "compile_op" "clos_to_bvl_compile_op";;

let compile_op_pmatch = prove
 (`!op.
   clos_to_bvl_compile_op op =
     (match op with
         closLang_BlockOp (closLang_Cons tag) -> closLang_BlockOp
           (closLang_Cons (clos_tag_shift tag)) | closLang_BlockOp
           (closLang_ConsExtend tag) -> closLang_BlockOp
           (closLang_ConsExtend (clos_tag_shift tag)) |
           closLang_BlockOp (closLang_TagEq tag) -> closLang_BlockOp
           (closLang_TagEq (clos_tag_shift tag)) | closLang_BlockOp
           (closLang_TagLenEq tag a) -> closLang_BlockOp
           (closLang_TagLenEq (clos_tag_shift tag) a) |
           closLang_BlockOp (closLang_FromList tag) ->
           closLang_BlockOp (closLang_FromList (clos_tag_shift tag)) |
           closLang_MemOp closLang_LengthByteVec -> closLang_MemOp
           closLang_LengthByte | closLang_MemOp closLang_DerefByteVec
           -> closLang_MemOp closLang_DerefByte | closLang_GlobOp
           (closLang_SetGlobal n) -> closLang_GlobOp
           (closLang_SetGlobal (n + num_added_globals)) |
           closLang_GlobOp (closLang_Global n) -> closLang_GlobOp
           (closLang_Global (n + num_added_globals)) |
           closLang_BlockOp (closLang_Constant c) -> compile_const c |
           x -> x)`,
  CHEAT_TAC);;

let mk_const_def = new_definition
  `(mk_const n:bvl_exp) = Op (closLang_IntOp (closLang_Const (&n)))
  []`;;

let mk_label_def = new_definition
  `(mk_label n:bvl_exp) = Op (closLang_Label n) []`;;

let mk_el_def = new_definition
  `(mk_el b i:bvl_exp) = Op (closLang_MemOp closLang_El) [i; b]`;;

let free_let_def = new_definition
  `free_let cl n = (GENLIST (\n. (\b i. bvl_Op (closLang_BlockOp
  (closLang_ElemAt i)) [b]) cl (n + 2)) n)`;;

let code_for_recc_case_def = new_definition
  `code_for_recc_case n num_args (c:bvl_exp) =
     (num_args + 1,
      Let [(\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b])
        (Var num_args) 2]
       (bvl_Let (GENLIST (\a. Var (a + 1)) num_args ++ GENLIST
         (\i. (\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i))
         [b]) (Var 0) i) n) c))`;;

let build_aux_def,build_aux_ind = define_rec
  [`build_aux (i:num) [] aux = ((i:num),aux)`;
   `build_aux (i:num) ((x:num#bvl_exp) :: xs) aux = build_aux (i +
  2) xs ((i,x) :: aux)`];;

let build_aux_LENGTH = prove
 (`!l n aux n1 t.
      (build_aux n l aux = (n1,t)) ==> (n1 = n + 2 * LENGTH l)`,
  CHEAT_TAC);;

let build_aux_MOVE = prove
 (`!xs n aux n1 aux1.
      (build_aux n xs aux = (n1,aux1)) <=>
      (?aux2. (build_aux n xs [] = (n1,aux2)) /\ (aux1 = aux2 ++
        aux))`,
  CHEAT_TAC);;

let build_aux_acc = prove
 (`!k n aux. ?aux1. SND (build_aux n k aux) = aux1 ++ aux`,
  CHEAT_TAC);;

let build_aux_MEM = prove
 (`!c n aux n7 aux7.
       (build_aux n c aux = (n7,aux7)) ==>
       (!k. k < LENGTH c ==> (?d. MEM (n + 2 * k,d) aux7))`,
  CHEAT_TAC);;

let build_aux_APPEND1 = prove
 (`!xs x n aux.
      build_aux n (xs ++ [x]) aux =
        (let (n1,aux1) = build_aux n xs aux in
          (n1 + 2,(n1,x) :: aux1))`,
  CHEAT_TAC);;

let recc_Let_def = new_definition
  `recc_Let n num_args i =
     Let [(\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b])
       (Var 0) 2]
      (bvl_Let [Op (closLang_BlockOp (closLang_Cons closure_tag))
        [Var 0; mk_const (num_args - 1); mk_label n]]
        (bvl_Let [Op (closLang_MemOp closLang_Update) [Var 0;
          mk_const i; Var 1]]
          (Var 1:bvl_exp)))`;;

(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let recc_Lets_def,recc_Lets_ind = define_wf
  `MEASURE (\(x0,x1,x2,x3). (\n. n) x2)`
  [`recc_Lets n nargs k rest =
     (if k = (0:num) then rest else
       let k = k - 1 in
         Let [recc_Let (n + 2 * k) (HD nargs) k] (recc_Lets n
           (TL nargs) k rest))`];;

let recc_Let0_def = new_definition
  `recc_Let0 n num_args i =
     Let [Op (closLang_BlockOp (closLang_Cons closure_tag)) [Var 0;
       mk_const (num_args - 1); mk_label n]]
       (bvl_Let [Op (closLang_MemOp closLang_Update) [Var 0;
         mk_const i; Var 1]] (Var 1:bvl_exp))`;;

let build_recc_lets_def = new_definition
  `build_recc_lets (nargs:num list) vs n1 fns_l (c3:bvl_exp) =
     Let [Let [Op (closLang_MemOp closLang_Ref) (REVERSE (MAP (K
       (mk_const 0)) nargs ++ MAP Var vs))]
            (recc_Let0 (n1 + (2 * (fns_l - 1))) (HD (REVERSE nargs))
              (fns_l - 1))]
       (recc_Lets n1 (TL (REVERSE nargs)) (fns_l - 1) c3)`;;

let num_stubs_def = new_definition
  `num_stubs max_app =
              // generic apps
              max_app + (
              // partial apps
              max_app * (max_app - 1)) DIV 2 + 1 +
       // code to install a jump table in global 0
       1
   // location for force_thunk stub`;;

let generic_app_fn_location_def = new_definition
  `generic_app_fn_location n = n`;;

let partial_app_fn_location_def = new_definition
  `partial_app_fn_location (max_app:num) tot prev =
     max_app + (tot * (tot - 1)) DIV 2 + prev`;;

let partial_app_fn_location_code_def = new_definition
  `(partial_app_fn_location_code max_app tot_exp prev_exp:bvl_exp) =
     Let [tot_exp]
      (bvl_Op (closLang_IntOp closLang_Add) [prev_exp;
         Op (closLang_IntOp closLang_Div) [mk_const 2;
           Op (closLang_IntOp closLang_Mult) [Var 0; Op
             (closLang_IntOp closLang_Sub) [mk_const 1; Var 0]]]])`;;

let mk_cl_call_def = new_definition
  `mk_cl_call cl args =
     If (Op (closLang_BlockOp (closLang_EqualConst (closLang_Int
       (&(LENGTH args - 1))))) [(\b i. bvl_Op (closLang_BlockOp
       (closLang_ElemAt i)) [b]) cl 1])
        (Call (LENGTH args - 1) NONE (args ++ [cl] ++ [(\b i. bvl_Op
          (closLang_BlockOp (closLang_ElemAt i)) [b]) cl 0]))
        (Call 0 (SOME (generic_app_fn_location (LENGTH args - 1)))
          (args ++ [cl]))`;;

(* Generic application of a function to n+1 arguments *)
let generate_generic_app_def = new_definition
  `generate_generic_app max_app n =
     Let [Op (closLang_IntOp closLang_Sub) [mk_const (n + 1); (\b i.
       bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b]) (Var (n + 1))
       1]]
         (
          // The number of arguments remaining - 1
          bvl_If (bvl_Op (closLang_IntOp closLang_Less) [mk_const 0;
            Var 0])
             (
              // Over application
              bvl_jump_Jump ((\b i. bvl_Op (closLang_BlockOp
                (closLang_ElemAt i)) [b]) (Var (n + 2)) 1)
               (GENLIST (\num_args.
                  Let [Call num_args
                            NONE
                            (GENLIST (\arg. Var ((arg + 2 + n) -
                              num_args)) (num_args + 1) ++
                             [Var (n + 3)] ++
                             [(\b i. bvl_Op (closLang_BlockOp
                               (closLang_ElemAt i)) [b]) (Var (n + 3))
                               0])]
                    (mk_cl_call (Var 0) (GENLIST (\n. Var (n + 3)) (n
                      - num_args))))
                max_app))
             (
              // Partial application
              mk_tick n
             (If (Op (closLang_BlockOp (closLang_TagEq closure_tag))
               [Var (n + 2)])
                 (
                  // Partial application of a normal closure
                  Op (closLang_BlockOp (closLang_Cons
                    partial_app_tag))
                     (REVERSE
                       (mk_el (Op (closLang_GlobOp (closLang_Global
                         0)) [])
                         (partial_app_fn_location_code max_app
                           ((\b i. bvl_Op (closLang_BlockOp
                             (closLang_ElemAt i)) [b]) (Var (n + 2)) 1)
                           (mk_const n)) ::
                        Var 0 ::
                        Var (n + 2) ::
                        GENLIST (\n. Var (n + 1)) (n + 1))))
                 (
                  // Partial application of a partially applied closure
                  Let [Op (closLang_IntOp closLang_Sub) [mk_const 3;
                    Op (closLang_BlockOp closLang_LengthBlock) [Var (n +
                    2)]]]
                   (
                    // The number of previous args
                    bvl_Op (closLang_BlockOp (closLang_ConsExtend
                      partial_app_tag))
                     (REVERSE
                       (Var (n + 3) ::
                        mk_const 3 ::
                        Var 0 ::
                        Op (closLang_IntOp closLang_Add) [Var 0;
                          mk_const (n + 4)] ::
                        mk_el (Op (closLang_GlobOp (closLang_Global
                          0)) [])
                          (partial_app_fn_location_code max_app
                            (Op (closLang_IntOp closLang_Add) [Var 0;
                              Op (closLang_IntOp closLang_Add) [mk_const
                              (n + 1); Var 1]])
                            (
                             // Shift from Var0 to Var1 because of Let in
                             // * partial_app_fn_location_code
                             Op (closLang_IntOp closLang_Add) [Var 1;
                               mk_const n])) ::
                        Var 1 ::
                        (\b i. bvl_Op (closLang_BlockOp
                          (closLang_ElemAt i)) [b]) (Var (n + 3)) 2 ::
                        GENLIST (\this_arg. Var (this_arg + 2)) (n
                          + 1))))))))`;;

(* The functions to complete the application of a partial closure.
 * We expect prev_args < total_args, also the function should take one more
 * argument than total, and have seen one more than prev (since there is
 * possiblity for a 0 argument function, or a partial application wrapper that
 * has seen no arguments yet. *)
let generate_partial_app_closure_fn_def = new_definition
  `generate_partial_app_closure_fn total_args prev_args =
     Let [(\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b])
       (Var (total_args - prev_args)) 2]
       (bvl_Call 0
         NONE
         (GENLIST (\this_arg. Var (this_arg + 1)) (total_args -
           prev_args) ++
          GENLIST (\prev_arg.
            (\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i)) [b])
              (Var (total_args - prev_args + 1)) (prev_arg + 3))
              (prev_args + 1) ++
          [Var 0] ++
          [(\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i))
            [b]) (Var 0) 0]))`;;

let check_closure_def = new_definition
  `check_closure v e =
     If (Op (closLang_BlockOp (closLang_TagEq closure_tag)) [Var v])
       (bvl_Bool T)
       (If (Op (closLang_BlockOp (closLang_TagEq partial_app_tag))
         [Var v]) (bvl_Bool T) e)`;;

let init_code_def = new_definition
  `clos_to_bvl_init_code max_app =
     sptree_fromList
       (GENLIST (\n. (n + 2,generate_generic_app max_app n)) max_app
         ++
        FLAT
          (GENLIST
            (\tot.
              GENLIST
                (\prev. (tot - prev +
                  1,generate_partial_app_closure_fn tot prev))
                tot)
            max_app))`;;
hol4_overload "init_code" "clos_to_bvl_init_code";;

let init_globals_def = new_definition
  `init_globals max_app start_loc =
     Let [Op (closLang_GlobOp closLang_AllocGlobal) [Op
       (closLang_IntOp (closLang_Const (&1))) []]]
     (bvl_Let
       [Op (closLang_GlobOp (closLang_SetGlobal
         partial_app_label_table_loc))
         [Op (closLang_BlockOp (closLang_Cons tuple_tag))
           (REVERSE (FLAT
             (GENLIST
               (\tot.
                 GENLIST
                   (\prev. mk_label (partial_app_fn_location max_app
                     tot prev))
                   tot)
               max_app)))]]
       (
        // Expect the real start of the program in code location 3
        bvl_Call 0 (SOME start_loc) []))`;;

let force_thunk_code_def = new_definition
  `force_thunk_code =
     (If (Op (closLang_BlockOp (closLang_EqualConst (closLang_Int
       (&0)))) [(\b i. bvl_Op (closLang_BlockOp (closLang_ElemAt i))
       [b]) (Var 1) 1])
       (Let [Call 0 NONE [(bvl_Op (closLang_BlockOp (closLang_Cons
         0)) []); Var 1; (\b i. bvl_Op (closLang_BlockOp
         (closLang_ElemAt i)) [b]) (Var 1) 0]]
         (bvl_Let [Op (ThunkOp (UpdateThunk Evaluated)) [Var 0; Var
           1]] (bvl_Var 1)))
       (Let [Call 0 (SOME 0) [(bvl_Op (closLang_BlockOp
         (closLang_Cons 0)) []); Var 1]]
         (bvl_Let [Op (ThunkOp (UpdateThunk Evaluated)) [Var 0;
           Var 1]] (bvl_Var 1))):bvl_exp)`;;

let _ = size_thms "closLang_exp";;
(* HOL4 clos_to_bvlScript.sml:483-493: the tactic that proves the
   termination *)
let clos_to_bvl_compile_exps_def,clos_to_bvl_compile_exps_ind =
  define_guess
  [`clos_to_bvl_compile_exps max_app [] aux = ([],aux)`;
   `clos_to_bvl_compile_exps max_app ((x:closLang_exp) :: y :: xs) aux =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app [x] aux
           in
         let (c2,aux2) = clos_to_bvl_compile_exps max_app (y :: xs)
           aux1 in
           (c1 ++ c2,aux2))`;
   `clos_to_bvl_compile_exps max_app [(Var t v:closLang_exp)] aux =
  ([(Var v):bvl_exp],aux)`;
   `clos_to_bvl_compile_exps max_app [(If t x1 x2 x3:closLang_exp)] aux
  =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux
           in
         let (c2,aux2) = clos_to_bvl_compile_exps max_app [x2] aux1
           in
         let (c3,aux3) = clos_to_bvl_compile_exps max_app [x3] aux2
           in
           ([If (HD c1) (HD c2) (HD c3)],aux3))`;
   `clos_to_bvl_compile_exps max_app [(Let t xs x2:closLang_exp)] aux =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
         let (c2,aux2) = clos_to_bvl_compile_exps max_app [x2] aux1
           in
           ([Let c1 (HD c2)],aux2))`;
   `clos_to_bvl_compile_exps max_app [(Raise t x1:closLang_exp)] aux =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux
           in
           ([Raise (HD c1)],aux1))`;
   `clos_to_bvl_compile_exps max_app [(Tick t x1:closLang_exp)] aux =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux
           in
           ([Tick (HD c1)],aux1))`;
   `clos_to_bvl_compile_exps max_app [(Op t op xs:closLang_exp)] aux =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
         (
         [if op = closLang_Install then
             Call 0 NONE [Op closLang_Install c1] else if op =
               ThunkOp ForceThunk then
             Let c1 (Force (num_stubs max_app - 2) 0) else
             Op (clos_to_bvl_compile_op op) c1],aux1))`;
   `clos_to_bvl_compile_exps max_app [(App t loc_opt x1
  xs2:closLang_exp)] aux =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux
           in
         let (c2,aux2) = clos_to_bvl_compile_exps max_app xs2 aux1
           in
           ([match loc_opt with NONE ->
                 Let (c2 ++ c1) (mk_cl_call (Var (LENGTH c2))
                   (GENLIST Var (LENGTH c2))) | SOME loc ->
                 (Call (LENGTH c2 - 1) (SOME (loc + (num_stubs
                   max_app))) (c2 ++ c1))],
            aux2))`;
   `clos_to_bvl_compile_exps max_app [closLang_Fn t loc_opt vs_opt
  num_args x1] aux =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
         let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux
           in
         let c2 =
           Let (GENLIST Var num_args ++ free_let (Var num_args)
             (LENGTH vs))
               (HD c1) in
           ([Op (closLang_BlockOp (closLang_Cons closure_tag))
                (REVERSE (mk_label (loc + num_stubs max_app) ::
                  mk_const (num_args - 1) :: MAP Var vs))],
            (loc + (num_stubs max_app),num_args + 1,c2) :: aux1))`;
   `clos_to_bvl_compile_exps max_app [(Letrec t loc_opt vsopt fns
  x1:closLang_exp)] aux =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let vs = (match vsopt with NONE -> [] | SOME x -> x) in
         match fns with [] -> clos_to_bvl_compile_exps max_app [x1]
           aux | [(num_args,exp)] ->
             (let (c1,aux1) = clos_to_bvl_compile_exps max_app [exp]
               aux in
             let c3 = Let (GENLIST Var num_args ++ [Var num_args] ++
               free_let (Var num_args) (LENGTH vs)) (HD c1) in
             let (c2,aux2) = clos_to_bvl_compile_exps max_app [x1]
               ((loc + (num_stubs max_app),num_args + 1,c3) :: aux1) in
             let c4 =
               Op (closLang_BlockOp (closLang_Cons closure_tag))
                  (REVERSE (mk_label (loc + (num_stubs max_app)) ::
                    mk_const (num_args - 1) :: MAP Var vs)) in
               ([Let [c4] (HD c2)],aux2)) | _3 ->
             (let fns_l = LENGTH fns in
             let l = fns_l + LENGTH vs in
             let (cs,aux1) = clos_to_bvl_compile_exps max_app (MAP
               SND fns) aux in
             let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs
               in
             let (n2,aux2) = build_aux (loc + (num_stubs max_app))
               cs1 aux1 in
             let (c3,aux3) = clos_to_bvl_compile_exps max_app [x1]
               aux2 in
             let c4 = build_recc_lets (MAP FST fns) vs (loc +
               (num_stubs max_app)) fns_l (HD c3) in
               ([c4],aux3)))`;
   `clos_to_bvl_compile_exps max_app [(Handle t x1 x2:closLang_exp)] aux
  =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app [x1] aux
           in
         let (c2,aux2) = clos_to_bvl_compile_exps max_app [x2] aux1
           in
           ([Handle (HD c1) (HD c2)],aux2))`;
   `clos_to_bvl_compile_exps max_app [(Call t ticks dest
  xs:closLang_exp)] aux =
         (let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
           ([Call ticks (SOME (dest + (num_stubs max_app)))
             c1],aux1))`];;
hol4_overload "compile_exps" "clos_to_bvl_compile_exps";;

(* HOL4 clos_to_bvlScript.sml:495: ML code, not ported *)

let _ = size_thms "bvl_exp";;
let _ = size_thms "closLang_exp";;
(* HOL4 clos_to_bvlScript.sml:575-583: the tactic that proves the
   termination *)
let compile_exp_sing_def = define_mutual_guess
  [`compile_exp_sing max_app (Var t v:closLang_exp) aux = (((Var
  v):bvl_exp),aux)`;
   `compile_exp_sing max_app (If t x1 x2 x3:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_sing max_app x1 aux in
         let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
         let (c3,aux3) = compile_exp_sing max_app x3 aux2 in
           (If c1 c2 c3,aux3))`;
   `compile_exp_sing max_app (Let t xs x2:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_list max_app xs aux in
         let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
           (Let c1 c2,aux2))`;
   `compile_exp_sing max_app (Raise t x1:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_sing max_app x1 aux in
           (Raise c1,aux1))`;
   `compile_exp_sing max_app (Tick t x1:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_sing max_app x1 aux in
           (Tick c1,aux1))`;
   `compile_exp_sing max_app (Op t op xs:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_list max_app xs aux in
         (
         (if op = closLang_Install then Call 0 NONE [Op
           closLang_Install c1] else if op = ThunkOp ForceThunk then
           Let c1 (Force (num_stubs max_app - 2) 0) else Op
           (clos_to_bvl_compile_op op) c1),aux1))`;
   `compile_exp_sing max_app (App t loc_opt x1 xs2:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_sing max_app x1 aux in
         let (c2,aux2) = compile_exp_list max_app xs2 aux1 in
           ((match loc_opt with NONE ->
                 Let (c2 ++ [c1]) (mk_cl_call (Var (LENGTH c2))
                   (GENLIST Var (LENGTH c2))) | SOME loc ->
                 (Call (LENGTH c2 - 1) (SOME (loc + (num_stubs
                   max_app))) (c2 ++ [c1]))),
            aux2))`;
   `compile_exp_sing max_app (closLang_Fn t loc_opt vs_opt num_args x1)
  aux =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let vs = (match vs_opt with NONE -> [] | SOME vs -> vs) in
         let (c1,aux1) = compile_exp_sing max_app x1 aux in
         let c2 =
           Let (GENLIST Var num_args ++ free_let (Var num_args)
             (LENGTH vs)) c1 in
           (Op (closLang_BlockOp (closLang_Cons closure_tag))
               (REVERSE (mk_label (loc + num_stubs max_app) ::
                 mk_const (num_args - 1) :: MAP Var vs)),
            (loc + (num_stubs max_app),num_args + 1,c2) :: aux1))`;
   `compile_exp_sing max_app (Letrec t loc_opt vsopt fns
  x1:closLang_exp) aux =
         (let loc = (match loc_opt with NONE -> 0 | SOME n -> n) in
         let vs = (match vsopt with NONE -> [] | SOME x -> x) in
         match fns with [] -> compile_exp_sing max_app x1 aux |
           [(num_args,exp)] ->
             (let (c1,aux1) = compile_exp_sing max_app exp aux in
             let c3 = Let (GENLIST Var num_args ++ [Var num_args] ++
               free_let (Var num_args) (LENGTH vs)) c1 in
             let (c2,aux2) = compile_exp_sing max_app x1 ((loc +
               (num_stubs max_app),num_args + 1,c3) :: aux1) in
             let c4 =
               Op (closLang_BlockOp (closLang_Cons closure_tag))
                  (REVERSE (mk_label (loc + (num_stubs max_app)) ::
                    mk_const (num_args - 1) :: MAP Var vs)) in
               (bvl_Let [c4] c2,aux2)) | _6 ->
             (let fns_l = LENGTH fns in
             let l = fns_l + LENGTH vs in
             let (cs,aux1) = compile_exp_list max_app (MAP SND fns)
               aux in
             let cs1 = MAP2 (code_for_recc_case l) (MAP FST fns) cs
               in
             let (n2,aux2) = build_aux (loc + (num_stubs max_app))
               cs1 aux1 in
             let (c3,aux3) = compile_exp_sing max_app x1 aux2 in
             let c4 = build_recc_lets (MAP FST fns) vs (loc +
               (num_stubs max_app)) fns_l c3 in
               (c4,aux3)))`;
   `compile_exp_sing max_app (Handle t x1 x2:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_sing max_app x1 aux in
         let (c2,aux2) = compile_exp_sing max_app x2 aux1 in
           (Handle c1 c2,aux2))`;
   `compile_exp_sing max_app (Call t ticks dest xs:closLang_exp) aux =
         (let (c1,aux1) = compile_exp_list max_app xs aux in
           (Call ticks (SOME (dest + (num_stubs max_app)))
             c1,aux1))`;
   `compile_exp_list max_app [] aux = ([],aux)`;
   `compile_exp_list max_app ((x:closLang_exp) :: xs) aux =
         (let (c1,aux1) = compile_exp_sing max_app x aux in
         let (c2,aux2) = compile_exp_list max_app xs aux1 in
           (c1 :: c2,aux2))`];;

let compile_exp_sing_eq = prove
 (`(!n e l. clos_to_bvl_compile_exps n [e] l = (\(a,b). ([a],b))
  (compile_exp_sing n e l)) /\
   (!n es l. clos_to_bvl_compile_exps n es l = compile_exp_list n
     es l)`,
  CHEAT_TAC);;

let clos_to_bvl_compile_prog_def = new_definition
  `clos_to_bvl_compile_prog max_app prog =
     (let (new_exps,aux) = clos_to_bvl_compile_exps max_app (MAP (SND
       o SND) prog) [] in
       MAP2 (\(loc,args,_7) exp. (loc + num_stubs max_app,args,exp))
         prog new_exps ++ aux)`;;
hol4_overload "compile_prog" "clos_to_bvl_compile_prog";;

(* HOL4 clos_to_bvlScript.sml:610: a theorem that HOL4 states as the
   value of an ML expression: compile_prog_eq *)

(* [local] *)
let pair_lem1 = prove
 (`!f x. (\(a,b). f a b) x = f (FST x) (SND x)`,
  CHEAT_TAC);;

(* [local] *)
let pair_lem2 = prove
 (`!x y z. (x,y) = z <=> x = FST z /\ y = SND z`,
  CHEAT_TAC);;

let compile_exps_acc = prove
 (`!max_app xs aux.
      let (c,aux1) = clos_to_bvl_compile_exps max_app xs aux in
        (LENGTH c = LENGTH xs) /\ (?ys. aux1 = ys ++ aux)`,
  CHEAT_TAC);;

(* compile_exps_LENGTH *)
let clos_to_bvl_compile_exps_LENGTH = prove
 (`(clos_to_bvl_compile_exps max_app xs aux = (c,aux1)) ==> (LENGTH c
  = LENGTH xs)`,
  CHEAT_TAC);;

(* compile_exps_SING *)
let clos_to_bvl_compile_exps_SING = prove
 (`(clos_to_bvl_compile_exps max_app [x] aux = (c,aux1)) ==> (?d. c =
  [d])`,
  CHEAT_TAC);;

let compile_exps_CONS = prove
 (`!max_app xs x aux.
      clos_to_bvl_compile_exps max_app (x :: xs) aux =
      (let (c1,aux1) = clos_to_bvl_compile_exps max_app [x] aux in
       let (c2,aux2) = clos_to_bvl_compile_exps max_app xs aux1 in
         (c1 ++ c2,aux2))`,
  CHEAT_TAC);;

let compile_exps_SNOC = prove
 (`!xs x aux max_app.
      clos_to_bvl_compile_exps max_app (SNOC x xs) aux =
      (let (c1,aux1) = clos_to_bvl_compile_exps max_app xs aux in
       let (c2,aux2) = clos_to_bvl_compile_exps max_app [x] aux1 in
         (c1 ++ c2,aux2))`,
  CHEAT_TAC);;

let clos_to_bvl_config_FIELDS = define_record "clos_to_bvl_config"
  ["next_loc","num";
   "start","num";
   "do_mti","bool";
   "known_conf","clos_known_config option";
   "do_call","bool";
   "call_state","1 spt#(num#num#closLang_exp) list";
   "max_app","num"];;
hol4_field_overload "start" "clos_to_bvl_config_start";;
hol4_field_overload "start_fupd" "clos_to_bvl_config_start_fupd";;

let clos_to_bvl_default_config_def = new_definition
  `clos_to_bvl_default_config = mk_clos_to_bvl_config 0 1 T (SOME
  (clos_known_default_config 10)) T (LN,[]) 10`;;
hol4_overload "default_config" "clos_to_bvl_default_config";;

let code_split_def,code_split_ind = define_rec
  [`code_split [] xs ys = (xs,ys)`;
   `code_split (z :: zs) xs ys = code_split zs (z :: ys) xs`];;

(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 clos_to_bvlScript.sml:725-727: the tactic that proves the
   termination *)
let code_merge_def,code_merge_ind = define_wf
  `MEASURE (\(xs,ys). LENGTH xs + LENGTH ys)`
  [`code_merge xs ys =
     (match (xs,ys) with ([],[]) -> [] | ([],_8) -> ys | (_9,[]) ->
       xs | (x1 :: xs1,y1 :: ys1) ->
         (if FST x1 < ((FST y1):num) then
           x1 :: code_merge xs1 ys else
           y1 :: code_merge xs ys1))`];;

let code_split_NULL = prove
 (`!ts1 ts2 ts3 xs ys.
      (xs,ys) = code_split ts1 ts2 ts3 /\ ~(ts2 = []) /\ ~(ts3 =
        []) ==> ~(xs = []) /\ ~(ys = [])`,
  CHEAT_TAC);;

let code_split_LENGTH = prove
 (`!ts1 ts2 ts3 xs ys.
      (xs,ys) = code_split ts1 ts2 ts3 ==>
      LENGTH xs + LENGTH ys = LENGTH ts1 + LENGTH ts2 + LENGTH ts3`,
  CHEAT_TAC);;

let code_sort_def = define_cases
  [`code_sort [] = []`;
   `code_sort [x] = [x]`;
   `code_sort (x :: y :: xs) =
         (let (xs,ys) = code_split xs [x] [y] in
           code_merge (code_sort xs) (code_sort ys))`];;

let _ = size_thms "closLang_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let chain_exps_def,chain_exps_ind = define_wf
  `MEASURE (\(x0,x1). closLang_exp_size1 x1)`
  [`chain_exps i x2 =
        match x2 with
          [] -> [(i,0,Op backend_common_None (closLang_IntOp
            (closLang_Const (&0))) [])]
        | [e] -> [(i,0,e)]
        | (e :: es) ->
       (i,0,
        closLang_Let backend_common_None [e] (closLang_Call
          backend_common_None 0 (i + 1) [])) :: chain_exps (i + 1)
          es`];;

(* c.max_app must be the same each time this is called *)
let compile_common_def = new_definition
  `compile_common c es =
     (let es = clos_mti_compile (clos_to_bvl_config_do_mti c)
       (clos_to_bvl_config_max_app c) es in
     // Add space for functions to call the expressions
     let loc = clos_to_bvl_config_next_loc c + MAX 1 (LENGTH es) in
     // Alignment padding
     let loc = (if loc MOD 2 = 0 then loc else loc + 1) in
     let (n,es) = renumber_code_locs_list loc es in
     let (kc,es) = clos_known_compile (clos_to_bvl_config_known_conf
       c) es in
     let (es,g,aux) = clos_call_compile (clos_to_bvl_config_do_call
       c) es in
     let prog = chain_exps (clos_to_bvl_config_next_loc c) es ++ aux
       in
     let prog = clos_annotate_compile prog in
       (clos_to_bvl_config_call_state_fupd (K (g,aux))
         (clos_to_bvl_config_known_conf_fupd (K kc)
         (clos_to_bvl_config_next_loc_fupd (K n)
         (clos_to_bvl_config_start_fupd (K (clos_to_bvl_config_next_loc
         c)) c))),
        prog))`;;

let add_src_names_def,add_src_names_ind = define_rec
  [`add_src_names n [] l = l`;
   `add_src_names n (x :: xs) l =
      add_src_names (n + 2) xs (sptree_insert n
        (mlstring_concat [x; implode "_clos"]) (sptree_insert (n +
        1) x l))`];;

let _ = size_thms "closLang_exp";;
(* HOL4 clos_to_bvlScript.sml:812-817: the tactic that proves the
   termination *)
let get_src_names_def,get_src_names_ind = define_guess
  [`get_src_names [] l = l`;
   `get_src_names (x :: y :: xs) l = get_src_names (y :: xs)
  (get_src_names [x] l)`;
   `get_src_names [closLang_If _10 x y z] l =
      get_src_names [x] (get_src_names [y] (get_src_names [z] l))`;
   `get_src_names [closLang_Var _11 _12] l = l`;
   `get_src_names [closLang_Let _13 xs x] l = get_src_names (x :: xs)
  l`;
   `get_src_names [(Raise _15 x:closLang_exp)] l = get_src_names [x]
  l`;
   `get_src_names [(Handle _17 x y:closLang_exp)] l = get_src_names
  [x] (get_src_names [y] l)`;
   `get_src_names [(Tick _19 x:closLang_exp)] l = get_src_names [x] l`;
   `get_src_names [(Call _23 _24 _25 xs:closLang_exp)] l =
  get_src_names xs l`;
   `get_src_names [(Op _28 _29 xs:closLang_exp)] l = get_src_names xs
  l`;
   `get_src_names [(App _32 _33 x xs:closLang_exp)] l = get_src_names
  (x :: xs) l`;
   `get_src_names [closLang_Fn name loc_opt _34 _35 x] l =
      (let l1 = get_src_names [x] l in
         match loc_opt with NONE -> l1 | SOME n -> add_src_names
           n [name] l1)`;
   `get_src_names [(Letrec names loc_opt _37 funs x:closLang_exp)] l =
      (let l0 = get_src_names (MAP SND funs) l in
       let l1 = get_src_names [x] l0 in
         match loc_opt with NONE -> l1 | SOME n ->
           add_src_names n names l1)`];;

let _ = size_thms "closLang_exp";;
(* HOL4 clos_to_bvlScript.sml:844-851: the tactic that proves the
   termination *)
let get_src_names_sing_def = define_mutual_guess
  [`get_src_names_sing (closLang_If _38 x y z) l =
      get_src_names_sing x (get_src_names_sing y
        (get_src_names_sing z l))`;
   `get_src_names_sing (closLang_Var _39 _40) l = l`;
   `get_src_names_sing (closLang_Let _41 xs x) l =
      get_src_names_list xs (get_src_names_sing x l)`;
   `get_src_names_sing (Raise _43 x:closLang_exp) l =
  get_src_names_sing x l`;
   `get_src_names_sing (Handle _45 x y:closLang_exp) l =
  get_src_names_sing x (get_src_names_sing y l)`;
   `get_src_names_sing (Tick _47 x:closLang_exp) l =
  get_src_names_sing x l`;
   `get_src_names_sing (Call _51 _52 _53 xs:closLang_exp) l =
  get_src_names_list xs l`;
   `get_src_names_sing (Op _56 _57 xs:closLang_exp) l =
  get_src_names_list xs l`;
   `get_src_names_sing (App _60 _61 x xs:closLang_exp) l =
      get_src_names_list xs (get_src_names_sing x l)`;
   `get_src_names_sing (closLang_Fn name loc_opt _62 _63 x) l =
      (let l1 = get_src_names_sing x l in
         match loc_opt with NONE -> l1 | SOME n -> add_src_names
           n [name] l1)`;
   `get_src_names_sing (Letrec names loc_opt _65 funs x:closLang_exp) l
  =
      (let l0 = get_src_names_list (MAP SND funs) l in
       let l1 = get_src_names_sing x l0 in
         match loc_opt with NONE -> l1 | SOME n -> add_src_names
           n names l1)`;
   `get_src_names_list [] l = l`;
   `get_src_names_list (x :: xs) l = get_src_names_list xs
  (get_src_names_sing x l)`];;

let get_src_names_sing_eq = prove
 (`(!e l. get_src_names [e] l = get_src_names_sing e l) /\
   (!es l. get_src_names es l = get_src_names_list es l)`,
  CHEAT_TAC);;

let make_name_alist_def = new_definition
  `make_name_alist nums prog nstubs dec_start (dec_length:num) =
     (let src_names = get_src_names (MAP (SND o SND) prog) LN in
       fromAList (MAP (\n. (n,(if n < nstubs then
                              if n = nstubs - 1 then implode
                                "bvl_init" else
                              if n = nstubs - 2 then implode
                                "bvl_force" else
                              implode "bvl_stub" else let clos_name =
                                n - nstubs in
                              if dec_start <= clos_name /\ clos_name
                                < dec_start + dec_length then implode
                                "dec" else
                              match sptree_lookup clos_name
                                src_names with NONE -> implode
                                "unknown_clos_fun" | SOME s -> s)))
                                nums):mlstring spt)`;;

(* HOL4 clos_to_bvlScript.sml:878-879: a theorem that HOL4 states as
   the value of an ML expression: make_name_alist_eq *)

let clos_to_bvl_compile_def = new_definition
  `clos_to_bvl_compile c0 es =
     (let (c,prog) = compile_common c0 es in
     let n = num_stubs (clos_to_bvl_config_max_app c) in
     let init_stubs' = toAList (clos_to_bvl_init_code
       (clos_to_bvl_config_max_app c)) in
     let init_globs = [(n - 1,0,init_globals
       (clos_to_bvl_config_max_app c) (n + clos_to_bvl_config_start c))]
       in
     let force_stub = [(n - 2,2,force_thunk_code)] in
     let comp_progs = clos_to_bvl_compile_prog
       (clos_to_bvl_config_max_app c) prog in
     let prog' = init_stubs' ++ force_stub ++ init_globs ++
       comp_progs in
     let func_names = make_name_alist (MAP FST prog') prog n
       (clos_to_bvl_config_next_loc
                        c0) (LENGTH es) in
     let c = clos_to_bvl_config_start_fupd (K (n - 1)) c in
       (c,code_sort prog',func_names))`;;
hol4_overload "compile" "clos_to_bvl_compile";;

let extract_name_def = define_cases
  [`extract_name [] = (0,[])`;
   `extract_name (x :: xs) =
      (match (some (\n. ?t. x = Op t (closLang_IntOp
        (closLang_Const (&n))) [])) with NONE -> (0,x :: xs) | SOME
        n -> (n,(if xs = [] then [x] else xs)))`];;

let extract_name_pmatch = prove
 (`extract_name xs =
     (match xs with [] -> (0,xs) | (x :: xs) ->
       (match x with
         (Op t (closLang_IntOp (closLang_Const i)) []) ->
           (if i < (&0) then (0,x :: xs) else
             (num_of_int (abs i),(if xs = [] then [x] else xs))) |
               _66 -> (0,x :: xs)))`,
  CHEAT_TAC);;

let clos_to_bvl_compile_inc_def = new_definition
  `clos_to_bvl_compile_inc' max_app (es,prog) =
     (let (n,real_es) = extract_name es in
         clos_to_bvl_compile_prog max_app
           (chain_exps n real_es ++ prog):(num#num#bvl_exp) list)`;;
hol4_overload "compile_inc" "clos_to_bvl_compile_inc'";;

let clos_to_bvl_clos_to_bvl_compile_inc_def = new_definition
  `clos_to_bvl_compile_inc c p =
     (let p = cond_mti_compile_inc (clos_to_bvl_config_do_mti c)
       (clos_to_bvl_config_max_app c) p in
     let (n,p) = ignore_table clos_number_compile_inc
       (clos_to_bvl_config_next_loc c) p in
     let c = clos_to_bvl_config_next_loc_fupd (K n) c in
     let spt = option_val_approx_spt (clos_to_bvl_config_known_conf
       c) in
     let (spt,p) = known_compile_inc (known_static_conf
       (clos_to_bvl_config_known_conf c)) spt p in
     let c = clos_to_bvl_config_known_conf_fupd (K
       (option_upd_val_spt spt (clos_to_bvl_config_known_conf c))) c in
     let (c',p) = cond_call_compile_inc (clos_to_bvl_config_do_call
       c) (FST (clos_to_bvl_config_call_state c)) p in
     let c = clos_to_bvl_config_call_state_fupd (K (c',[])) c in
     let p = clos_annotate_compile_inc p in
     let p = clos_to_bvl_compile_inc' (clos_to_bvl_config_max_app c)
       p in
       (c,p))`;;

(* and the names that this file reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
