(* ======================================================== *)
(*  bvl_to_bvi: ported from HOL4's
    compiler/backend/bvl_to_bviScript.sml
    A definition theory, with 34 definitions, 1 datatype and 17
    theorems.  Needed by 7 files of the port.  *)
(* ======================================================== *)

(*
  A compiler phase that transforms BVL programs into BVI programs. As
  part of this phase, certain primitive operations map to "stubs" code
  implemented in BVI; numeric constants are split into smaller ones to
  ease code generation later; Handle is fused with Call; and very
  large expressions are split into smaller ones (in order to protect
  the register allocator from overly large inputs).
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/bvi_inline.ml";;
needs "compiler/backend/bvi_let.ml";;
needs "compiler/backend/bvi_tailrec.ml";;
needs "compiler/backend/bvi_tmc.ml";;
needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_const.ml";;
needs "compiler/backend/bvl_handle.ml";;
needs "compiler/backend/bvl_inline.ml";;
needs "compiler/backend/closLang.ml";;
needs "compiler/backend/dataLang.ml";;
needs "lib/regexp_compiler.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

cake_hide ["num_stubs"; "pmatch"];;

let destLet_def = cake_define
  `destLet x1 =
        match x1 with
          ((Let xs b):bvl_exp) -> (xs,b)
        | _1 -> ([],Var 0)`;;

let destLet_pmatch = cake_theorem "destLet_pmatch"
  (fun () ->
    `!exp.
     destLet exp =
       (match exp with
         Let xs b -> (xs,b) | _2 -> ([],Var 0))`)
  CHEAT_TAC;;

(* HOL4 bvl_to_bviScript.sml:37: the ML values that the definitions
   below antiquote *)

let compile_int_def = cake_define
  `compile_int (i:int) =
     bvi_Op (if --((&268435457):int) <= i /\ i <=
       ((&268435457):int) then closLang_IntOp (closLang_Const i) else
       closLang_BlockOp (closLang_Build [Int i])) []`;;

let alloc_glob_count_def = cake_define
  `alloc_glob_count x1 =
        match x1 with
          [] -> (0:num)
        | (x :: y :: xs) ->
        alloc_glob_count [x] + alloc_glob_count (y :: xs)
        | [(Var _3):bvl_exp] -> 0
        | [If x y z] ->
        alloc_glob_count [x] +
        alloc_glob_count [y] +
        alloc_glob_count [z]
        | [Handle x y] ->
        alloc_glob_count [x] +
        alloc_glob_count [y]
        | [Tick x] -> alloc_glob_count [x]
        | [Force loc v] -> 0
        | [Raise x] -> alloc_glob_count [x]
        | [Let xs x] -> alloc_glob_count (x :: xs)
        | [Call _4 _5 xs] -> alloc_glob_count xs
        | [Op op xs] ->
        (if op = closLang_GlobOp closLang_AllocGlobal then 1 +
          alloc_glob_count xs else alloc_glob_count xs)
        | [_6] -> 0`;;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
let global_count_sing_def = cake_define_list_wf
  `MEASURE (\x. match x with INL e -> bvl_exp_size e | INR es ->
  list_size bvl_exp_size es)`
  [`global_count_sing ((Var _7):bvl_exp) = 0`;
   `global_count_sing (If x y z:bvl_exp) =
         global_count_sing x +
         global_count_sing y +
         global_count_sing z`;
   `global_count_sing (Handle x y:bvl_exp) =
         global_count_sing x +
         global_count_sing y`;
   `global_count_sing (Force loc v:bvl_exp) = 0`;
   `global_count_sing (Tick x:bvl_exp) = global_count_sing x`;
   `global_count_sing (Raise x:bvl_exp) = global_count_sing x`;
   `global_count_sing (Let xs x:bvl_exp) =
         global_count_sing x + global_count_list xs`;
   `global_count_sing (Call _10 _11 xs:bvl_exp) = global_count_list
  xs`;
   `global_count_sing (Op op xs:bvl_exp) =
         (if op = closLang_GlobOp closLang_AllocGlobal then 1 +
           global_count_list xs else global_count_list xs)`;
   `global_count_list [] = (0:num)`;
   `global_count_list (x :: xs) = ((
         global_count_sing x + global_count_list xs):num)`];;

let alloc_glob_count_eq_global_count_list =
  cake_theorem "alloc_glob_count_eq_global_count_list"
  (fun () ->
    `(!e. global_count_sing e = alloc_glob_count [e]) /\
     (!es. global_count_list es = alloc_glob_count es)`)
  CHEAT_TAC;;

let AllocGlobal_location_def = cake_define
  `AllocGlobal_location = data_num_stubs`;;
let CopyGlobals_location_def = cake_define
  `CopyGlobals_location = AllocGlobal_location + 1`;;
let InitGlobals_location_def = cake_define
  `InitGlobals_location = CopyGlobals_location + 1`;;
let ListLength_location_def = cake_define
  `ListLength_location = InitGlobals_location + 1`;;
let FromListByte_location_def = cake_define
  `FromListByte_location = ListLength_location + 1`;;
let ToListByte_location_def = cake_define
  `ToListByte_location = FromListByte_location + 1`;;
let SumListLength_location_def = cake_define
  `SumListLength_location = ToListByte_location + 1`;;
let ConcatByte_location_def = cake_define
  `ConcatByte_location = SumListLength_location + 1`;;

(* HOL4 bvl_to_bviScript.sml:129-130: a theorem that HOL4 states as
   the value of an ML expression: AllocGlobal_location_eq *)
(* HOL4 bvl_to_bviScript.sml:131-132: a theorem that HOL4 states as
   the value of an ML expression: CopyGlobals_location_eq *)
(* HOL4 bvl_to_bviScript.sml:133-134: a theorem that HOL4 states as
   the value of an ML expression: InitGlobals_location_eq *)
(* HOL4 bvl_to_bviScript.sml:135-136: a theorem that HOL4 states as
   the value of an ML expression: ListLength_location_eq *)
(* HOL4 bvl_to_bviScript.sml:137-138: a theorem that HOL4 states as
   the value of an ML expression: FromListByte_location_eq *)
(* HOL4 bvl_to_bviScript.sml:139-140: a theorem that HOL4 states as
   the value of an ML expression: ToListByte_location_eq *)
(* HOL4 bvl_to_bviScript.sml:141-142: a theorem that HOL4 states as
   the value of an ML expression: SumListLength_location_eq *)
(* HOL4 bvl_to_bviScript.sml:143-144: a theorem that HOL4 states as
   the value of an ML expression: ConcatByte_location_eq *)

let AllocGlobal_code_def = cake_define
  `AllocGlobal_code = ((1:num),
     Let [Op (closLang_GlobOp closLang_GlobalsPtr) []] (
     Let [Op (closLang_MemOp closLang_El) [Op (closLang_IntOp
       (closLang_Const (&0))) []; Var 0]] (
     Let [Op (closLang_IntOp closLang_Add) [Var 0; Var 2]] (
     Let [Op (closLang_MemOp closLang_Length) [Var 2]] (
     Let [Op (closLang_MemOp closLang_Update) [Var 1; Op
       (closLang_IntOp (closLang_Const (&0))) []; Var 3]]
       (If (Op (closLang_IntOp closLang_Less) [Var 1; Var 2]) (Var 0)
          (Let [Op (closLang_MemOp closLang_RefArray) [Op
            (closLang_IntOp (closLang_Const (&0))) []; Op
            (closLang_IntOp closLang_Add) [Var 2; Var 2]]] (
           Let [Op (closLang_GlobOp closLang_SetGlobalsPtr) [Var 0]]
             (Call 0 (SOME CopyGlobals_location)
               [Var 1; Var 6; Op (closLang_IntOp closLang_Sub) [Op
                 (closLang_IntOp (closLang_Const (&1))) []; Var 3]]
                 NONE)))))))))`;;

let CopyGlobals_code_def = cake_define
  `CopyGlobals_code = ((3:num),
     // ptr to new array, ptr to old array, index to copy
     Let [Op (closLang_MemOp closLang_Update) [Op (closLang_MemOp
       closLang_El) [Var 2; Var 1]; Var 2; Var 0]]
       (If (Op (closLang_BlockOp closLang_Equal) [Op (closLang_IntOp
         (closLang_Const (&0))) []; Var 3]) (Var 0)
         (Call 0 (SOME CopyGlobals_location) [Var 1; Var 2; Op
           (closLang_IntOp closLang_Sub) [Op (closLang_IntOp
           (closLang_Const (&1))) []; Var 3]] NONE)))`;;

let InitGlobals_max_def = cake_define
  `InitGlobals_max = 10000`;;

let InitGlobals_code_def = cake_define
  `InitGlobals_code start' n = ((0:num),
     (let n = MIN (MAX n 1) InitGlobals_max in
       Let [Op (closLang_MemOp closLang_RefArray) [Op (closLang_IntOp
         (closLang_Const (&0))) []; Op (closLang_IntOp (closLang_Const
         (&n))) []]]
         (Let [Op (closLang_MemOp closLang_Update) [Op
           (closLang_IntOp (closLang_Const (&1))) []; Op (closLang_IntOp
           (closLang_Const (&0))) []; Var 0]]
           (Let [Op (closLang_GlobOp closLang_SetGlobalsPtr) [Var 1]]
              (Call 0 (SOME start') [] (SOME (Var 0)))))))`;;

let ListLength_code_def = cake_define
  `ListLength_code = (2,
     // ptr to array, accumulated length
     If (Op (closLang_BlockOp (closLang_TagLenEq nil_tag 0)) [Var 0])
       (Var 1) (Call 0 (SOME ListLength_location)
                 [Op (closLang_MemOp closLang_El) [Op (closLang_IntOp
                   (closLang_Const (&1))) []; Var 0];
                  Op (closLang_IntOp closLang_Add) [Var 1; Op
                    (closLang_IntOp (closLang_Const (&1))) []]]
                    NONE))`;;

let FromListByte_code_def = cake_define
  `FromListByte_code = (3,
     // list, current index, byte array
     If (Op (closLang_BlockOp (closLang_TagLenEq nil_tag 0)) [Var 0])
       (Var 2)
       (Let [Op (closLang_MemOp closLang_UpdateByte) [Op
         (closLang_MemOp closLang_El) [Op (closLang_IntOp
         (closLang_Const (&0))) []; Var 0]; Var 1; Var 2]]
         (Call 0 (SOME FromListByte_location)
           [Op (closLang_MemOp closLang_El) [Op (closLang_IntOp
             (closLang_Const (&1))) []; Var 1];
            Op (closLang_IntOp closLang_Add) [Var 2; Op
              (closLang_IntOp (closLang_Const (&1))) []];
            Var 3] NONE)))`;;

let ToListByte_code_def = cake_define
  `ToListByte_code = (3,
     // list, current index, byte array
     If (Op (closLang_BlockOp (closLang_EqualConst (closLang_Int
       (&0)))) [Var 1]) (Var 0)
       (Let [Op (closLang_IntOp closLang_Sub) [Op (closLang_IntOp
         (closLang_Const (&1))) []; Var 1]]
       (Let [Op (closLang_MemOp closLang_DerefByte) [Var 0; Var 3]]
         (Call 0 (SOME ToListByte_location)
           [Op (closLang_BlockOp (closLang_Cons 0)) [Var 2; Var 0];
            Var 1;
            Var 4] NONE))))`;;

let SumListLength_code_def = cake_define
  `SumListLength_code = (2,
     // ptr to list, accumulated length
     If (Op (closLang_BlockOp (closLang_TagLenEq nil_tag 0)) [Var 0])
       (Var 1)
       (Call 0 (SOME SumListLength_location)
          [Op (closLang_MemOp closLang_El) [Op (closLang_IntOp
            (closLang_Const (&1))) []; Var 0];
           Op (closLang_IntOp closLang_Add) [Var 1; Op
             (closLang_MemOp closLang_LengthByte)
                            [Op (closLang_MemOp closLang_El) [Op
                              (closLang_IntOp (closLang_Const (&0)))
                              []; Var 0]]]] NONE))`;;

let ConcatByte_code_def = cake_define
  `ConcatByte_code = (3,
     // list, current index, destination
     If (Op (closLang_BlockOp (closLang_TagLenEq nil_tag 0)) [Var 0])
       (Var 2)
       (Let [Op (closLang_MemOp closLang_El) [Op (closLang_IntOp
         (closLang_Const (&0))) []; Var 0]]
         (Let [Op (closLang_MemOp closLang_LengthByte) [Var 0]]
           (Let [Op (closLang_MemOp (closLang_CopyByte F))
                   [Var 3; Var 4; Var 0; Op (closLang_IntOp
                     (closLang_Const (&0))) []; Var 1]]
             (Call 0 (SOME ConcatByte_location)
               [Op (closLang_MemOp closLang_El) [Op (closLang_IntOp
                 (closLang_Const (&1))) []; Var 3];
                Op (closLang_IntOp closLang_Add) [Var 4; Var 1];
                Var 5] NONE)))))`;;

let stubs_def = cake_define
  `bvl_to_bvi_stubs start' n = [(AllocGlobal_location,AllocGlobal_code);
                    (CopyGlobals_location,CopyGlobals_code);
                    (InitGlobals_location,InitGlobals_code start' n);
                    (ListLength_location,ListLength_code);
                    (FromListByte_location,FromListByte_code);
                    (ToListByte_location,ToListByte_code);
                    (SumListLength_location,SumListLength_code);
                    (ConcatByte_location,ConcatByte_code)]`;;
hol4_overload "stubs" "bvl_to_bvi_stubs";;

(* HOL4 bvl_to_bviScript.sml:243: the overload num_stubs, which the
   port expands *)

let compile_op_def = cake_define
  `bvl_to_bvi_compile_op op c1 =
     (match op with closLang_IntOp (closLang_Const i) ->
       (match c1 with [] -> compile_int i | _12 -> Let [Op
         (closLang_IntOp (closLang_Const (&0))) c1] (compile_int i)) |
         closLang_GlobOp (closLang_Global n) ->
       (if NULL c1 then Op (closLang_GlobOp (closLang_Global (n +
         1))) [] else Let c1 (Op (closLang_MemOp closLang_El) [
         Op (closLang_IntOp closLang_Add) [Op (closLang_IntOp
           (closLang_Const (&2))) []; Var 0];
         Op (closLang_GlobOp closLang_GlobalsPtr) []])) |
           closLang_GlobOp (closLang_SetGlobal n) -> Op (closLang_GlobOp
           (closLang_SetGlobal (n + 1))) c1 | closLang_GlobOp
           closLang_AllocGlobal -> Call 0 (SOME AllocGlobal_location) c1
           NONE | closLang_BlockOp (closLang_FromList n) -> Let
         (if NULL c1 then [Op (closLang_IntOp (closLang_Const (&0)))
           []] else c1)
         (Op (closLang_BlockOp (closLang_FromList n))
         [Var 0; Call 0 (SOME ListLength_location) [Var 0; Op
           (closLang_IntOp (closLang_Const (&0))) []] NONE]) |
           closLang_Install -> Let
       (if ~(LENGTH c1 = 2) then [Let c1 (Op (closLang_IntOp
         (closLang_Const (&0))) []); Op (closLang_IntOp (closLang_Const
         (&0))) []] else c1)
       (Op closLang_Install
        [Call 0 (SOME ListLength_location)
           [Var 0; Op (closLang_IntOp (closLang_Const (&0))) []]
             NONE;
         Call 0 (SOME ListLength_location)
           [Var 1; Op (closLang_IntOp (closLang_Const (&0))) []]
             NONE;
         Var 0; Var 1]) | closLang_MemOp closLang_FromListByte ->
         Let (if NULL c1 then [Op (closLang_IntOp (closLang_Const
           (&0))) []] else c1)
           (Call 0 (SOME FromListByte_location)
              [Var 0;
               Op (closLang_IntOp (closLang_Const (&0))) [];
               Op (closLang_MemOp (closLang_RefByte T))
                 [Op (closLang_IntOp (closLang_Const (&0))) [];
                  Call 0 (SOME ListLength_location)
                    [Var 0; Op (closLang_IntOp (closLang_Const (&0)))
                      []] NONE]]
              NONE) | closLang_MemOp closLang_ToListByte ->
         Let (if NULL c1 then [Op (closLang_IntOp (closLang_Const
           (&0))) []] else c1)
           (Call 0 (SOME ToListByte_location)
              [Op (closLang_BlockOp (closLang_Cons 0)) [];
               Op (closLang_MemOp closLang_LengthByte) [Var 0];
               Var 0]
              NONE) | closLang_MemOp closLang_ConcatByteVec ->
         Let (if NULL c1 then [Op (closLang_IntOp (closLang_Const
           (&0))) []] else c1)
           (Call 0 (SOME ConcatByte_location)
             [Var 0;
              Op (closLang_IntOp (closLang_Const (&0))) [];
              Op (closLang_MemOp (closLang_RefByte T))
                [Op (closLang_IntOp (closLang_Const (&0))) [];
                 Call 0 (SOME SumListLength_location)
                   [Var 0; Op (closLang_IntOp (closLang_Const (&0)))
                     []] NONE]] NONE) | closLang_MemOp
                     (closLang_CopyByte T) ->
       // TODO: this should eventually be implemented in data_to_word instead for efficiency
       Let (if LENGTH c1 < 3 then (c1 ++ REPLICATE 3 (Op
         (closLang_IntOp (closLang_Const (&0))) [])) else c1)
         (Let [Op (closLang_MemOp (closLang_RefByte T)) [Op
           (closLang_IntOp (closLang_Const (&0))) []; Var 0]]
            (Let [Op (closLang_MemOp (closLang_CopyByte F)) [Op
              (closLang_IntOp (closLang_Const (&0))) []; Var 0; Var 1;
              Var 2; Var 3]]
              (Var 1))) | closLang_Label l -> Op (closLang_Label
                (bvl_num_stubs + bvl_to_bvi_namespaces * l)) c1 |
                closLang_BlockOp (closLang_Build ps) -> Op
                (closLang_BlockOp (closLang_Build ps)) c1 |
                closLang_BlockOp (closLang_EqualConst p) -> Op
                (closLang_BlockOp (closLang_EqualConst p)) c1 |
       // reserved for bvi_tmc; bvlSem$do_app is Error on these, so compile them out
       closLang_MemOp (closLang_MutCons tag i) -> Let c1 (Op
         (closLang_IntOp (closLang_Const (&0))) []) | closLang_MemOp
         closLang_UpdateCons -> Let c1 (Op (closLang_IntOp
         (closLang_Const (&0))) []) | closLang_MemOp
         closLang_FinaliseCons -> Let c1 (Op (closLang_IntOp
         (closLang_Const (&0))) []) | _13 -> Op op c1)`;;
hol4_overload "compile_op" "bvl_to_bvi_compile_op";;

(* HOL4 bvl_to_bviScript.sml:313-321: a theorem that HOL4 states as
   the value of an ML expression: compile_op_pmatch *)

hol4_overload "++" "SmartAppend";;
(* HOL4 bvl_to_bviScript.sml:324: the overload nss, which the port
   expands *)

let compile_aux_def = cake_define
  `compile_aux (k,args,p) =
     List [(bvl_num_stubs + bvl_to_bvi_namespaces * k +
       1,args,bvi_let_compile_exp p)]`;;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let compile_exps_def = cake_define_try_tac (fun () ->
  `MEASURE (list_size bvl_exp_size o SND)`)
  CHEAT_TAC
  `(bvl_to_bvi_compile_exps n [] = ([],misc_Nil,n)) /\
   (bvl_to_bvi_compile_exps n ((x:bvl_exp) :: y :: xs) =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x] in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 (y :: xs) in
        (c1 ++ c2,aux1 ++ aux2,n2))) /\
   (bvl_to_bvi_compile_exps n [Var v] = ([(Var
     v):bvi_exp],misc_Nil,n)) /\
   (bvl_to_bvi_compile_exps n [If x1 x2 x3] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x1] in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x2] in
      let (c3,aux3,n3) = bvl_to_bvi_compile_exps n2 [x3] in
        ([If (HD c1) (HD c2) (HD c3)],aux1 ++ aux2 ++ aux3,n3))) /\
   (bvl_to_bvi_compile_exps n [Let xs x2] =
      (if NULL xs then
        // i.e. a marker
        let (args,x0) = destLet x2 in
        let (c1,aux1,n1) = bvl_to_bvi_compile_exps n args in
        let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x0] in
        let n3 = n2 + 1 in
          ([Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n2
            + 1)) c1 NONE],
           aux1 ++ aux2 ++ compile_aux (n2,LENGTH args,HD c2),n3)
             else
        let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x2] in
          ([Let c1 (HD c2)],aux1 ++ aux2,n2))) /\
   (bvl_to_bvi_compile_exps n [Raise x1] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x1] in
        ([Raise (HD c1)],aux1,n1))) /\
   (bvl_to_bvi_compile_exps n [Tick x1] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x1] in
        ([Tick (HD c1)],aux1,n1))) /\
   (bvl_to_bvi_compile_exps n [Force loc v] =
      ([Force (bvl_num_stubs + bvl_to_bvi_namespaces * loc)
        v],misc_Nil,n)) /\
   (bvl_to_bvi_compile_exps n [Op op xs] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        ([bvl_to_bvi_compile_op op c1],aux1,n1))) /\
   (bvl_to_bvi_compile_exps n [Handle x1 x2] =
      (let (args,x0) = destLet x1 in
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n args in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x0] in
      let (c3,aux3,n3) = bvl_to_bvi_compile_exps n2 [x2] in
      let aux4 = compile_aux (n3,LENGTH args,HD c2) in
      let n4 = n3 + 1 in
        ([Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n3 +
          1)) c1 (SOME (HD c3))],
         aux1 ++ aux2 ++ aux3 ++ aux4,n4))) /\
   (bvl_to_bvi_compile_exps n [Call ticks dest xs] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        ([Call ticks
               (match dest with NONE -> NONE | SOME n -> SOME
                 (bvl_num_stubs + bvl_to_bvi_namespaces * n)) c1
                 NONE],aux1,n1)))`;;
hol4_overload "compile_exps" "bvl_to_bvi_compile_exps";;

let _ = size_thms "bvl_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let compile_exps_sing_def = cake_define_try_tac (fun () ->
  `MEASURE (\x. match x with INL (n,e) -> bvl_exp_size e | INR (n,es)
  -> list_size bvl_exp_size es)`)
  CHEAT_TAC
  `(compile_exps_sing n (Var v:bvl_exp) = (((Var
  v):bvi_exp),misc_Nil,n)) /\
   (compile_exps_sing n (If x1 x2 x3) =
      (let (c1,aux1,n1) = compile_exps_sing n x1 in
      let (c2,aux2,n2) = compile_exps_sing n1 x2 in
      let (c3,aux3,n3) = compile_exps_sing n2 x3 in
        (If c1 c2 c3,aux1 ++ aux2 ++ aux3,n3))) /\
   (compile_exps_sing n (Let xs x2) =
      (if NULL xs then
        // i.e. a marker
        let (args,x0) = destLet x2 in
        let (c1,aux1,n1) = compile_exps_list n args in
        let (c2,aux2,n2) = compile_exps_sing n1 x0 in
        let n3 = n2 + 1 in
          ((Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n2
            + 1)) c1 NONE),
           aux1 ++ aux2 ++ compile_aux (n2,LENGTH args,c2),n3) else
        let (c1,aux1,n1) = compile_exps_list n xs in
        let (c2,aux2,n2) = compile_exps_sing n1 x2 in
          ((Let c1 (c2)),aux1 ++ aux2,n2))) /\
   (compile_exps_sing n (Raise x1) =
      (let (c1,aux1,n1) = compile_exps_sing n x1 in
        (Raise c1,aux1,n1))) /\
   (compile_exps_sing n (Tick x1) =
      (let (c1,aux1,n1) = compile_exps_sing n x1 in
        (Tick c1,aux1,n1))) /\
   (compile_exps_sing n (Force loc v) =
      (Force (bvl_num_stubs + bvl_to_bvi_namespaces * loc)
        v,misc_Nil,n)) /\
   (compile_exps_sing n (Op op xs) =
      (let (c1,aux1,n1) = compile_exps_list n xs in
        (bvl_to_bvi_compile_op op c1,aux1,n1))) /\
   (compile_exps_sing n (Handle x1 x2) =
      (let (args,x0) = destLet x1 in
      let (c1,aux1,n1) = compile_exps_list n args in
      let (c2,aux2,n2) = compile_exps_sing n1 x0 in
      let (c3,aux3,n3) = compile_exps_sing n2 x2 in
      let aux4 = compile_aux (n3,LENGTH args,c2) in
      let n4 = n3 + 1 in
        ((Call 0 (SOME (bvl_num_stubs + bvl_to_bvi_namespaces * n3 +
          1)) c1 (SOME c3)),
         aux1 ++ aux2 ++ aux3 ++ aux4,n4))) /\
   (compile_exps_sing n (Call ticks dest xs) =
      (let (c1,aux1,n1) = compile_exps_list n xs in
        ((Call ticks
               (match dest with NONE -> NONE | SOME n -> SOME
                 (bvl_num_stubs + bvl_to_bvi_namespaces * n)) c1
                 NONE),aux1,n1))) /\
   (compile_exps_list n [] = ([],misc_Nil,n)) /\
   (compile_exps_list n ((x:bvl_exp) :: xs) =
      (let (c1,aux1,n1) = compile_exps_sing n x in
      let (c2,aux2,n2) = compile_exps_list n1 xs in
        (c1 :: c2,aux1 ++ aux2,n2)))`;;

let compile_exps_sing = cake_theorem "compile_exps_sing"
  (fun () ->
    `(!n e. bvl_to_bvi_compile_exps n [e] =
            (let (x,y,z) = compile_exps_sing n e in ([x],y,z))) /\
     (!n es. compile_exps_list n es = bvl_to_bvi_compile_exps n
       es)`)
  CHEAT_TAC;;

let compile_exps_LENGTH_lemma =
  cake_theorem "compile_exps_LENGTH_lemma[local]"
  (fun () ->
    `!n xs. (LENGTH (FST (bvl_to_bvi_compile_exps n xs)) = LENGTH xs)`)
  CHEAT_TAC;;

let compile_exps_LENGTH = cake_theorem "compile_exps_LENGTH"
  (fun () ->
    `(bvl_to_bvi_compile_exps n xs = (ys,aux,n1)) ==> (LENGTH ys =
  LENGTH xs)`)
  CHEAT_TAC;;

let compile_exps_SING = cake_theorem "compile_exps_SING"
  (fun () ->
    `(bvl_to_bvi_compile_exps n [x] = (c,aux,n1)) ==> (?y. c = [y])`)
  CHEAT_TAC;;

let compile_single_def = cake_define
  `bvl_to_bvi_compile_single n (name,arg_count,exp) =
     (let (c,aux,n1) = bvl_to_bvi_compile_exps n [exp] in
       (
         List [(bvl_num_stubs + bvl_to_bvi_namespaces *
           name,arg_count,bvi_let_compile_exp (HD c))] ++ aux,n1))`;;
hol4_overload "compile_single" "bvl_to_bvi_compile_single";;

let compile_single_eq = cake_theorem "compile_single_eq"
  (fun () ->
    `bvl_to_bvi_compile_single n (name,arg_count,exp) =
       (let (c,aux,n1) = compile_exps_sing n exp in
         (
           List [(bvl_num_stubs + bvl_to_bvi_namespaces *
             name,arg_count,bvi_let_compile_exp c)] ++ aux,n1))`)
  CHEAT_TAC;;

let compile_list_def = cake_define_list
  [`bvl_to_bvi_compile_list n [] = (List [],n)`;
   `bvl_to_bvi_compile_list n (p :: progs) =
         (let (code1,n1) = bvl_to_bvi_compile_single n p in
         let (code2,n2) = bvl_to_bvi_compile_list n1 progs in
           (code1 ++ code2,n2))`];;
hol4_overload "compile_list" "bvl_to_bvi_compile_list";;

let compile_inc_def = cake_define
  `// incremental version used by Install
   bvl_to_bvi_compile_inc n prog =
     (let (p1,n1) = bvl_to_bvi_compile_list n prog in
       (n1,append p1))`;;
hol4_overload "compile_inc" "bvl_to_bvi_compile_inc";;

let compile_prog_def = cake_define
  `bvl_to_bvi_compile_prog start' n prog =
     (let k = alloc_glob_count (MAP (\(_14,_15,p). p) prog) in
     let (code,n1) = compile_list n prog in
       (InitGlobals_location,bvl_to_bvi_stubs (bvl_num_stubs +
         bvl_to_bvi_namespaces * start') k ++ append code,n1))`;;
hol4_overload "compile_prog" "bvl_to_bvi_compile_prog";;

(* HOL4 bvl_to_bviScript.sml:520-521: a theorem that HOL4 states as
   the value of an ML expression: compile_prog_eq *)

let bvl_to_bvi_config_FIELDS = define_record "bvl_to_bvi_config"
  ["inline_size_limit","num";
   (* zero disables inlining *)
   "exp_cut","num";
   (* huge number effectively disables exp splitting *)
   "split_main_at_seq","bool";
   (* split main expression at Seqs *)
   "next_name1","num";
   (* there should be as many of *)
   "next_name2","num";
   (* these as bvl_to_bvi_namespaces-1 *)
   "next_name3","num";
   "do_tailrec","bool";
   "do_tmc","bool";
   "inlines","(num#bvl_exp) spt";
   "bvi_inlines","(num#bvi_exp) spt"];;

let default_config_def = cake_define
  `bvl_to_bvi_default_config =
     mk_bvl_to_bvi_config 10 1000 T (bvl_num_stubs + 1)
       (bvl_num_stubs + 2) (bvl_num_stubs + 3) T T LN LN`;;
hol4_overload "default_config" "bvl_to_bvi_default_config";;

let get_names_def = cake_define
  `bvl_to_bvi_get_names final_nums old_names =
     fromAList (MAP (\n. (n,
       (if n = InitGlobals_location then implode "start" else
       if n = AllocGlobal_location then implode "AllocGlobal" else
       if n = CopyGlobals_location then implode "CopyGlobals" else
       if n = ListLength_location then implode "ListLength" else
       if n = FromListByte_location then implode "FromListByte" else
       if n = ToListByte_location then implode "ToListByte" else
       if n = SumListLength_location then implode "SumListLength"
         else
       if n = ConcatByte_location then implode "ConcatByte" else
       if n < bvl_num_stubs then implode "bvi_unknown" else
         let k = n - bvl_num_stubs in
         let kd = k DIV bvl_to_bvi_namespaces in
         let km = k MOD bvl_to_bvi_namespaces in
         let n = (match sptree_lookup kd old_names with NONE ->
           implode "bvi_unmapped" | SOME name -> name) in
         let aux = (if km = 0 then implode "" else implode
           "_bvi_aux") in (\x y. strcat x y) n aux))) final_nums)`;;
hol4_overload "get_names" "bvl_to_bvi_get_names";;

let compile_def = cake_define
  `bvl_to_bvi_compile start' c names prog =
     (let (inlines,prog) = bvl_inline_compile_prog
       (bvl_to_bvi_config_inline_size_limit c)
       (bvl_to_bvi_config_split_main_at_seq
            c) (bvl_to_bvi_config_exp_cut c) prog in
     let (loc,code,n1) = compile_prog start' 0 prog in
     let (n2,code') = bvi_tailrec_compile_prog
       (bvl_to_bvi_config_do_tailrec c) (bvl_num_stubs + 2) code in
     let (n3,code') = bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
       c) (bvl_num_stubs + 3) code' in
     let (bvi_inlines,code') = bvi_inline_compile_prog code' in
       (loc,code',inlines,bvi_inlines,n1,n2,n3,
        bvl_to_bvi_get_names (MAP FST code') names))`;;
hol4_overload "compile" "bvl_to_bvi_compile";;

let bvl_to_bvi_compile_inc_all_def = cake_define
  `bvl_to_bvi_compile_inc_all c p =
     (let (inl,p) = bvl_inline_compile_inc
       (bvl_to_bvi_config_inline_size_limit c)
       (bvl_to_bvi_config_split_main_at_seq
         c) (bvl_to_bvi_config_exp_cut c) (bvl_to_bvi_config_inlines
           c) p in
     let c = bvl_to_bvi_config_inlines_fupd (K inl) c in
     let (nn1,p) = bvl_to_bvi_compile_inc
       (bvl_to_bvi_config_next_name1 c) p in
     let c = bvl_to_bvi_config_next_name1_fupd (K nn1) c in
     let (nn2,p) = bvi_tailrec_compile_prog
       (bvl_to_bvi_config_do_tailrec c) (bvl_to_bvi_config_next_name2 c)
       p in
     let c = bvl_to_bvi_config_next_name2_fupd (K nn2) c in
     let (nn3,p) = bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc c)
       (bvl_to_bvi_config_next_name3 c) p in
     let c = bvl_to_bvi_config_next_name3_fupd (K nn3) c in
     let (bvi_inlines,p) = bvi_inline_compile_inc
       (bvl_to_bvi_config_bvi_inlines c) p in
     let c = bvl_to_bvi_config_bvi_inlines_fupd (K bvi_inlines) c in
       (c,p))`;;

hol4_only "++" "APPEND";;

cake_hide [];;
