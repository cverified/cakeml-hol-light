(* ======================================================== *)
(*  bvl_to_bvi: ported from HOL4's
    compiler/backend/bvl_to_bviScript.sml  *)
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
needs "lib/comparison.ml";;
needs "lib/sptree.ml";;
needs "misc/misc.ml";;
needs "semantics/ast.ml";;

let destLet_def = cake_define
  `destLet x1 =
        match x1 with
          ((Let xs b):bvl_exp) -> (xs,b)
        | _1 -> ([],Var 0)`;;

(* HOL4 ML code, not ported:
val large_int = ``268435457:int``; (* 2**28-1 *)
*)

let compile_int_def = cake_define
  `compile_int (i:int) =
     bvi_Op (if --large_int <= i /\ i <= large_int then IntOp
       (Const i) else BlockOp (Build [Int i])) []`;;

let alloc_glob_count_def = cake_define
  `alloc_glob_count x1 =
        match x1 with
          [] -> (0:num)
        | (x :: y :: xs) ->
        alloc_glob_count [x] + alloc_glob_count (y :: xs)
        | [(Var _2):bvl_exp] -> 0
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
        | [Call _3 _4 xs] -> alloc_glob_count xs
        | [Op op xs] ->
        (if op = GlobOp AllocGlobal then 1 + alloc_glob_count xs else
          alloc_glob_count xs)
        | [_5] -> 0`;;

let _ = size_thms "exp";;
let _ = size_thms "exp1";;
(* HOL4 termination: \\ rpt strip_tac \\ simp
   [bvlTheory.exp_size_def] *)
let global_count_sing_def = cake_define_wf
  `MEASURE (\x. match x with INL e -> exp_size e | INR es -> exp1_size
  es)`
  `(global_count_sing ((Var _6):bvl_exp) = 0) /\
   (global_count_sing (If x y z) =
      global_count_sing x +
      global_count_sing y +
      global_count_sing z) /\
   (global_count_sing (Handle x y) =
      global_count_sing x +
      global_count_sing y) /\
   (global_count_sing (Force loc v) = 0) /\
   (global_count_sing (Tick x) = global_count_sing x) /\
   (global_count_sing (Raise x) = global_count_sing x) /\
   (global_count_sing (Let xs x) =
      global_count_sing x + global_count_list xs) /\
   (global_count_sing (Call _7 _8 xs) = global_count_list xs) /\
   (global_count_sing (Op op xs) =
      (if op = GlobOp AllocGlobal then 1 + global_count_list xs else
        global_count_list xs)) /\
   (global_count_list [] = (0:num)) /\
   (global_count_list (x :: xs) =
      global_count_sing x + global_count_list xs)`;;

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

let AllocGlobal_code_def = cake_define
  `AllocGlobal_code = ((1:num),
     Let [Op (GlobOp GlobalsPtr) []] (
     Let [Op (MemOp El) [Op (IntOp (Const (&0))) []; Var 0]] (
     Let [Op (IntOp Add) [Var 0; Var 2]] (
     Let [Op (MemOp Length) [Var 2]] (
     Let [Op (MemOp Update) [Var 1; Op (IntOp (Const (&0))) []; Var
       3]]
       (If (Op (IntOp Less) [Var 1; Var 2]) (Var 0)
          (Let [Op (MemOp RefArray) [Op (IntOp (Const (&0))) []; Op
            (IntOp Add) [Var 2; Var 2]]] (
           Let [Op (GlobOp SetGlobalsPtr) [Var 0]]
             (Call 0 (SOME CopyGlobals_location)
               [Var 1; Var 6; Op (IntOp Sub) [Op (IntOp (Const
                 (&1))) []; Var 3]] NONE)))))))))`;;

let CopyGlobals_code_def = cake_define
  `CopyGlobals_code = ((3:num),
     Let [Op (MemOp Update) [Op (MemOp El) [Var 2; Var 1]; Var 2; Var
       0]]
       (If (Op (BlockOp Equal) [Op (IntOp (Const (&0))) []; Var 3])
         (Var 0)
         (Call 0 (SOME CopyGlobals_location) [Var 1; Var 2; Op
           (IntOp Sub) [Op (IntOp (Const (&1))) []; Var 3]] NONE)))`;;

let InitGlobals_max_def = cake_define
  `InitGlobals_max = 10000`;;

let InitGlobals_code_def = cake_define
  `InitGlobals_code start n = ((0:num),
     (let n = MIN (MAX n 1) InitGlobals_max in
       Let [Op (MemOp RefArray) [Op (IntOp (Const (&0))) []; Op
         (IntOp (Const (&n))) []]]
         (Let [Op (MemOp Update) [Op (IntOp (Const (&1))) []; Op
           (IntOp (Const (&0))) []; Var 0]]
           (Let [Op (GlobOp SetGlobalsPtr) [Var 1]]
              (Call 0 (SOME start) [] (SOME (Var 0)))))))`;;

let ListLength_code_def = cake_define
  `ListLength_code = (2,
     If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0])
       (Var 1) (Call 0 (SOME ListLength_location)
                 [Op (MemOp El) [Op (IntOp (Const (&1))) []; Var 0];
                  Op (IntOp Add) [Var 1; Op (IntOp (Const (&1)))
                    []]] NONE))`;;

let FromListByte_code_def = cake_define
  `FromListByte_code = (3,
     If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0]) (Var 2)
       (Let [Op (MemOp UpdateByte) [Op (MemOp El) [Op (IntOp (Const
         (&0))) []; Var 0]; Var 1; Var 2]]
         (Call 0 (SOME FromListByte_location)
           [Op (MemOp El) [Op (IntOp (Const (&1))) []; Var 1];
            Op (IntOp Add) [Var 2; Op (IntOp (Const (&1))) []];
            Var 3] NONE)))`;;

let ToListByte_code_def = cake_define
  `ToListByte_code = (3,
     If (Op (BlockOp (EqualConst (Int (&0)))) [Var 1]) (Var 0)
       (Let [Op (IntOp Sub) [Op (IntOp (Const (&1))) []; Var 1]]
       (Let [Op (MemOp DerefByte) [Var 0; Var 3]]
         (Call 0 (SOME ToListByte_location)
           [Op (BlockOp (Cons 0)) [Var 2; Var 0];
            Var 1;
            Var 4] NONE))))`;;

let SumListLength_code_def = cake_define
  `SumListLength_code = (2,
     If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0])
       (Var 1)
       (Call 0 (SOME SumListLength_location)
          [Op (MemOp El) [Op (IntOp (Const (&1))) []; Var 0];
           Op (IntOp Add) [Var 1; Op (MemOp LengthByte)
                            [Op (MemOp El) [Op (IntOp (Const
                              (&0))) []; Var 0]]]] NONE))`;;

let ConcatByte_code_def = cake_define
  `ConcatByte_code = (3,
     If (Op (BlockOp (TagLenEq nil_tag 0)) [Var 0]) (Var 2)
       (Let [Op (MemOp El) [Op (IntOp (Const (&0))) []; Var 0]]
         (Let [Op (MemOp LengthByte) [Var 0]]
           (Let [Op (MemOp (CopyByte F))
                   [Var 3; Var 4; Var 0; Op (IntOp (Const (&0))) [];
                     Var 1]]
             (Call 0 (SOME ConcatByte_location)
               [Op (MemOp El) [Op (IntOp (Const (&1))) []; Var 3];
                Op (IntOp Add) [Var 4; Var 1];
                Var 5] NONE)))))`;;

let stubs_def = cake_define
  `bvl_to_bvi_stubs start n = [(AllocGlobal_location,AllocGlobal_code);
                    (CopyGlobals_location,CopyGlobals_code);
                    (InitGlobals_location,InitGlobals_code start n);
                    (ListLength_location,ListLength_code);
                    (FromListByte_location,FromListByte_code);
                    (ToListByte_location,ToListByte_code);
                    (SumListLength_location,SumListLength_code);
                    (ConcatByte_location,ConcatByte_code)]`;;
hol4_overload "stubs" "bvl_to_bvi_stubs";;

(* HOL4 overload (expanded in the port):
     num_stubs = backend_common$bvl_num_stubs *)

(* HOL4 ML code, not ported:
local val compile_op_quotation = `
  compile_op op c1 =
    case op of
    | IntOp (Const i) =>
      (case c1 of [] => compile_int i
      | _ => Let [Op (IntOp (Const 0)) c1] (compile_int i))
    | GlobOp (Global n) =>
      (if NULL c1 then Op (GlobOp (Global (n+1))) []
      else Let c1 (Op (MemOp El) [
        Op (IntOp Add) [Op (IntOp (Const 2)) []; Var 0];
        Op (GlobOp GlobalsPtr) []]))
    | GlobOp (SetGlobal n) => Op (GlobOp (SetGlobal (n+1))) c1
    | GlobOp AllocGlobal => Call 0 (SOME AllocGlobal_location) c1 NONE
    | BlockOp (FromList n) => Let
        (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
        (Op (BlockOp (FromList n))
        [Var 0; Call 0 (SOME ListLength_location) [Var 0; Op (IntOp
          (Const 0)) []] NONE])
    | Install => Let
      (if LENGTH c1 <> 2
       then [Let c1 (Op (IntOp (Const 0)) []); Op (IntOp (Const 0)) []]
         else c1)
      (Op Install
       [Call 0 (SOME ListLength_location)
          [Var 0; Op (IntOp (Const 0)) []] NONE;
        Call 0 (SOME ListLength_location)
          [Var 1; Op (IntOp (Const 0)) []] NONE;
        Var 0; Var 1])
    | MemOp FromListByte =>
        Let (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
          (Call 0 (SOME FromListByte_location)
             [Var 0;
              Op (IntOp (Const 0)) [];
              Op (MemOp (RefByte T))
                [Op (IntOp (Const 0)) [];
                 Call 0 (SOME ListLength_location)
                   [Var 0; Op (IntOp (Const 0)) []] NONE]]
             NONE)
    | MemOp ToListByte =>
        Let (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
          (Call 0 (SOME ToListByte_location)
             [Op (BlockOp (Cons 0)) [];
              Op (MemOp LengthByte) [Var 0];
              Var 0]
             NONE)
    | MemOp ConcatByteVec =>
        Let (if NULL c1 then [Op (IntOp (Const 0)) []] else c1)
          (Call 0 (SOME ConcatByte_location)
            [Var 0;
             Op (IntOp (Const 0)) [];
             Op (MemOp (RefByte T))
               [Op (IntOp (Const 0)) [];
                Call 0 (SOME SumListLength_location)
                  [Var 0; Op (IntOp (Const 0)) []] NONE]] NONE)
    | MemOp (CopyByte T) => (* TODO: this should eventually be
      implemented in data_to_word instead for efficiency *)
      Let (if LENGTH c1 < 3 then (c1 ++ REPLICATE 3 (Op (IntOp (Const
        0)) [])) else c1)
        (Let [Op (MemOp (RefByte T)) [Op (IntOp (Const 0)) []; Var 0]]
           (Let [Op (MemOp (CopyByte F)) [Op (IntOp (Const 0)) []; Var
             0; Var 1; Var 2; Var 3]]
             (Var 1)))
    | Label l => Op (Label (bvl_num_stubs + bvl_to_bvi_namespaces * l))
      c1
    | BlockOp (Build ps) => Op (BlockOp (Build ps)) c1
    | BlockOp (EqualConst p) => Op (BlockOp (EqualConst p)) c1
*)
    (* reserved for bvi_tmc; bvlSem$do_app is Error on these, so compile
       them out *)
(* HOL4 ML code, not ported:
    | MemOp (MutCons tag i) => Let c1 (Op (IntOp (Const 0)) [])
    | MemOp UpdateCons => Let c1 (Op (IntOp (Const 0)) [])
    | MemOp FinaliseCons => Let c1 (Op (IntOp (Const 0)) [])
    | _ => Op op c1`
in
val compile_op_def = Define compile_op_quotation;
*)

(* HOL4 overload (expanded in the port):
     None =  *)
(* HOL4 overload (expanded in the port):
     None =  *)

let compile_aux_def = cake_define
  `compile_aux (k,args,p) =
     List [((bvl_num_stubs) + nss * k + 1,args,bvi_let_compile_exp
       p)]`;;

let _ = size_thms "exp1";;
(* HOL4 termination: \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC \\ TRY
   (Cases_on `x1`) \\ fs [destLet_def] \\ TRY (Cases_on `x2`) \\ fs
   [destLet_def] \\ SRW_TAC [] [bvlTheory.exp_size_def] \\ DECIDE_TAC *)
let compile_exps_def = cake_define_wf
  `MEASURE (exp1_size o SND)`
  `(bvl_to_bvi_compile_exps n [] = ([],Nil,n)) /\
   (bvl_to_bvi_compile_exps n ((x:bvl_exp) :: y :: xs) =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x] in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 (y :: xs) in
        (c1 ++ c2,aux1 ++ aux2,n2))) /\
   (bvl_to_bvi_compile_exps n [Var v] = ([(Var v):bvi_exp],Nil,n)) /\
   (bvl_to_bvi_compile_exps n [If x1 x2 x3] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n [x1] in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x2] in
      let (c3,aux3,n3) = bvl_to_bvi_compile_exps n2 [x3] in
        ([If (HD c1) (HD c2) (HD c3)],aux1 ++ aux2 ++ aux3,n3))) /\
   (bvl_to_bvi_compile_exps n [Let xs x2] =
      (if NULL xs then
        let (args,x0) = destLet x2 in
        let (c1,aux1,n1) = bvl_to_bvi_compile_exps n args in
        let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x0] in
        let n3 = n2 + 1 in
          ([Call 0 (SOME ((bvl_num_stubs) + nss * n2 + 1)) c1 NONE],
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
      ([Force ((bvl_num_stubs) + nss * loc) v],Nil,n)) /\
   (bvl_to_bvi_compile_exps n [Op op xs] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        ([compile_op op c1],aux1,n1))) /\
   (bvl_to_bvi_compile_exps n [Handle x1 x2] =
      (let (args,x0) = destLet x1 in
      let (c1,aux1,n1) = bvl_to_bvi_compile_exps n args in
      let (c2,aux2,n2) = bvl_to_bvi_compile_exps n1 [x0] in
      let (c3,aux3,n3) = bvl_to_bvi_compile_exps n2 [x2] in
      let aux4 = compile_aux (n3,LENGTH args,HD c2) in
      let n4 = n3 + 1 in
        ([Call 0 (SOME ((bvl_num_stubs) + nss * n3 + 1)) c1 (SOME (HD
          c3))],
         aux1 ++ aux2 ++ aux3 ++ aux4,n4))) /\
   (bvl_to_bvi_compile_exps n [Call ticks dest xs] =
      (let (c1,aux1,n1) = bvl_to_bvi_compile_exps n xs in
        ([Call ticks
               (match dest with NONE -> NONE | SOME n -> SOME
                 ((bvl_num_stubs) + nss * n)) c1 NONE],aux1,n1)))`;;
hol4_overload "compile_exps" "bvl_to_bvi_compile_exps";;

let _ = size_thms "exp";;
let _ = size_thms "exp1";;
(* HOL4 termination: \\ rpt strip_tac \\ rpt $ qpat_x_assum ‘(_,_,_)
   = _’ kall_tac \\ gvs [bvlTheory.exp_size_def] \\ gvs [oneline
   destLet_def, AllCaseEqs(), bvlTheory.exp_size_def] *)
let compile_exps_sing_def = cake_define_wf
  `MEASURE (\x. match x with INL (n,e) -> exp_size e | INR (n,es) ->
  exp1_size es)`
  `(compile_exps_sing n (Var v) = (((Var v):bvi_exp),Nil,n)) /\
   (compile_exps_sing n (If x1 x2 x3) =
      (let (c1,aux1,n1) = compile_exps_sing n x1 in
      let (c2,aux2,n2) = compile_exps_sing n1 x2 in
      let (c3,aux3,n3) = compile_exps_sing n2 x3 in
        (If c1 c2 c3,aux1 ++ aux2 ++ aux3,n3))) /\
   (compile_exps_sing n (Let xs x2) =
      (if NULL xs then
        let (args,x0) = destLet x2 in
        let (c1,aux1,n1) = compile_exps_list n args in
        let (c2,aux2,n2) = compile_exps_sing n1 x0 in
        let n3 = n2 + 1 in
          ((Call 0 (SOME ((bvl_num_stubs) + nss * n2 + 1)) c1 NONE),
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
      (Force ((bvl_num_stubs) + nss * loc) v,Nil,n)) /\
   (compile_exps_sing n (Op op xs) =
      (let (c1,aux1,n1) = compile_exps_list n xs in
        (compile_op op c1,aux1,n1))) /\
   (compile_exps_sing n (Handle x1 x2) =
      (let (args,x0) = destLet x1 in
      let (c1,aux1,n1) = compile_exps_list n args in
      let (c2,aux2,n2) = compile_exps_sing n1 x0 in
      let (c3,aux3,n3) = compile_exps_sing n2 x2 in
      let aux4 = compile_aux (n3,LENGTH args,c2) in
      let n4 = n3 + 1 in
        ((Call 0 (SOME ((bvl_num_stubs) + nss * n3 + 1)) c1 (SOME
          c3)),
         aux1 ++ aux2 ++ aux3 ++ aux4,n4))) /\
   (compile_exps_sing n (Call ticks dest xs) =
      (let (c1,aux1,n1) = compile_exps_list n xs in
        ((Call ticks
               (match dest with NONE -> NONE | SOME n -> SOME
                 ((bvl_num_stubs) + nss * n)) c1 NONE),aux1,n1))) /\
   (compile_exps_list n [] = ([],Nil,n)) /\
   (compile_exps_list n ((x:bvl_exp) :: xs) =
      (let (c1,aux1,n1) = compile_exps_sing n x in
      let (c2,aux2,n2) = compile_exps_list n1 xs in
        (c1 :: c2,aux1 ++ aux2,n2)))`;;

let compile_single_def = cake_define
  `bvl_to_bvi_compile_single n (name,arg_count,exp) =
     (let (c,aux,n1) = compile_exps n [exp] in
       (
         List [((bvl_num_stubs) + nss *
           name,arg_count,bvi_let_compile_exp (HD c))] ++ aux,n1))`;;
hol4_overload "compile_single" "bvl_to_bvi_compile_single";;

let compile_list_def = cake_define
  `(bvl_to_bvi_compile_list n [] = (List [],n)) /\
   (bvl_to_bvi_compile_list n (p :: progs) =
      (let (code1,n1) = compile_single n p in
      let (code2,n2) = bvl_to_bvi_compile_list n1 progs in
        (code1 ++ code2,n2)))`;;
hol4_overload "compile_list" "bvl_to_bvi_compile_list";;

let compile_inc_def = cake_define
  `bvl_to_bvi_compile_inc n prog =
     (let (p1,n1) = bvl_to_bvi_compile_list n prog in
       (n1,append p1))`;;
hol4_overload "compile_inc" "bvl_to_bvi_compile_inc";;

let compile_prog_def = cake_define
  `bvl_to_bvi_compile_prog start n prog =
     (let k = alloc_glob_count (MAP (\(_9,_10,p). p) prog) in
     let (code,n1) = compile_list n prog in
       (InitGlobals_location,bvl_to_bvi_stubs ((bvl_num_stubs) +
         nss * start) k ++ append code,n1))`;;
hol4_overload "compile_prog" "bvl_to_bvi_compile_prog";;

let bvl_to_bvi_config_FIELDS = define_record "bvl_to_bvi_config"
  ["inline_size_limit","num";
   "exp_cut","num";
   "split_main_at_seq","bool";
   "next_name1","num";
   "next_name2","num";
   "next_name3","num";
   "do_tailrec","bool";
   "do_tmc","bool";
   "inlines","(num#bvl_exp) spt";
   "bvi_inlines","(num#bvi_exp) spt"];;

let default_config_def = cake_define
  `bvl_to_bvi_default_config =
     mk_bvl_to_bvi_config 10 1000 T ((bvl_num_stubs) + 1)
       ((bvl_num_stubs) + 2) ((bvl_num_stubs) + 3) T T LN LN`;;
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
       if n < (bvl_num_stubs) then implode "bvi_unknown" else
         let k = n - (bvl_num_stubs) in
         let kd = k DIV nss in
         let km = k MOD nss in
         let n = (match lookup kd old_names with NONE -> implode
           "bvi_unmapped" | SOME name -> name) in
         let aux = (if km = 0 then implode "" else implode
           "_bvi_aux") in ^
           n aux))) final_nums)`;;
hol4_overload "get_names" "bvl_to_bvi_get_names";;

let compile_def = cake_define
  `bvl_to_bvi_compile start c names prog =
     (let (inlines,prog) = bvl_inline_compile_prog
       (bvl_to_bvi_config_inline_size_limit c)
       (bvl_to_bvi_config_split_main_at_seq
            c) (bvl_to_bvi_config_exp_cut c) prog in
     let (loc,code,n1) = compile_prog start 0 prog in
     let (n2,code') = bvi_tailrec_compile_prog
       (bvl_to_bvi_config_do_tailrec c) ((bvl_num_stubs) + 2) code in
     let (n3,code') = bvi_tmc_compile_prog (bvl_to_bvi_config_do_tmc
       c) ((bvl_num_stubs) + 3) code' in
     let (bvi_inlines,code') = bvi_inline_compile_prog code' in
       (loc,code',inlines,bvi_inlines,n1,n2,n3,
        get_names (MAP FST code') names))`;;
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
