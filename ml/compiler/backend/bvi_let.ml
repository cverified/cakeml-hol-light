(* ======================================================== *)
(*  bvi_let: ported from HOL4's
    compiler/backend/bvi_letScript.sml
    A definition theory, with 6 definitions and 5 theorems.  Needed
    by bvi_letProof.ml, bvl_to_bvi.ml and bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*

   This is a BVI transformation that propagates variable lookups that
   are immediately assigned to a new variable in Let bindings. This
   optimisation is to run immediately when entering BVI.

   This optimisation removes each Var in a Let, i.e.

     Let [ ... ; Var ... ; ... ] ...

   and replaces them with constants

     Let [ ... ; Op (IntOp (Const _)) [] ; ... ] ....

   and then replaces all occurrences of the bound var in the body with
   a lookup to the original variable.

   There is a similar optimisation in BVL (bvl_const). This version
   (which is slightly simpler) is run again because the BVL-to-BVI
   compiler can introduce large Let expressions consisting of only
   variable lookups.

   This BVI version differs from the BVL version (bvl_const) by having
   the ability to move expressions into tail-position, e.g.

     let
       val x = foo ...
       val y = bar x
     in y end

   becomes:

     let
       val x = foo ...
     in bar x end

   This is important because pat-to-clos translates Seq p1 p2 into
   Let [compile p1; compile p2] (Var 1).

*)

needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;

let extract_def = cake_define
  `bvi_let_extract x1 ys =
        match x1 with
          ((Var n):bvi_exp) -> n + LENGTH ys + 1
        | _1 -> 0`;;
hol4_overload "extract" "bvi_let_extract";;

let extract_list_def = cake_define_list
  [`bvi_let_extract_list [] = []`;
   `bvi_let_extract_list (x :: xs) = extract x xs ::
  bvi_let_extract_list xs`];;
hol4_overload "extract_list" "bvi_let_extract_list";;

let delete_var_def = cake_define
  `bvi_let_delete_var x =
        match x with
          ((Var n):bvi_exp) -> Op (closLang_IntOp (closLang_Const
            (&0))) []
        | x -> x`;;
hol4_overload "delete_var" "bvi_let_delete_var";;

(* HOL4 bvi_letScript.sml:62-66: a theorem whose statement the port
   cannot state yet: exp2_size_APPEND *)

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let compile_def = cake_define_list_try_tac (fun () ->
  `MEASURE (list_size bvi_exp_size o SND o SND)`)
  CHEAT_TAC
  [`bvi_let_compile env d [] = []`;
   `bvi_let_compile env d (x :: y :: xs) = bvi_let_compile env d [x]
  ++ bvi_let_compile env d (y :: xs)`;
   `bvi_let_compile env d [(Var v):bvi_exp] =
         (match (\l n. oEL n l) env v with SOME n -> [Var (v +
           n)] | _2 -> [Var (v + d)])`;
   `bvi_let_compile env d [(If x1 x2 x3:bvi_exp)] =
         [If (HD (bvi_let_compile env d [x1]))
             (HD (bvi_let_compile env d [x2]))
             (HD (bvi_let_compile env d [x3]))]`;
   `bvi_let_compile env d [(Let xs x2:bvi_exp)] =
         (let l = LENGTH xs in
           if l = 0 then bvi_let_compile env d [x2] else
             let k = l - 1 in
               if x2 = Var k then
                 let ys = bvi_let_compile env d (BUTLAST xs) in
                   [Let ys (HD (bvi_let_compile (MAP ((+) k) env) (d
                     + k) [LAST xs]))] else
                 let ys = bvi_let_compile env d xs in
                   [Let (MAP bvi_let_delete_var ys)
                     (HD (bvi_let_compile (bvi_let_extract_list
                       ys ++ env) d [x2]))])`;
   `bvi_let_compile env d [(Raise x1:bvi_exp)] =
         [Raise (HD (bvi_let_compile env d [x1]))]`;
   `bvi_let_compile env d [(Op op xs:bvi_exp)] = [Op op
  (bvi_let_compile env d xs)]`;
   `bvi_let_compile env d [(Tick x:bvi_exp)] = [Tick (HD
  (bvi_let_compile env d [x]))]`;
   `bvi_let_compile env d [(Force loc v:bvi_exp)] =
         (match (\l n. oEL n l) env v with SOME n -> [Force loc
           (v + n)] | _5 -> [Force loc (v + d)])`;
   `bvi_let_compile env d [(Call t dest xs h:bvi_exp)] =
         [Call t dest (bvi_let_compile env d xs)
             (match h with NONE -> NONE | SOME e -> SOME (HD
               (bvi_let_compile (0 :: env) d [e])))]`;
   `bvi_let_compile env d [(bvi_Return xs:bvi_exp)] = [bvi_Return
  (bvi_let_compile env d xs)]`;
   `bvi_let_compile env d [bvi_LetCall rets t dest xs y] =
         [bvi_LetCall rets t dest (bvi_let_compile env d xs)
            (HD (bvi_let_compile (REPLICATE rets 0 ++ env) d
              [y]))]`];;
hol4_overload "compile" "bvi_let_compile";;

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_letScript.sml:158-168: the tactic that proves the
   termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let compile_sing_def = cake_define_list_try_tac (fun () ->
  `MEASURE (\x. match x with INL (_10,_11,e) -> bvi_exp_size e | INR
     (_12,_13,es) -> list_size bvi_exp_size es)`)
  CHEAT_TAC
  [`bvi_let_compile_sing env d ((Var v):bvi_exp) =
         (match (\l n. oEL n l) env v with SOME n -> Var (v + n)
           | _6 -> Var (v + d))`;
   `bvi_let_compile_sing env d (If x1 x2 x3:bvi_exp) =
         (If (bvi_let_compile_sing env d x1)
             (bvi_let_compile_sing env d x2)
             (bvi_let_compile_sing env d x3))`;
   `bvi_let_compile_sing env d (Let xs x2:bvi_exp) =
         (let l = LENGTH xs in
           if l = 0 then bvi_let_compile_sing env d x2 else
             let k = l - 1 in
               if x2 = Var k then
                 let ys = bvi_let_compile_list env d (BUTLAST xs) in
                   (Let ys ((bvi_let_compile_sing (MAP ((+) k) env)
                     (d + k) (LAST xs)))) else
                 let ys = bvi_let_compile_list env d xs in
                   (Let (MAP bvi_let_delete_var ys)
                     ((bvi_let_compile_sing (bvi_let_extract_list
                       ys ++ env) d x2))))`;
   `bvi_let_compile_sing env d (Raise x1:bvi_exp) =
         (Raise ((bvi_let_compile_sing env d x1)))`;
   `bvi_let_compile_sing env d (Op op xs:bvi_exp) = (Op op
  (bvi_let_compile_list env d xs))`;
   `bvi_let_compile_sing env d (Tick x:bvi_exp) = (Tick
  (bvi_let_compile_sing env d x))`;
   `bvi_let_compile_sing env d (Force loc v:bvi_exp) =
         (match (\l n. oEL n l) env v with SOME n -> Force loc (v
           + n) | _9 -> Force loc (v + d))`;
   `bvi_let_compile_sing env d (Call t dest xs h:bvi_exp) =
         (Call t dest (bvi_let_compile_list env d xs)
             (match h with NONE -> NONE | SOME e -> SOME
               ((bvi_let_compile_sing (0 :: env) d e))))`;
   `bvi_let_compile_sing env d (bvi_Return xs:bvi_exp) = bvi_Return
  (bvi_let_compile_list env d xs)`;
   `bvi_let_compile_sing env d (bvi_LetCall rets t dest xs y) =
         bvi_LetCall rets t dest (bvi_let_compile_list env d xs)
            (bvi_let_compile_sing (REPLICATE rets 0 ++ env) d y)`;
   `bvi_let_compile_list env d [] = []`;
   `bvi_let_compile_list env d (x :: xs) =
        bvi_let_compile_sing env d x :: bvi_let_compile_list
          env d xs`];;
hol4_overload "compile_list" "bvi_let_compile_list";;
hol4_overload "compile_sing" "bvi_let_compile_sing";;

let compile_sing = cake_theorem "compile_sing"
  (fun () ->
    `(!n d e. bvi_let_compile n d [e] = [bvi_let_compile_sing n d e]) /\
     (!n d e. bvi_let_compile_list n d e = bvi_let_compile n d e)`)
  CHEAT_TAC;;

let compile_length = cake_theorem "compile_length[simp]"
  (fun () ->
    `!n d xs. LENGTH (bvi_let_compile n d xs) = LENGTH xs`)
  CHEAT_TAC;;

let compile_HD_SING = cake_theorem "compile_HD_SING"
  (fun () ->
    `[HD (bvi_let_compile n d [x])] = bvi_let_compile n d [x]`)
  CHEAT_TAC;;

let compile_exp_def = cake_define
  `bvi_let_compile_exp x =
     (match bvi_let_compile [] 0 [x] with (y :: _14) -> y | _15 ->
       Var 0)`;;
hol4_overload "compile_exp" "bvi_let_compile_exp";;

(* HOL4 bvi_letScript.sml:202: a theorem that HOL4 states as the
   value of an ML expression: compile_exp_eq *)
