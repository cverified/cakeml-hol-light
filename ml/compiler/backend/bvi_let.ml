(* ======================================================== *)
(*  bvi_let: ported from HOL4's
    compiler/backend/bvi_letScript.sml  *)
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

let extract_def = cake_define
  `bvi_let_extract x1 ys =
        match x1 with
          ((bvi_Var n):bvi_exp) -> n + LENGTH ys + 1
        | _1 -> 0`;;

let extract_list_def = cake_define
  `(bvi_let_extract_list [] = []) /\
   (bvi_let_extract_list (x :: xs) = bvi_let_extract x xs ::
     bvi_let_extract_list xs)`;;

let delete_var_def = cake_define
  `bvi_let_delete_var x =
        match x with
          ((bvi_Var n):bvi_exp) -> bvi_Op (closLang_IntOp
            (closLang_Const 0)) []
        | x -> x`;;

(* HOL4 termination: \\ rw [] \\ fs [LENGTH_NIL] \\ imp_res_tac
   (METIS_PROVE [SNOC_CASES] ``m <> [] ==> ?x y. m = SNOC x y``) \\
   full_simp_tac std_ss [LAST_SNOC,LENGTH_SNOC,FRONT_SNOC] \\ fs
   [exp2_size_APPEND,SNOC_APPEND,exp_size_def] *)
let compile_def = cake_define_wf
  `MEASURE (exp2_size o SND o SND)`
  `(bvi_let_compile env d [] = []) /\
   (bvi_let_compile env d (x :: y :: xs) = bvi_let_compile env d [x]
     ++ bvi_let_compile env d (y :: xs)) /\
   (bvi_let_compile env d [(bvi_Var v):bvi_exp] =
      (match (\l n. oEL n l) env v with SOME n -> [bvi_Var (v + n)] |
        _2 -> [bvi_Var (v + d)])) /\
   (bvi_let_compile env d [bvi_If x1 x2 x3] =
      [bvi_If (HD (bvi_let_compile env d [x1]))
          (HD (bvi_let_compile env d [x2]))
          (HD (bvi_let_compile env d [x3]))]) /\
   (bvi_let_compile env d [bvi_Let xs x2] =
      (let l = LENGTH xs in
        if l = 0 then bvi_let_compile env d [x2] else
          let k = l - 1 in
            if x2 = bvi_Var k then
              let ys = bvi_let_compile env d (BUTLAST xs) in
                [bvi_Let ys (HD (bvi_let_compile (MAP ((+) k) env) (d
                  + k) [LAST xs]))] else
              let ys = bvi_let_compile env d xs in
                [bvi_Let (MAP bvi_let_delete_var ys)
                  (HD (bvi_let_compile (bvi_let_extract_list ys ++
                    env) d [x2]))])) /\
   (bvi_let_compile env d [bvi_Raise x1] =
      [bvi_Raise (HD (bvi_let_compile env d [x1]))]) /\
   (bvi_let_compile env d [bvi_Op closLang_op xs] = [bvi_Op
     closLang_op (bvi_let_compile env d xs)]) /\
   (bvi_let_compile env d [bvi_Tick x] = [bvi_Tick (HD
     (bvi_let_compile env d [x]))]) /\
   (bvi_let_compile env d [bvi_Force loc v] =
      (match (\l n. oEL n l) env v with SOME n -> [bvi_Force loc (v +
        n)] | _3 -> [bvi_Force loc (v + d)])) /\
   (bvi_let_compile env d [bvi_Call t dest xs h] =
      [bvi_Call t dest (bvi_let_compile env d xs)
          (match h with NONE -> NONE | SOME e -> SOME (HD
            (bvi_let_compile (0 :: env) d [e])))]) /\
   (bvi_let_compile env d [bvi_Return xs] = [bvi_Return
     (bvi_let_compile env d xs)]) /\
   (bvi_let_compile env d [bvi_LetCall rets t dest xs y] =
      [bvi_LetCall rets t dest (bvi_let_compile env d xs)
         (HD (bvi_let_compile (REPLICATE rets 0 ++ env) d [y]))])`;;

(* HOL4 termination: \\ rw[bviTheory.exp_size_def] \\ rename1`xs ≠
   []` \\ pop_assum mp_tac \\ qid_spec_tac`xs` \\ Cases using
   SNOC_CASES \\ gvs
   [SNOC_APPEND,exp2_size_APPEND,bviTheory.exp_size_def
     ,list_size_APPEND] *)
let compile_sing_def = cake_define_wf
  `MEASURE (\x. match x with INL (_6,_7,e) -> exp_size e | INR
  (_8,_9,es) -> list_size exp_size es)`
  `(bvi_let_compile_sing env d ((bvi_Var v):bvi_exp) =
      (match (\l n. oEL n l) env v with SOME n -> bvi_Var (v + n) |
        _4 -> bvi_Var (v + d))) /\
   (bvi_let_compile_sing env d (bvi_If x1 x2 x3) =
      (bvi_If (bvi_let_compile_sing env d x1)
          (bvi_let_compile_sing env d x2)
          (bvi_let_compile_sing env d x3))) /\
   (bvi_let_compile_sing env d (bvi_Let xs x2) =
      (let l = LENGTH xs in
        if l = 0 then bvi_let_compile_sing env d x2 else
          let k = l - 1 in
            if x2 = bvi_Var k then
              let ys = bvi_let_compile_list env d (BUTLAST xs) in
                (bvi_Let ys ((bvi_let_compile_sing (MAP ((+) k) env)
                  (d + k) (LAST xs)))) else
              let ys = bvi_let_compile_list env d xs in
                (bvi_Let (MAP bvi_let_delete_var ys)
                  ((bvi_let_compile_sing (bvi_let_extract_list ys ++
                    env) d x2))))) /\
   (bvi_let_compile_sing env d (bvi_Raise x1) =
      (bvi_Raise ((bvi_let_compile_sing env d x1)))) /\
   (bvi_let_compile_sing env d (bvi_Op closLang_op xs) = (bvi_Op
     closLang_op (bvi_let_compile_list env d xs))) /\
   (bvi_let_compile_sing env d (bvi_Tick x) = (bvi_Tick
     (bvi_let_compile_sing env d x))) /\
   (bvi_let_compile_sing env d (bvi_Force loc v) =
      (match (\l n. oEL n l) env v with SOME n -> bvi_Force loc (v +
        n) | _5 -> bvi_Force loc (v + d))) /\
   (bvi_let_compile_sing env d (bvi_Call t dest xs h) =
      (bvi_Call t dest (bvi_let_compile_list env d xs)
          (match h with NONE -> NONE | SOME e -> SOME
            ((bvi_let_compile_sing (0 :: env) d e))))) /\
   (bvi_let_compile_sing env d (bvi_Return xs) = bvi_Return
     (bvi_let_compile_list env d xs)) /\
   (bvi_let_compile_sing env d (bvi_LetCall rets t dest xs y) =
      bvi_LetCall rets t dest (bvi_let_compile_list env d xs)
         (bvi_let_compile_sing (REPLICATE rets 0 ++ env) d y)) /\
   (bvi_let_compile_list env d [] = []) /\
   (bvi_let_compile_list env d (x :: xs) =
     bvi_let_compile_sing env d x :: bvi_let_compile_list env d
       xs)`;;

let compile_exp_def = cake_define
  `bvi_let_compile_exp x =
     (match bvi_let_compile [] 0 [x] with (y :: _10) -> y | _11 ->
       bvi_Var 0)`;;
