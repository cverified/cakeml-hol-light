(* ======================================================== *)
(*  bvi_let: ported from HOL4's
    compiler/backend/bvi_letScript.sml
    A definition theory, with 6 definitions and 5 theorems.  Needed
    by bvi_letProof.ml and bvl_to_bvi.ml.  *)
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

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "bvi_let"
  ["bvi"];;

let bvi_let_extract_def = new_definition
  `bvi_let_extract x1 ys =
     match x1 with
       ((bvi_Var n):bvi_exp) -> n + LENGTH ys + 1
     | _ -> 0`;;

let extract_list_def,extract_list_ind = define_rec
  `(bvi_let_extract_list [] = []) /\
   (bvi_let_extract_list (CONS x xs) = CONS (bvi_let_extract x xs)
    (bvi_let_extract_list xs))`;;

let delete_var_def = new_definition
  `bvi_let_delete_var x =
     match x with
       ((bvi_Var n):bvi_exp) -> bvi_Op (clos_IntOp (clos_Const (&0))) []
     | x -> x`;;

make_size "bvi_exp";;
let exp2_size_APPEND = prove
 (`!xs ys. bvi_exp_size1 (APPEND xs ys) = bvi_exp_size1 xs + bvi_exp_size1 ys`,
  CHEAT_TAC);;

(* the size facts that the termination of the two definitions of
   this file needs, which ml/lib/define.ml takes from here, and the
   budget that their recursion asks for: eight seconds is what a
   definition of the port is given before it is assumed instead,
   and these two take about twenty each *)

let bvi_let_term_facts = !cake_term_facts;;
let bvi_let_budget = !cake_cheat_budget;;
cake_term_facts := list_size_BUTLAST :: list_size_LAST ::
                   (!cake_term_facts);;
cake_cheat_budget := 300;;

(* Return/LetCall are pass-through (only nested Lets are optimised).
  TODO(multiret):
   no optimisation specific to them yet -- e.g. the Let tail-position move
     could
   extend to `Let xs (Return (GENLIST Var n))`. *)
(* the clauses in two quotations: dest is (num option) and num; xs is (exp
   list) and (_)list, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives, with
   the names that the port gives the constants *)
(* HOL4 bvi_letScript.sml:110-116: the tactic that proves the termination *)
(* the first pass assumes the termination:
   replacing the CHEAT_TAC is all that is left *)
let bvi_let_compile_def,bvi_let_compile_ind = define_wf_cheat_clauses
  `MEASURE (list_size bvi_exp_size o SND o SND)`
  [`(bvi_let_compile env d [] = []) /\
    (bvi_let_compile env d (CONS x (CONS y xs)) = APPEND (bvi_let_compile
    env d [x]) (bvi_let_compile env d (CONS y xs))) /\
    (bvi_let_compile env d [(bvi_Var v):bvi_exp] =
         match (\l n. oEL n l) env v with SOME n -> [bvi_Var (v + n)]
         | _ -> [bvi_Var (v + d)]) /\
    (bvi_let_compile env d [bvi_If x1 x2 x3] =
         [bvi_If (HD (bvi_let_compile env d [x1]))
             (HD (bvi_let_compile env d [x2]))
             (HD (bvi_let_compile env d [x3]))]) /\
    (bvi_let_compile env d [bvi_Let xs x2] =
         let l = LENGTH xs in
           if l = 0 then bvi_let_compile env d [x2] else let k = l - 1 in
               if x2 = bvi_Var k then
                 // moves the last exp into tail-position if the body is a Var
                 let ys = bvi_let_compile env d (BUTLAST xs) in
                   [bvi_Let ys (HD (bvi_let_compile (MAP ((+) k) env) (d +
                       k) [LAST xs]))]
               else let ys = bvi_let_compile env d xs in
                   [bvi_Let (MAP bvi_let_delete_var ys)
                     (HD (bvi_let_compile (APPEND (bvi_let_extract_list
                         ys) env) d [x2]))]) /\
    (bvi_let_compile env d [bvi_Raise x1] =
         [bvi_Raise (HD (bvi_let_compile env d [x1]))]) /\
    (bvi_let_compile env d [bvi_Op op xs] = [bvi_Op op (bvi_let_compile env
    d xs)]) /\
    (bvi_let_compile env d [bvi_Tick x] = [bvi_Tick (HD (bvi_let_compile env
    d [x]))]) /\
    (bvi_let_compile env d [bvi_Force loc v] =
         match (\l n. oEL n l) env v with SOME n -> [bvi_Force loc (v + n)]
         | _ -> [bvi_Force loc (v + d)]) /\
    (bvi_let_compile env d [bvi_Call t dest xs h] =
         [bvi_Call t dest (bvi_let_compile env d xs)
             (match h with NONE -> NONE
                      | SOME e -> SOME (HD (bvi_let_compile (CONS 0
                          env) d [e])))]) /\
    (bvi_let_compile env d [bvi_Return xs] = [bvi_Return (bvi_let_compile
    env d xs)])`;
   `bvi_let_compile env d [bvi_LetCall rets t dest xs y] =
         [bvi_LetCall rets t dest (bvi_let_compile env d xs)
            (HD (bvi_let_compile (APPEND (REPLICATE rets 0) env) d
                [y]))]`];;

(* the clauses in two quotations: dest is (num option) and num; xs is (exp
   list) and (_)list, which one quotation cannot typecheck *)
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL (_,_,e) -> bvi_exp_size e
                                   | INR (_,_,es) -> list_size bvi_exp_size es)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 bvi_letScript.sml:158-168: the tactic that proves the termination *)
let bvi_let_compile_sing_def,bvi_let_compile_sing_ind =
  define_shaped_wf_tac_clauses
  "maplist>measure"
  `MEASURE (\(x0,x1,x2). bvi_exp_size x2)`
  TERM_TAC
  [`(bvi_let_compile_sing env d ((bvi_Var v):bvi_exp) =
         match (\l n. oEL n l) env v with SOME n -> bvi_Var (v + n)
         | _ -> bvi_Var (v + d)) /\
    (bvi_let_compile_sing env d (bvi_If x1 x2 x3) =
         (bvi_If (bvi_let_compile_sing env d x1)
             (bvi_let_compile_sing env d x2)
             (bvi_let_compile_sing env d x3))) /\
    (bvi_let_compile_sing env d (bvi_Let xs x2) =
         let l = LENGTH xs in
           if l = 0 then bvi_let_compile_sing env d x2 else let k = l - 1
               in
               if x2 = bvi_Var k then
                 // moves the last exp into tail-position if the body is a Var
                 let ys = bvi_let_compile_list env d (BUTLAST xs) in
                   (bvi_Let ys ((bvi_let_compile_sing (MAP ((+) k) env) (d
                       + k) (LAST xs))))
               else let ys = bvi_let_compile_list env d xs in
                   (bvi_Let (MAP bvi_let_delete_var ys)
                     ((bvi_let_compile_sing (APPEND
                         (bvi_let_extract_list ys) env) d x2)))) /\
    (bvi_let_compile_sing env d (bvi_Raise x1) =
         (bvi_Raise ((bvi_let_compile_sing env d x1)))) /\
    (bvi_let_compile_sing env d (bvi_Op op xs) = (bvi_Op op
    (bvi_let_compile_list env d xs))) /\
    (bvi_let_compile_sing env d (bvi_Tick x) = (bvi_Tick
    (bvi_let_compile_sing env d x))) /\
    (bvi_let_compile_sing env d (bvi_Force loc v) =
         match (\l n. oEL n l) env v with SOME n -> bvi_Force loc (v + n)
         | _ -> bvi_Force loc (v + d)) /\
    (bvi_let_compile_sing env d (bvi_Call t dest xs h) =
         (bvi_Call t dest (bvi_let_compile_list env d xs)
             (match h with NONE -> NONE
                      | SOME e -> SOME ((bvi_let_compile_sing (CONS 0
                          env) d e))))) /\
    (bvi_let_compile_sing env d (bvi_Return xs) = bvi_Return
    (bvi_let_compile_list env d xs)) /\
    (bvi_let_compile_list env d [] = []) /\
    (bvi_let_compile_list env d (CONS x xs) = CONS (bvi_let_compile_sing
    env d x) (bvi_let_compile_list env d xs))`;
   `bvi_let_compile_sing env d (bvi_LetCall rets t dest xs y) =
         bvi_LetCall rets t dest (bvi_let_compile_list env d xs)
            (bvi_let_compile_sing (APPEND (REPLICATE rets 0) env) d y)`];;

cake_term_facts := bvi_let_term_facts;;
cake_cheat_budget := bvi_let_budget;;

let compile_sing = prove
 (`(!n d e. bvi_let_compile n d [e] = [bvi_let_compile_sing n d e]) /\
   (!n d e. bvi_let_compile_list n d e = bvi_let_compile n d e)`,
  CHEAT_TAC);;

let compile_length = prove
 (`!n d xs. LENGTH (bvi_let_compile n d xs) = LENGTH xs`,
  CHEAT_TAC);;
add_simp compile_length;;

let compile_HD_SING = prove
 (`[HD (bvi_let_compile n d [x])] = bvi_let_compile n d [x]`,
  CHEAT_TAC);;

let bvi_let_compile_exp_def = new_definition
  `bvi_let_compile_exp x =
     match bvi_let_compile [] 0 [x] with (CONS y _) -> y | _ -> bvi_Var 0
   // impossible`;;

let bvi_let_compile_exp_eq = SIMP_RULE [compile_sing] bvi_let_compile_exp_def;;

(* and the interface *)
let _ = unhide_overloads ();;
