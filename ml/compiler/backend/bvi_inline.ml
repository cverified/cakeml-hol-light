(* ======================================================== *)
(*  bvi_inline: ported from HOL4's
    compiler/backend/bvi_inlineScript.sml
    A definition theory, with 8 definitions and 5 theorems.  Needed
    by bvi_inlineProof.ml, bvl_to_bvi.ml and bvl_to_bviProof.ml.  *)
(* ======================================================== *)

(*
  A deliberately small BVI inliner for CPR worker-wrapper functions.

  This pass is name preserving.  It only substitutes wrappers satisfying
  [wrapper_ok]; extending that predicate is the intended way to support a
  new worker-wrapper protocol.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvi_inline"
  ["backend_common"; "bvi"];;

let bvi_mk_tick_def = new_definition
  `bvi_mk_tick n e = FUNPOW bvi_Tick n e`;;

(* First-order form for cv_compute, which has no [FUNPOW]. *)
let bvi_mk_tick_eq = prove
 (`bvi_mk_tick n e = (if n = 0 then e else bvi_Tick (bvi_mk_tick (n -
  1) e))`,
  CHEAT_TAC);;

(* [Op] reverses its argument list, so a wrapper that boxes the worker's
   [rets] results in order lists them reversed under the [Cons]. *)
let canonical_wrapper_def = new_definition
  `canonical_wrapper name arity x3 =
        match x3 with
          bvi_LetCall rets ticks worker args
           (bvi_Op (closLang_BlockOp (closLang_Cons tag)) rvs) ->
             ~(worker = name) /\
        args = list_of_seq bvi_Var arity /\
        rvs = REVERSE (list_of_seq bvi_Var rets)
        | _1 -> F`;;

let wrapper_ok_def = new_definition
  `wrapper_ok name arity body <=> canonical_wrapper name arity body`;;

(* [cs] is a cache of code-table entries.  The correctness invariant
   needed for a hit is that the cached label, arity, and body correspond
   to the code table (up to the expression relation used by the pass). *)
let _ = size_thms "bvi_exp";;
let inline_exp_def,inline_exp_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`inline_exp cs (bvi_Var n) = bvi_Var n`;
   `inline_exp cs (bvi_If x y z) =
         bvi_If (inline_exp cs x) (inline_exp cs y) (inline_exp
           cs z)`;
   `inline_exp cs (bvi_Let xs y) =
         bvi_Let (inline_exps cs xs) (inline_exp cs y)`;
   `inline_exp cs (bvi_Raise x) = bvi_Raise (inline_exp cs x)`;
   `inline_exp cs (bvi_Tick x) = bvi_Tick (inline_exp cs x)`;
   `inline_exp cs (bvi_Call ticks dest xs handler) =
         (let xs = inline_exps cs xs in
           match handler with SOME h -> bvi_Call ticks dest xs (SOME
             (inline_exp cs h)) | NONE ->
               (match dest with NONE -> bvi_Call ticks NONE xs NONE
                 | SOME name ->
                   (match sptree_lookup name cs with NONE ->
                     bvi_Call ticks (SOME name) xs NONE | SOME
                     (arity,body) ->
                       (if LENGTH xs = arity then
                         bvi_Let xs (bvi_mk_tick (SUC ticks)
                           body) else bvi_Call ticks (SOME name) xs
                           NONE))))`;
   `inline_exp cs (bvi_Force loc n) = bvi_Force loc n`;
   `inline_exp cs (bvi_Op op xs) = bvi_Op op (inline_exps cs xs)`;
   `inline_exp cs (bvi_LetCall rets ticks dest xs y) =
         bvi_LetCall rets ticks dest (inline_exps cs xs)
           (inline_exp cs y)`;
   `inline_exp cs (bvi_Return xs) = bvi_Return (inline_exps cs xs)`;
   `inline_exps cs [] = []`;
   `inline_exps cs (CONS x xs) = CONS (inline_exp cs x)
  (inline_exps cs xs)`];;

let inline_all_def,inline_all_ind = define_rec
  [`inline_all cs [] = (cs,[])`;
   `inline_all cs (CONS (name,arity,body) prog) =
         (let body = inline_exp cs body in
         let cs1 = (if wrapper_ok name arity body then
                     sptree_insert name (arity,body) cs else cs) in
         let (cs2,prog2) = inline_all cs1 prog in
           (cs2,CONS (name,arity,body) prog2))`];;

let _ = size_thms "bvi_exp";;
(* the termination relation that HOL4 gives is
     MEASURE (\x. match x with INL e -> bvi_exp_size e | INR es ->
       list_size bvi_exp_size es)
   which is not one that HOL Light takes here; the one
   below is what the port found for it *)
(* HOL4 bvi_inlineScript.sml:115-120: the tactic that proves the
   termination *)
let remove_ticks_exp_def,remove_ticks_exp_ind = define_mutual_shaped_wf
  "maplist>measure"
  `MEASURE (\x0. bvi_exp_size x0)`
  [`remove_ticks_exp (bvi_Var n) = bvi_Var n`;
   `remove_ticks_exp (bvi_If x y z) =
         bvi_If (remove_ticks_exp x) (remove_ticks_exp y)
           (remove_ticks_exp z)`;
   `remove_ticks_exp (bvi_Let xs y) =
         bvi_Let (remove_ticks_exps xs) (remove_ticks_exp y)`;
   `remove_ticks_exp (bvi_Raise x) = bvi_Raise (remove_ticks_exp x)`;
   `remove_ticks_exp (bvi_Tick x) = remove_ticks_exp x`;
   `remove_ticks_exp (bvi_Call ticks dest xs handler) =
         bvi_Call 0 dest (remove_ticks_exps xs)
           (OPTION_MAP remove_ticks_exp handler)`;
   `remove_ticks_exp (bvi_Force loc n) = bvi_Force loc n`;
   `remove_ticks_exp (bvi_Op op xs) = bvi_Op op (remove_ticks_exps
  xs)`;
   `remove_ticks_exp (bvi_LetCall rets ticks dest xs y) =
         bvi_LetCall rets 0 dest (remove_ticks_exps xs)
           (remove_ticks_exp y)`;
   `remove_ticks_exp (bvi_Return xs) =
         bvi_Return (remove_ticks_exps xs)`;
   `remove_ticks_exps [] = []`;
   `remove_ticks_exps (CONS x xs) = CONS (remove_ticks_exp x)
  (remove_ticks_exps xs)`];;

let compile_inc_def = new_definition
  `bvi_inline_compile_inc cs prog =
     (let (cs1,prog1) = inline_all cs prog in
       (cs1,MAP (\(name,arity,body).
                   (name,arity,remove_ticks_exp body)) prog1))`;;
hol4_overload "compile_inc" "bvi_inline_compile_inc";;

let bvi_inline_compile_prog_def = new_definition
  `bvi_inline_compile_prog prog = bvi_inline_compile_inc LN prog`;;
hol4_overload "compile_prog" "bvi_inline_compile_prog";;

let canonical_four_result_wrapper = prove
 (`wrapper_ok 10 3
     (bvi_LetCall 4 0 11 (list_of_seq Var 3)
       (bvi_Op (closLang_BlockOp (closLang_Cons 7)) (REVERSE
         (list_of_seq Var 4))))`,
  CHEAT_TAC);;

let malformed_wrappers_rejected = prove
 (`~(wrapper_ok 10 3
       (bvi_LetCall 4 0 10 (list_of_seq Var 3)
         (bvi_Op (closLang_BlockOp (closLang_Cons 7)) (list_of_seq
           Var 4)))) /\
   ~(wrapper_ok 10 3
       (bvi_LetCall 4 0 11 [Var 0; Var 2; Var 1]
         (bvi_Op (closLang_BlockOp (closLang_Cons 7)) (list_of_seq
           Var 4)))) /\
   ~(wrapper_ok 10 3
       (bvi_LetCall 4 0 11 (list_of_seq Var 3)
         (bvi_Op (closLang_BlockOp (closLang_Cons 7)) [Var 0; Var 1;
           Var 2]))) /\
   ~(wrapper_ok 10 3 (bvi_Return (list_of_seq Var 3)))`,
  CHEAT_TAC);;

let inline_boundary_examples = prove
 (`inline_exp (sptree_insert 10 (3,
       bvi_LetCall 4 0 11 (list_of_seq Var 3)
         (bvi_Op (closLang_BlockOp (closLang_Cons 7)) (list_of_seq
           Var 4))) LN) (Call 2 (SOME 10) [Var 4; Var 5; Var 6]
           NONE:bvi_exp) =
       Let [Var 4; Var 5; Var 6]
         (bvi_mk_tick 3
           (bvi_LetCall 4 0 11 (list_of_seq Var 3)
             (bvi_Op (closLang_BlockOp (closLang_Cons 7))
               (list_of_seq Var 4)))) /\
   inline_exp (sptree_insert 10 (3,
       bvi_LetCall 4 0 11 (list_of_seq Var 3)
         (bvi_Op (closLang_BlockOp (closLang_Cons 7)) (list_of_seq
           Var 4))) LN)
     (Call 2 (SOME 10) [Var 4; Var 5; Var 6] (SOME (Var 0))) =
       Call 2 (SOME 10) [Var 4; Var 5; Var 6] (SOME (Var 0)) /\
   inline_exp (sptree_insert 10 (3,
       bvi_LetCall 4 0 11 (list_of_seq Var 3)
         (bvi_Op (closLang_BlockOp (closLang_Cons 7)) (list_of_seq
           Var 4))) LN)
     (bvi_LetCall 1 2 10 [Var 4; Var 5; Var 6] (bvi_Return [Var 0]))
       =
       bvi_LetCall 1 2 10 [Var 4; Var 5; Var 6] (bvi_Return [Var
         0])`,
  CHEAT_TAC);;

let final_tick_cleanup_example = prove
 (`remove_ticks_exp (Tick (bvi_Call 2 (SOME 10) [Tick (bvi_Var 0)]
       (SOME (bvi_LetCall 1 3 11 [Tick (bvi_Var 1)] (bvi_Return [Var
         0])))):bvi_exp) =
     Call 0 (SOME 10) [Var 0]
       (SOME (bvi_LetCall 1 0 11 [Var 1] (bvi_Return [Var 0])))`,
  CHEAT_TAC);;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
