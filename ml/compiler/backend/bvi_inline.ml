(* ======================================================== *)
(*  bvi_inline: ported from HOL4's
    compiler/backend/bvi_inlineScript.sml  *)
(* ======================================================== *)

(*
  A deliberately small BVI inliner for CPR worker-wrapper functions.

  This pass is name preserving.  It only substitutes wrappers satisfying
  [wrapper_ok]; extending that predicate is the intended way to support
    a
  new worker-wrapper protocol.
*)

needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/bvi.ml";;
needs "compiler/backend/closLang.ml";;
needs "lib/sptree.ml";;

let bvi_mk_tick_def = cake_define
  `bvi_mk_tick n e = FUNPOW bvi_Tick n e`;;

(* First-order form for cv_compute, which has no [FUNPOW]. *)

(* [Op] reverses its argument list, so a wrapper that boxes the worker's
   [rets] results in order lists them reversed under the [Cons]. *)
let canonical_wrapper_def = cake_define
  `canonical_wrapper name arity x3 =
        match x3 with
          bvi_LetCall rets ticks worker args
           (bvi_Op (BlockOp (Cons tag)) rvs) -> ~(
        worker = name) /\
        args = GENLIST bvi_Var arity /\
        rvs = REVERSE (GENLIST bvi_Var rets)
        | _1 -> F`;;

let wrapper_ok_def = cake_define
  `wrapper_ok name arity body <=> canonical_wrapper name arity body`;;

(* [cs] is a cache of code-table entries.  The correctness invariant
   needed for a hit is that the cached label, arity, and body correspond
   to the code table (up to the expression relation used by the pass).
     *)
let inline_exp_def = cake_define_list
  [`inline_exp cs (bvi_Var n:bvi_exp) = bvi_Var n`;
   `inline_exp cs (bvi_If x y z:bvi_exp) =
         bvi_If (inline_exp cs x) (inline_exp cs y) (inline_exp
           cs z)`;
   `inline_exp cs (bvi_Let xs y:bvi_exp) =
         bvi_Let (inline_exps cs xs) (inline_exp cs y)`;
   `inline_exp cs (bvi_Raise x:bvi_exp) = bvi_Raise (inline_exp cs x)`;
   `inline_exp cs (bvi_Tick x:bvi_exp) = bvi_Tick (inline_exp cs x)`;
   `inline_exp cs (bvi_Call ticks dest xs handler:bvi_exp) =
         (let xs = inline_exps cs xs in
           match handler with SOME h -> bvi_Call ticks dest xs (SOME
             (inline_exp cs h)) | NONE ->
               (match dest with NONE -> bvi_Call ticks NONE xs NONE
                 | SOME name ->
                   (match lookup name cs with NONE -> bvi_Call ticks
                     (SOME name) xs NONE | SOME (arity,body) ->
                       (if LENGTH xs = arity then
                         bvi_Let xs (bvi_mk_tick (SUC ticks)
                           body) else bvi_Call ticks (SOME name) xs
                           NONE))))`;
   `inline_exp cs (bvi_Force loc n:bvi_exp) = bvi_Force loc n`;
   `inline_exp cs (bvi_Op op xs:bvi_exp) = bvi_Op op (inline_exps cs
  xs)`;
   `inline_exp cs (bvi_LetCall rets ticks dest xs y:bvi_exp) =
         bvi_LetCall rets ticks dest (inline_exps cs xs)
           (inline_exp cs y)`;
   `inline_exp cs (bvi_Return xs:bvi_exp) = bvi_Return (inline_exps
  cs xs)`;
   `inline_exps cs [] = []`;
   `inline_exps cs (x :: xs) = inline_exp cs x :: inline_exps cs xs`];;

let inline_all_def = cake_define
  `(inline_all cs [] = (cs,[])) /\
   (inline_all cs ((name,arity,body) :: prog) =
      (let body = inline_exp cs body in
      let cs1 = if wrapper_ok name arity body then
                  insert name (arity,body) cs else cs in
      let (cs2,prog2) = inline_all cs1 prog in
        (cs2,(name,arity,body) :: prog2)))`;;

let remove_ticks_exp_def = cake_define_list
  [`remove_ticks_exp (bvi_Var n:bvi_exp) = bvi_Var n`;
   `remove_ticks_exp (bvi_If x y z:bvi_exp) =
         bvi_If (remove_ticks_exp x) (remove_ticks_exp y)
           (remove_ticks_exp z)`;
   `remove_ticks_exp (bvi_Let xs y:bvi_exp) =
         bvi_Let (remove_ticks_exps xs) (remove_ticks_exp y)`;
   `remove_ticks_exp (bvi_Raise x:bvi_exp) = bvi_Raise
  (remove_ticks_exp x)`;
   `remove_ticks_exp (bvi_Tick x:bvi_exp) = remove_ticks_exp x`;
   `remove_ticks_exp (bvi_Call ticks dest xs handler:bvi_exp) =
         bvi_Call 0 dest (remove_ticks_exps xs)
           (OPTION_MAP remove_ticks_exp handler)`;
   `remove_ticks_exp (bvi_Force loc n:bvi_exp) = bvi_Force loc n`;
   `remove_ticks_exp (bvi_Op op xs:bvi_exp) = bvi_Op op
  (remove_ticks_exps xs)`;
   `remove_ticks_exp (bvi_LetCall rets ticks dest xs y:bvi_exp) =
         bvi_LetCall rets 0 dest (remove_ticks_exps xs)
           (remove_ticks_exp y)`;
   `remove_ticks_exp (bvi_Return xs:bvi_exp) =
         bvi_Return (remove_ticks_exps xs)`;
   `remove_ticks_exps [] = []`;
   `remove_ticks_exps (x :: xs) =
         remove_ticks_exp x :: remove_ticks_exps xs`];;

let compile_inc_def = cake_define
  `bvi_inline_compile_inc cs prog =
     (let (cs1,prog1) = inline_all cs prog in
       (cs1,MAP (\(name,arity,body).
                   (name,arity,remove_ticks_exp body)) prog1))`;;
hol4_overload "compile_inc" "bvi_inline_compile_inc";;

let compile_prog_def = cake_define
  `bvi_inline_compile_prog prog = compile_inc LN prog`;;
hol4_overload "compile_prog" "bvi_inline_compile_prog";;
