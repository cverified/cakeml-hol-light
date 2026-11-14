(* ======================================================== *)
(*  bvl: ported from HOL4's
    compiler/backend/bvlScript.sml
    A definition theory, with 2 definitions, 1 datatype and no
    theorems.  Needed by 10 files of the port.  *)
(* ======================================================== *)

(*
  The BVL intermediate language. This language is a simple first-order
  functional language without closures.

  BVL = bytecode-value language

   All operations that are uninteresting from a control-flow
   and binding perspective are lumped together in closLang$op.

   There are only a handful of "interesting" operations.

   BVL uses De Bruijn indices so there is no need for a variable name
   in the let-expression.

   The optional number in the call expression below is the label to
   which the call will target. If that component is NONE, then the
   target address is read from the end of the argument list, i.e. in
   case of NONE, the last exp in the argument list must evaluate
   to a CodePtr. This first number in the Call expression is how
   many additional ticks the Call should do.
*)

needs "compiler/backend/backend_common.ml";;
(* for tags *)
needs "compiler/backend/closLang.ml";;
(* for op *)

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvl"
  ["backend_common"; "closLang"];;

let bvl_exp_INDUCT,bvl_exp_RECURSION = define_datatype
  "bvl_exp = bvl_Var (num) | bvl_If (bvl_exp) (bvl_exp) (bvl_exp) | \
   bvl_Let (bvl_exp list) (bvl_exp) | bvl_Raise (bvl_exp) | \
   bvl_Handle (bvl_exp) (bvl_exp) | bvl_Tick (bvl_exp) | bvl_Call \
   (num) (num option) (bvl_exp list) | bvl_Force (num) (num) \
   // loc to call for evaluation of unevaluated thunk\n\
   // var holding thunk\n\
   | bvl_Op (closLang_op) (bvl_exp list)";;

let bool_def = new_definition
  `bvl_Bool b = bvl_Op (closLang_BlockOp (closLang_Cons (bool_to_tag
  b))) []`;;

let mk_tick_def = new_definition
  `mk_tick n e = (ITER n bvl_Tick e:bvl_exp)`;;

(* HOL4 bvlScript.sml:50: the overload mk_unit, which the port
   expands *)

(* HOL4 bvlScript.sml:52: the overload mk_elem_at, which the port
   expands *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
