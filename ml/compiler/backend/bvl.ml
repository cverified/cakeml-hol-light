(* ======================================================== *)
(*  bvl: ported from HOL4's
    compiler/backend/bvlScript.sml  *)
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
hol4_overload "Var" "bvl_Var";;
hol4_overload "If" "bvl_If";;
hol4_overload "Let" "bvl_Let";;
hol4_overload "Raise" "bvl_Raise";;
hol4_overload "Handle" "bvl_Handle";;
hol4_overload "Tick" "bvl_Tick";;
hol4_overload "Call" "bvl_Call";;
hol4_overload "Force" "bvl_Force";;
hol4_overload "Op" "bvl_Op";;

let bool_def = new_definition
  `bvl_Bool b = Op (closLang_BlockOp (closLang_Cons (bool_to_tag b)))
  []`;;
hol4_overload "Bool" "bvl_Bool";;

let mk_tick_def = new_definition
  `mk_tick n e = (FUNPOW Tick n e:bvl_exp)`;;

(* HOL4 bvlScript.sml:50: the overload mk_unit, which the port
   expands *)

(* HOL4 bvlScript.sml:52: the overload mk_elem_at, which the port
   expands *)

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
