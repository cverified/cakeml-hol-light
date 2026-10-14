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
needs "compiler/backend/closLang.ml";;
(* HOL4 ancestors outside the port: (* for op *) (* for tags *) *)

let bvl_exp_INDUCT,bvl_exp_RECURSION = define_datatype
  "bvl_exp = bvl_Var (num) | bvl_If (bvl_exp) (bvl_exp) (bvl_exp) | \
   bvl_Let (bvl_exp list) (bvl_exp) | bvl_Raise (bvl_exp) | \
   bvl_Handle (bvl_exp) (bvl_exp) | bvl_Tick (bvl_exp) | bvl_Call \
   (num) (num option) (bvl_exp list) | bvl_Force (num) (num) | bvl_Op \
   (closLang_op) (bvl_exp list)";;

let Bool_def = cake_define
  `bvl_Bool b = bvl_Op (closLang_BlockOp (closLang_Cons (bool_to_tag
  b))) []`;;

let mk_tick_def = cake_define
  `mk_tick n e = (FUNPOW bvl_Tick n e:bvl_exp)`;;

(* HOL4 overload (expanded in the port):
     mk_unit = bvl$Op (BlockOp (Cons 0)) [] *)

(* HOL4 overload (expanded in the port):
     mk_elem_at = λb i. bvl$Op (BlockOp (ElemAt i)) [b] *)
