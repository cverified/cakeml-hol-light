(* ======================================================== *)
(*  bvi: ported from HOL4's
    compiler/backend/bviScript.sml  *)
(* ======================================================== *)

(*
  The BVI intermediate language. This language is very similar to BVL.
  One of the more notable differences is that exception handling is
  now bundled together with function calls: exceptions can only be
  caught at the point of function calls.
*)

needs "compiler/backend/closLang.ml";;
(* HOL4 ancestors outside the port: (* for op *) *)

(* BVI = bytecode-value intermediate language *)

(* BVI is a stepping stone on the way from BVL to dataLang. BVI is
   almost
   identical to BVL. The main differences are:

    - The Handle (exception) construct from BVL has been merged into
      the Call construct. The reason we want to do this is that we
      want each function in BVI (and the following intermediate
      languages) to only operate within one stack frame. The execution
      of the body of the Handle construct is to execute in a separate
      stack frame. To keep things simple and uniform, we merge all
      stack-frame creation into the Call construct. Note that BVL and
      BVI have no concept of stack frames. However, the next language,
      dataLang, does have stack frames. BVI is a nice high-level
        language
      where the Handle construct can cleanly be eliminated.

    - Each creation of a number constant must only produce constants
      that will fit into a machine word. The previous language, BVL,
      allows any size of integer to be constructed immediately. In
      BVI, we compile creation of very large constants into creation
      of small constants, and plug these together using +, - and *.

    - BVI also doesn't have the 'globals' state component from BVL.
      BVI implements the globals using a (dynamically extended) wide
      reference. *)


(* --- Syntax of BVI --- *)

let bvi_exp_INDUCT,bvi_exp_RECURSION = define_datatype
  "bvi_exp = bvi_Var (num) | bvi_If (bvi_exp) (bvi_exp) (bvi_exp) | \
   bvi_Let (bvi_exp list) (bvi_exp) | bvi_Raise (bvi_exp) | bvi_Tick \
   (bvi_exp) | bvi_Call (num) (num option) (bvi_exp list) (bvi_exp \
   option) | bvi_Force (num) (num) | bvi_Op (closLang_op) (bvi_exp \
   list) | bvi_LetCall (num) (num) (num) (bvi_exp list) (bvi_exp) | \
   bvi_Return (bvi_exp list)";;

(* HOL4 overload (expanded in the port):
     mk_unit = bvi$Op (BlockOp (Cons 0)) [] *)

(* HOL4 overload (expanded in the port):
     mk_elem_at = λb i. bvi$Op (BlockOp (ElemAt i)) [b] *)

(* HOL4 overload (expanded in the port):
     TailCall = λret_count ticks dest args.
                       LetCall ret_count ticks dest args (Return
                         (GENLIST Var ret_count)) *)
