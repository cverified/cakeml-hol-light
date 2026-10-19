(* ======================================================== *)
(*  bvi: ported from HOL4's
    compiler/backend/bviScript.sml
    A definition theory, with no definitions, 1 datatype and no
    theorems.  Needed by 10 files of the port.  *)
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

(* BVI is a stepping stone on the way from BVL to dataLang. BVI is almost
   identical to BVL. The main differences are:

    - The Handle (exception) construct from BVL has been merged into
      the Call construct. The reason we want to do this is that we
      want each function in BVI (and the following intermediate
      languages) to only operate within one stack frame. The execution
      of the body of the Handle construct is to execute in a separate
      stack frame. To keep things simple and uniform, we merge all
      stack-frame creation into the Call construct. Note that BVL and
      BVI have no concept of stack frames. However, the next language,
      dataLang, does have stack frames. BVI is a nice high-level language
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
   option) | bvi_Force (num) (num) \
   // loc to call for evaluation of unevaluated thunk\n\
   // var holding thunk\n\
   | bvi_Op (closLang_op) (bvi_exp list) | \
   // multi-value call and return:\n\
   // let-and-call: num of return values, ticks, call target, args, body of let\n\
   bvi_LetCall (num) (num) (num) (bvi_exp list) (bvi_exp) | \
   // return-multi-value: returns values of given expressions\n\
   bvi_Return (bvi_exp list)";;
hol4_overload "Var" "bvi_Var";;
hol4_overload "If" "bvi_If";;
hol4_overload "Let" "bvi_Let";;
hol4_overload "Raise" "bvi_Raise";;
hol4_overload "Tick" "bvi_Tick";;
hol4_overload "Call" "bvi_Call";;
hol4_overload "Force" "bvi_Force";;
hol4_overload "Op" "bvi_Op";;
hol4_overload "LetCall" "bvi_LetCall";;
hol4_overload "Return" "bvi_Return";;

(* HOL4 bviScript.sml:59: the overload mk_unit, which the port
   expands *)

(* HOL4 bviScript.sml:61: the overload mk_elem_at, which the port
   expands *)

(* HOL4 bviScript.sml:63-64: the overload TailCall, which the port
   expands *)
