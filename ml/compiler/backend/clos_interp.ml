(* ======================================================== *)
(*  clos_interp: ported from HOL4's
    compiler/backend/clos_interpScript.sml
    A definition theory, with 17 definitions and 3 theorems.  Needed
    by clos_interpProof.ml, flat_to_clos.ml and
    flat_to_closProof.ml.  *)
(* ======================================================== *)

(*
  Implementation of interpreter for closLang expressions written in closLang.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;

(* the theory of this file, and the ones its statements read *)
let _ = cake_theory "clos_interp"
  ["backend_common"; "closLang"];;

let _ = do_list hide_constant ["pmatch"];;

(* fits in subset *)

let can_interpret_op_def = new_definition
  `can_interpret_op x1 l =
      match x1 with
        closLang_BlockOp (closLang_Cons tag) -> (l = 0 \/ tag < 3)
      | (closLang_IntOp (closLang_Const i)) -> (l = 0)
      | (closLang_GlobOp (closLang_Global n)) -> (l = 0)
      | (closLang_BlockOp (closLang_Constant c)) -> (l = 0)
      | _1 -> F`;;

let can_interpret_def,can_interpret_ind = define_rec
  [`can_interpret ((closLang_Var t n):closLang_exp) = T`;
   `can_interpret (closLang_If t e1 e2 e3:closLang_exp) =
      (can_interpret e1 /\ can_interpret e2 /\ can_interpret e3)`;
   `can_interpret (closLang_Let t es e:closLang_exp) = (can_interpret
    e /\ can_interpret_list es)`;
   `can_interpret (closLang_Op t p es:closLang_exp) =
      (can_interpret_op p (LENGTH es) /\ can_interpret_list es)`;
   `can_interpret (closLang_Raise t e:closLang_exp) = can_interpret e`;
   `can_interpret (closLang_Tick t e:closLang_exp) = can_interpret e`;
   `can_interpret (closLang_Fn _2 _3 _4 _5 e) = F`;
   `can_interpret (closLang_Handle t e1 e2:closLang_exp) =
    (can_interpret e1 /\ can_interpret e2)`;
   `can_interpret (closLang_Call _9 _10 _11 es:closLang_exp) = F`;
   `can_interpret (closLang_App _13 opt e es:closLang_exp) =
      (IS_NONE opt /\ can_interpret e /\ can_interpret_list es /\
          LENGTH es = 1)`;
   `can_interpret (closLang_Letrec _17 _18 _19 fns e:closLang_exp) =
    F`;
   `can_interpret_list [] = T`;
   `can_interpret_list (CONS x xs) = (can_interpret x /\
    can_interpret_list xs)`];;

(* check size *)

let check_size_op_def = new_definition
  `check_size_op k x2 l =
      match x2 with
        closLang_BlockOp (closLang_Cons tag) -> (if l = (0:num) then
          k else k - (1:num))
      | (closLang_IntOp (closLang_Const i)) -> (k:num)
      | (closLang_GlobOp (closLang_Global n)) -> k
      | _20 -> k - 1`;;

let check_size_def,check_size_ind = define_rec
  [`check_size (k:num) ((closLang_Var t n):closLang_exp) = (k:num)`;
   `check_size (k:num) (closLang_If t e1 e2 e3:closLang_exp) =
      (((let k = check_size k e1 in if k = 0 then 0 else
         let k = check_size k e2 in if k = 0 then 0 else
           check_size k e3)):num)`;
   `check_size (k:num) (closLang_Let t es e:closLang_exp) =
      (((let k = check_size_list k es in if k = 0 then 0 else
         check_size k e)):num)`;
   `check_size (k:num) (closLang_Op t p es:closLang_exp) =
      (((let k = check_size_op k p (LENGTH es) in if k = 0 then 0
          else
         check_size_list k es)):num)`;
   `check_size (k:num) (closLang_Raise t e:closLang_exp) =
    ((check_size k e):num)`;
   `check_size (k:num) (closLang_Tick t e:closLang_exp) =
    ((check_size k e):num)`;
   `check_size (k:num) (closLang_Fn _21 _22 _23 _24 e) = ((k):num)`;
   `check_size (k:num) (closLang_Handle t e1 e2:closLang_exp) =
      (((let k = check_size k e1 in if k = 0 then 0 else
         check_size k e2)):num)`;
   `check_size (k:num) (closLang_Call _28 _29 _30 es:closLang_exp) =
    ((k):num)`;
   `check_size (k:num) (closLang_App _33 _34 e es:closLang_exp) =
      (((let k = check_size (k - 1) e in if k = 0 then 0 else
         check_size_list k es)):num)`;
   `check_size (k:num) (closLang_Letrec _38 _39 _40 fns
    e:closLang_exp) = ((k):num)`;
   `check_size_list (k:num) [] = k`;
   `check_size_list (k:num) (CONS x xs) =
      (let k = check_size k x in if k = 0 then 0 else
         check_size_list k xs)`];;

let nontrivial_size_def = new_definition
  `nontrivial_size e = (check_size 8 e = 0)`;;

(* convert to const *)

let to_constant_op_def = new_definition
  `to_constant_op x1 l cs =
      match x1 with
        closLang_IntOp (closLang_Const i) -> ConstCons 1 [ConstInt i]
      | (closLang_BlockOp (closLang_Constant c)) -> ConstCons 1 [c]
      | (closLang_GlobOp (closLang_Global n)) -> ConstCons 2
        [ConstInt (&n)]
      | (closLang_BlockOp (closLang_Cons tag)) ->
     (if l = 0 then ConstCons 1 [ConstCons tag []] else ConstCons
       (tag + 5) [cs])
      | _41 -> ConstInt (&0)`;;

let to_constant_def,to_constant_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`to_constant ((closLang_Var t n):closLang_exp) =
      ConstCons 0 [ConstInt (&n)]`;
   `to_constant (closLang_App _48 _49 e es:closLang_exp) =
      ConstCons 0 [to_constant e; match es with [] -> ConstInt
          (&0) | (CONS e1 _50) -> to_constant e1]`;
   `to_constant (closLang_If t e1 e2 e3:closLang_exp) =
      ConstCons 0 [to_constant e1; to_constant e2; to_constant
          e3]`;
   `to_constant (closLang_Let t es e:closLang_exp) = ConstCons 1
    [to_constant_list es; to_constant e]`;
   `to_constant (closLang_Op t p es:closLang_exp) = to_constant_op p
    (LENGTH es) (to_constant_list es)`;
   `to_constant (closLang_Raise t e:closLang_exp) = ConstCons 3
    [to_constant e]`;
   `to_constant (closLang_Tick t e:closLang_exp) = ConstCons 4
    [to_constant e]`;
   `to_constant (closLang_Handle t e1 e2:closLang_exp) = ConstCons 2
    [to_constant e1; to_constant e2]`;
   `to_constant (closLang_Fn _51 _52 _53 _54 e) = ConstInt (&0)`;
   `to_constant (closLang_Call _58 _59 _60 es:closLang_exp) =
    ConstInt (&0)`;
   `to_constant (closLang_Letrec _64 _65 _66 fns e:closLang_exp) =
    ConstInt (&0)`;
   `to_constant_list [] = ConstCons 0 []`;
   `to_constant_list (CONS x xs) = ConstCons 0 [to_constant x;
    to_constant_list xs]`];;

(* interpreter as closLang program *)

(* HOL4 clos_interpScript.sml:119: the overload V, which the port
   expands *)

(* HOL4 clos_interpScript.sml:121: the overload IsCase, which the
   port expands *)

(* HOL4 clos_interpScript.sml:123: the overload GetEl, which the port
   expands *)

(* HOL4 clos_interpScript.sml:125-127: the overload CallInterp, which
   the port expands *)

(* HOL4 clos_interpScript.sml:129-131: the overload CallInterpList,
   which the port expands *)

let clos_interp_el_def = new_definition
  `clos_interp_el =
     closLang_If backend_common_None (closLang_Op backend_common_None
       (closLang_BlockOp (closLang_EqualConst (closLang_Int (&0))))
       [(closLang_Var backend_common_None) 1])
       ((\n x. closLang_Op backend_common_None (closLang_BlockOp
         (closLang_ElemAt n)) [x]) 0 ((closLang_Var backend_common_None)
         0))
     (closLang_App backend_common_None NONE (closLang_App
       backend_common_None NONE ((closLang_Var backend_common_None) 2)
       [closLang_Op backend_common_None (closLang_IntOp
         closLang_Sub) [closLang_Op backend_common_None
         (closLang_IntOp (closLang_Const (&1))) []; (closLang_Var
         backend_common_None) 1]]) [(\n x. closLang_Op
         backend_common_None (closLang_BlockOp (closLang_ElemAt n))
         [x]) 1 ((closLang_Var backend_common_None) 0)])`;;

let clos_interp_rev_def = new_definition
  `clos_interp_rev =
     closLang_If backend_common_None (closLang_Op backend_common_None
       (closLang_BlockOp (closLang_LenEq 0)) [(closLang_Var
       backend_common_None) 1])
       ((closLang_Var backend_common_None) 0)
     (closLang_App backend_common_None NONE (closLang_App
       backend_common_None NONE ((closLang_Var backend_common_None) 2)
       [(\n x. closLang_Op backend_common_None (closLang_BlockOp
         (closLang_ElemAt n)) [x]) 1 ((closLang_Var
         backend_common_None) 1)]) [closLang_Op backend_common_None
         (closLang_BlockOp (closLang_Cons 0)) [(closLang_Var
         backend_common_None) 0; (\n x. closLang_Op
         backend_common_None (closLang_BlockOp (closLang_ElemAt n))
         [x]) 0 ((closLang_Var backend_common_None) 1)]])`;;

let clos_interpreter_body_def = new_definition
  `clos_interpreter_body =
       closLang_If backend_common_None ((closLang_Var
         backend_common_None) 1)
         (
          // is _list version
          closLang_If backend_common_None (closLang_Op
            backend_common_None (closLang_BlockOp (closLang_LenEq 0))
            [(closLang_Var backend_common_None) 0]) ((closLang_Var
            backend_common_None) 0) (
            closLang_Let backend_common_None [(\env x. closLang_App
              backend_common_None NONE (closLang_App backend_common_None
              NONE (closLang_App backend_common_None NONE (closLang_Op
              backend_common_None (closLang_GlobOp (closLang_Global 0))
              [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0));
                      (\env x. closLang_App backend_common_None NONE
                        (closLang_App backend_common_None NONE
                        (closLang_App backend_common_None NONE
                        (closLang_Op backend_common_None
                        (closLang_GlobOp (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 1)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 1 ((closLang_Var
               backend_common_None) 0))]
              (closLang_Op backend_common_None (closLang_BlockOp
                (closLang_Cons 0)) [(closLang_Var backend_common_None)
                1; (closLang_Var backend_common_None) 0]))) (
       // normal cases
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 0 2
         (
          // App
          closLang_App backend_common_None NONE ((\env x.
            closLang_App backend_common_None NONE (closLang_App
            backend_common_None NONE (closLang_App backend_common_None
            NONE (closLang_Op backend_common_None (closLang_GlobOp
            (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0)))
                        [(\env x. closLang_App backend_common_None
                          NONE (closLang_App backend_common_None NONE
                          (closLang_App backend_common_None NONE
                          (closLang_Op backend_common_None
                          (closLang_GlobOp (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 1 ((closLang_Var
               backend_common_None) 0))]) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 1 1
         (
          // Constant
          (\n x. closLang_Op backend_common_None (closLang_BlockOp
            (closLang_ElemAt n)) [x]) 0 ((closLang_Var
            backend_common_None) 0)) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 2 1
         (
          // Global
          closLang_Op backend_common_None (closLang_GlobOp
            (closLang_Global 0)) [(\n x. closLang_Op backend_common_None
            (closLang_BlockOp (closLang_ElemAt n)) [x]) 0 ((closLang_Var
            backend_common_None) 0)]) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 0 1
         (
          // Var
          closLang_Letrec [] NONE NONE
            [(1,closLang_Fn (implode "") NONE NONE 1 clos_interp_el)]
            (closLang_App backend_common_None NONE (closLang_App
              backend_common_None NONE ((closLang_Var
              backend_common_None) 0) [(\n x. closLang_Op
              backend_common_None (closLang_BlockOp (closLang_ElemAt n))
              [x]) 0 ((closLang_Var backend_common_None) 1)])
              [(closLang_Var backend_common_None) 3])) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 1 2
         (
          // Let
          closLang_Let backend_common_None [(\env x. closLang_App
            backend_common_None NONE (closLang_App backend_common_None
            NONE (closLang_App backend_common_None NONE (closLang_Op
            backend_common_None (closLang_GlobOp (closLang_Global 0))
            [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 1)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0))]
            ((\env x. closLang_App backend_common_None NONE
              (closLang_App backend_common_None NONE (closLang_App
              backend_common_None NONE (closLang_Op backend_common_None
              (closLang_GlobOp (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               (closLang_Op backend_common_None (closLang_BlockOp
               closLang_ListAppend) [(closLang_Var backend_common_None)
               3; (closLang_Var backend_common_None) 0]) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 1 ((closLang_Var
               backend_common_None) 1)))) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 2 2
         (
          // Handle
          closLang_Handle backend_common_None ((\env x. closLang_App
            backend_common_None NONE (closLang_App backend_common_None
            NONE (closLang_App backend_common_None NONE (closLang_Op
            backend_common_None (closLang_GlobOp (closLang_Global 0))
            [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0)))
            ((\env x. closLang_App backend_common_None NONE
              (closLang_App backend_common_None NONE (closLang_App
              backend_common_None NONE (closLang_Op backend_common_None
              (closLang_GlobOp (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               (closLang_Op backend_common_None (closLang_BlockOp
               (closLang_Cons 0)) [(closLang_Var backend_common_None) 3;
               (closLang_Var backend_common_None) 0]) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 1 ((closLang_Var
               backend_common_None) 1)))) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 0 3
         (
          // If
          closLang_If backend_common_None ((\env x. closLang_App
            backend_common_None NONE (closLang_App backend_common_None
            NONE (closLang_App backend_common_None NONE (closLang_Op
            backend_common_None (closLang_GlobOp (closLang_Global 0))
            [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0)))
                  ((\env x. closLang_App backend_common_None NONE
                    (closLang_App backend_common_None NONE (closLang_App
                    backend_common_None NONE (closLang_Op
                    backend_common_None (closLang_GlobOp
                    (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 1 ((closLang_Var
               backend_common_None) 0)))
                  ((\env x. closLang_App backend_common_None NONE
                    (closLang_App backend_common_None NONE (closLang_App
                    backend_common_None NONE (closLang_Op
                    backend_common_None (closLang_GlobOp
                    (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 2 ((closLang_Var
               backend_common_None) 0)))) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 3 1
         (
          // Raise
          closLang_Raise backend_common_None ((\env x. closLang_App
            backend_common_None NONE (closLang_App backend_common_None
            NONE (closLang_App backend_common_None NONE (closLang_Op
            backend_common_None (closLang_GlobOp (closLang_Global 0))
            [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0)))) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 4 1
         (
          // Tick
          (\env x. closLang_App backend_common_None NONE
            (closLang_App backend_common_None NONE (closLang_App
            backend_common_None NONE (closLang_Op backend_common_None
            (closLang_GlobOp (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0))) (
       // Cons for non-empty payload
       closLang_Let backend_common_None [(\env x. closLang_App
         backend_common_None NONE (closLang_App backend_common_None NONE
         (closLang_App backend_common_None NONE (closLang_Op
         backend_common_None (closLang_GlobOp (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 1)) []]) [x])
               ((closLang_Var backend_common_None) 2) ((\n x.
               closLang_Op backend_common_None (closLang_BlockOp
               (closLang_ElemAt n)) [x]) 0 ((closLang_Var
               backend_common_None) 0))] (
       closLang_Letrec [] NONE NONE
         [(1,closLang_Fn (implode "") NONE NONE 1 clos_interp_rev)] (
       closLang_Let backend_common_None [closLang_App
         backend_common_None NONE (closLang_App backend_common_None NONE
         ((closLang_Var backend_common_None) 0) [(closLang_Var
         backend_common_None) 1]) [closLang_Op backend_common_None
         (closLang_BlockOp (closLang_Cons 0)) []]] (
       closLang_Let backend_common_None [(closLang_Var
         backend_common_None) 3] (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 5 1 (
            // Cons 0
            closLang_Op backend_common_None (closLang_BlockOp
              (closLang_FromList 0)) [(closLang_Var backend_common_None)
              1]) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 6 1 (
            // Cons 1
            closLang_Op backend_common_None (closLang_BlockOp
              (closLang_FromList 1)) [(closLang_Var backend_common_None)
              1]) (
       (\tag len. closLang_If backend_common_None (closLang_Op
         backend_common_None (closLang_BlockOp (closLang_TagLenEq tag
         len)) [(closLang_Var backend_common_None) 0])) 7 1 (
            // Cons 2
            closLang_Op backend_common_None (closLang_BlockOp
              (closLang_FromList 2)) [(closLang_Var backend_common_None)
              1])
       (closLang_Op backend_common_None (closLang_BlockOp
         (closLang_Cons 0)) [])))))))))))))))))`;;

let clos_interpreter_def = new_definition
  `clos_interpreter =
     closLang_Fn (implode "env") NONE NONE 1 (
     closLang_Fn (implode "exp") NONE NONE 1
       clos_interpreter_body)`;;

(* functions that insert calls to interpreter *)

let opt_interp_def = new_definition
  `opt_interp e =
     (if can_interpret e /\ nontrivial_size e then
       SOME ((\env x. closLang_App backend_common_None NONE
         (closLang_App backend_common_None NONE (closLang_App
         backend_common_None NONE (closLang_Op backend_common_None
         (closLang_GlobOp (closLang_Global 0)) [])
             [env]) [closLang_Op backend_common_None
               (closLang_BlockOp (closLang_Cons 0)) []]) [x])
               (closLang_Op backend_common_None (closLang_BlockOp
               (closLang_Cons 0)) []) (closLang_Op
               backend_common_None (closLang_BlockOp
               (closLang_Constant (to_constant e))) [])) else NONE)`;;

let opt_interp1_def = new_definition
  `opt_interp1 e =
     (match opt_interp e with SOME x -> x | NONE -> e)`;;

let insert_interp1_def = new_definition
  `insert_interp1 e =
     (match opt_interp e with SOME x -> x | NONE ->
         (match e with closLang_Let t ys y -> closLang_Let
           backend_common_None (MAP opt_interp1 ys) y | _67 -> e))`;;

let compile_init_def = new_definition
  `compile_init b =
     closLang_Let backend_common_None [closLang_Op
       backend_common_None (closLang_GlobOp closLang_AllocGlobal)
       [closLang_Op backend_common_None (closLang_IntOp (closLang_Const
       (&1))) []];
               if b then
                 closLang_Fn (implode "clos_interpreter") NONE NONE 1
                   clos_interpreter else
                 closLang_Op backend_common_None (closLang_BlockOp
                   (closLang_Cons 0)) []]
       (closLang_Op backend_common_None (closLang_GlobOp
         (closLang_SetGlobal 0)) [closLang_Var backend_common_None
         1])`;;

let attach_interpreter_def = new_definition
  `attach_interpreter xs = CONS (compile_init (has_install_list xs))
  xs`;;

let insert_interp_def = new_definition
  `insert_interp xs = MAP insert_interp1 xs`;;

(* pmatch versions of the op-functions *)

let can_interpret_op_pmatch = prove
 (`can_interpret_op p l =
     (match p with closLang_BlockOp (closLang_Cons tag) -> (l = 0
       \/ tag < 3) | closLang_IntOp (closLang_Const i) -> (l = 0) |
       closLang_GlobOp (closLang_Global n) -> (l = 0) |
       closLang_BlockOp (closLang_Constant c) -> (l = 0) | _68 -> F)`,
  CHEAT_TAC);;

let check_size_op_pmatch = prove
 (`check_size_op k p l =
     (match p with closLang_BlockOp (closLang_Cons tag) -> (if l =
       (0:num) then k else k - (1:num)) | closLang_IntOp
       (closLang_Const i) -> k | closLang_GlobOp (closLang_Global n)
       -> k | _69 -> k - 1)`,
  CHEAT_TAC);;

let to_constant_op_pmatch = prove
 (`to_constant_op p l cs =
     (match p with closLang_IntOp (closLang_Const i) -> ConstCons 1
       [ConstInt i] | closLang_BlockOp (closLang_Constant c) ->
       ConstCons 1 [c] | closLang_GlobOp (closLang_Global n) ->
       ConstCons 2 [ConstInt (&n)] | closLang_BlockOp (closLang_Cons
       tag) -> (if l = 0 then ConstCons 1 [ConstCons tag []] else
       ConstCons (tag + 5) [cs]) | _70 -> ConstInt (&0))`,
  CHEAT_TAC);;

(* and the names it reads as variables are constants again *)
let _ = do_list unhide_constant
  ["pmatch"];;
