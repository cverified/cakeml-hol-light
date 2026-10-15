(* ======================================================== *)
(*  clos_interp: ported from HOL4's
    compiler/backend/clos_interpScript.sml  *)
(* ======================================================== *)

(*
  Implementation of interpreter for closLang expressions written in
    closLang.
*)

needs "basis/pure/mlstring.ml";;
needs "compiler/backend/backend_common.ml";;
needs "compiler/backend/closLang.ml";;
needs "semantics/ast.ml";;

(* fits in subset *)

let can_interpret_op_def = cake_define
  `can_interpret_op x1 l =
      match x1 with
        BlockOp (Cons tag) -> (l = 0 \/ tag < 3)
      | (IntOp (Const i)) -> (l = 0)
      | (GlobOp (Global n)) -> (l = 0)
      | (BlockOp (Constant c)) -> (l = 0)
      | _1 -> F`;;

let can_interpret_def = cake_define_list
  [`can_interpret ((Var t n):closLang_exp) = T`;
   `can_interpret (If t e1 e2 e3:closLang_exp) =
      (can_interpret e1 /\ can_interpret e2 /\ can_interpret e3)`;
   `can_interpret (Let t es e:closLang_exp) = (can_interpret e /\
  can_interpret_list es)`;
   `can_interpret (Op t p es:closLang_exp) =
      (can_interpret_op p (LENGTH es) /\ can_interpret_list es)`;
   `can_interpret (Raise t e:closLang_exp) = can_interpret e`;
   `can_interpret (Tick t e:closLang_exp) = can_interpret e`;
   `can_interpret (Fn _2 _3 _4 _5 e:closLang_exp) = F`;
   `can_interpret (Handle t e1 e2:closLang_exp) = (can_interpret e1
  /\ can_interpret e2)`;
   `can_interpret (Call _6 _7 _8 es:closLang_exp) = F`;
   `can_interpret (App _9 opt e es:closLang_exp) =
      (IS_NONE opt /\ can_interpret e /\ can_interpret_list es /\
        LENGTH es = 1)`;
   `can_interpret (Letrec _10 _11 _12 fns e:closLang_exp) = F`;
   `can_interpret_list [] = T`;
   `can_interpret_list (x :: xs) = (can_interpret x /\
  can_interpret_list xs)`];;

(* check size *)

let check_size_op_def = cake_define
  `check_size_op k x2 l =
      match x2 with
        BlockOp (Cons tag) -> (if l = (0:num) then k else k -
          (1:num))
      | (IntOp (Const i)) -> (k:num)
      | (GlobOp (Global n)) -> k
      | _13 -> k - 1`;;

let check_size_def = cake_define_list
  [`check_size k ((Var t n):closLang_exp) = (k:num)`;
   `check_size k (If t e1 e2 e3:closLang_exp) =
      (let k = check_size k e1 in if k = 0 then 0 else
         let k = check_size k e2 in if k = 0 then 0 else
           check_size k e3)`;
   `check_size k (Let t es e:closLang_exp) =
      (let k = check_size_list k es in if k = 0 then 0 else
         check_size k e)`;
   `check_size k (Op t p es:closLang_exp) =
      (let k = check_size_op k p (LENGTH es) in if k = 0 then 0 else
         check_size_list k es)`;
   `check_size k (Raise t e:closLang_exp) = check_size k e`;
   `check_size k (Tick t e:closLang_exp) = check_size k e`;
   `check_size k (Fn _14 _15 _16 _17 e:closLang_exp) = k`;
   `check_size k (Handle t e1 e2:closLang_exp) =
      (let k = check_size k e1 in if k = 0 then 0 else
         check_size k e2)`;
   `check_size k (Call _18 _19 _20 es:closLang_exp) = k`;
   `check_size k (App _21 _22 e es:closLang_exp) =
      (let k = check_size (k - 1) e in if k = 0 then 0 else
         check_size_list k es)`;
   `check_size k (Letrec _23 _24 _25 fns e:closLang_exp) = k`;
   `check_size_list k [] = k`;
   `check_size_list k (x :: xs) =
      (let k = check_size k x in if k = 0 then 0 else
         check_size_list k xs)`];;

let nontrivial_size_def = cake_define
  `nontrivial_size e = (check_size 8 e = 0)`;;

(* convert to const *)

let to_constant_op_def = cake_define
  `to_constant_op x1 l cs =
      match x1 with
        IntOp (Const i) -> ConstCons 1 [ConstInt i]
      | (BlockOp (Constant c)) -> ConstCons 1 [c]
      | (GlobOp (Global n)) -> ConstCons 2 [ConstInt (&n)]
      | (BlockOp (Cons tag)) ->
     (if l = 0 then ConstCons 1 [ConstCons tag []] else ConstCons
       (tag + 5) [cs])
      | _26 -> ConstInt (&0)`;;

let to_constant_def = cake_define_list
  [`to_constant ((Var t n):closLang_exp) =
      ConstCons 0 [ConstInt (&n)]`;
   `to_constant (App _27 _28 e es:closLang_exp) =
      ConstCons 0 [to_constant e; match es with [] -> ConstInt
        (&0) | (e1 :: _29) -> to_constant e1]`;
   `to_constant (If t e1 e2 e3:closLang_exp) =
      ConstCons 0 [to_constant e1; to_constant e2; to_constant
        e3]`;
   `to_constant (Let t es e:closLang_exp) = ConstCons 1
  [to_constant_list es; to_constant e]`;
   `to_constant (Op t p es:closLang_exp) = to_constant_op p (LENGTH
  es) (to_constant_list es)`;
   `to_constant (Raise t e:closLang_exp) = ConstCons 3 [to_constant
  e]`;
   `to_constant (Tick t e:closLang_exp) = ConstCons 4 [to_constant e]`;
   `to_constant (Handle t e1 e2:closLang_exp) = ConstCons 2
  [to_constant e1; to_constant e2]`;
   `to_constant (Fn _30 _31 _32 _33 e:closLang_exp) = ConstInt (&0)`;
   `to_constant (Call _34 _35 _36 es:closLang_exp) = ConstInt (&0)`;
   `to_constant (Letrec _37 _38 _39 fns e:closLang_exp) = ConstInt
  (&0)`;
   `to_constant_list [] = ConstCons 0 []`;
   `to_constant_list (x :: xs) = ConstCons 0 [to_constant x;
  to_constant_list xs]`];;

(* interpreter as closLang program *)

(* HOL4 overload (expanded in the port):
     V = Var None *)

(* HOL4 overload (expanded in the port):
     IsCase = λtag len. If None (Op None (BlockOp (TagLenEq tag len)) [V
       0]) *)

(* HOL4 overload (expanded in the port):
     GetEl = λn x. Op None (BlockOp (ElemAt n)) [x] *)

(* HOL4 overload (expanded in the port):
     CallInterp = λenv x. App None NONE (App None NONE (App None NONE
       (Op None (GlobOp (Global 0)) [])
            [env]) [Op None (BlockOp (Cons 0)) []]) [x] *)

(* HOL4 overload (expanded in the port):
     CallInterpList = λenv x. App None NONE (App None NONE (App None
       NONE (Op None (GlobOp (Global 0)) [])
            [env]) [Op None (BlockOp (Cons 1)) []]) [x] *)

let clos_interp_el_def = cake_define
  `clos_interp_el =
     If None (Op None (BlockOp (EqualConst (Int (&0)))) [(Var None)
       1])
       ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var None) 0))
     (App None NONE (App None NONE ((Var None) 2)
       [Op None (IntOp Sub) [Op None (IntOp (Const (&1))) []; (Var
         None) 1]]) [(\n x. Op None (BlockOp (ElemAt n)) [x]) 1 ((Var
         None) 0)])`;;

let clos_interp_rev_def = cake_define
  `clos_interp_rev =
     If None (Op None (BlockOp (LenEq 0)) [(Var None) 1])
       ((Var None) 0)
     (App None NONE (App None NONE ((Var None) 2)
       [(\n x. Op None (BlockOp (ElemAt n)) [x]) 1 ((Var None)
         1)]) [Op None (BlockOp (Cons 0)) [(Var None) 0; (\n x. Op
         None (BlockOp (ElemAt n)) [x]) 0 ((Var None) 1)]])`;;

let clos_interpreter_body_def = cake_define
  `clos_interpreter_body =
       If None ((Var None) 1)
         (If None (Op None (BlockOp (LenEq 0)) [(Var None) 0]) ((Var
           None) 0) (
            Let None [(\env x. App None NONE (App None NONE (App None
              NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0));
                      (\env x. App None NONE (App None NONE (App None
                        NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 1)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 1 ((Var
               None) 0))]
              (Op None (BlockOp (Cons 0)) [(Var None) 1; (Var None)
                0]))) (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 0 2
         (App None NONE ((\env x. App None NONE (App None NONE (App
           None NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0)))
                        [(\env x. App None NONE (App None NONE (App
                          None NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 1 ((Var
               None) 0))]) (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 1 1
         ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var None) 0))
           (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 2 1
         (Op None (GlobOp (Global 0)) [(\n x. Op None (BlockOp
           (ElemAt n)) [x]) 0 ((Var None) 0)]) (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 0 1
         (Letrec [] NONE NONE
            [(1,Fn (implode "") NONE NONE 1 clos_interp_el)]
            (App None NONE (App None NONE ((Var None) 0) [(\n x. Op
              None (BlockOp (ElemAt n)) [x]) 0 ((Var None) 1)]) [(Var
              None) 3])) (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 1 2
         (Let None [(\env x. App None NONE (App None NONE (App None
           NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 1)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0))]
            ((\env x. App None NONE (App None NONE (App None NONE (Op
              None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) (Op None
               (BlockOp ListAppend) [(Var None) 3; (Var None) 0]) ((\n
               x. Op None (BlockOp (ElemAt n)) [x]) 1 ((Var None) 1))))
               (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 2 2
         (Handle None ((\env x. App None NONE (App None NONE (App
           None NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0)))
            ((\env x. App None NONE (App None NONE (App None NONE (Op
              None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) (Op None
               (BlockOp (Cons 0)) [(Var None) 3; (Var None) 0]) ((\n x.
               Op None (BlockOp (ElemAt n)) [x]) 1 ((Var None) 1)))) (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 0 3
         (If None ((\env x. App None NONE (App None NONE (App None
           NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0)))
                  ((\env x. App None NONE (App None NONE (App None
                    NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 1 ((Var
               None) 0)))
                  ((\env x. App None NONE (App None NONE (App None
                    NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 2 ((Var
               None) 0)))) (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 3 1
         (Raise None ((\env x. App None NONE (App None NONE (App None
           NONE (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0)))) (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 4 1
         ((\env x. App None NONE (App None NONE (App None NONE (Op
           None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0))) (
       Let None [(\env x. App None NONE (App None NONE (App None NONE
         (Op None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 1)) []]) [x]) ((Var None)
               2) ((\n x. Op None (BlockOp (ElemAt n)) [x]) 0 ((Var
               None) 0))] (
       Letrec [] NONE NONE
         [(1,Fn (implode "") NONE NONE 1 clos_interp_rev)] (
       Let None [App None NONE (App None NONE ((Var None) 0) [(Var
         None) 1]) [Op None (BlockOp (Cons 0)) []]] (
       Let None [(Var None) 3] (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 5 1 (Op None (BlockOp (FromList 0)) [(Var None) 1])
         (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 6 1 (Op None (BlockOp (FromList 1)) [(Var None) 1])
         (
       (\tag len. If None (Op None (BlockOp (TagLenEq tag len)) [(Var
         None) 0])) 7 1 (Op None (BlockOp (FromList 2)) [(Var None) 1])
       (Op None (BlockOp (Cons 0)) [])))))))))))))))))`;;

let clos_interpreter_def = cake_define
  `clos_interpreter =
     Fn (implode "env") NONE NONE 1 (
     Fn (implode "exp") NONE NONE 1
       clos_interpreter_body)`;;

(* functions that insert calls to interpreter *)

let opt_interp_def = cake_define
  `opt_interp e =
     (if can_interpret e /\ nontrivial_size e then
       SOME ((\env x. App None NONE (App None NONE (App None NONE (Op
         None (GlobOp (Global 0)) [])
             [env]) [Op None (BlockOp (Cons 0)) []]) [x]) (Op None
               (BlockOp (Cons 0)) []) (Op None (BlockOp (Constant
               (to_constant e))) [])) else NONE)`;;

let opt_interp1_def = cake_define
  `opt_interp1 e =
     (match opt_interp e with SOME x -> x | NONE -> e)`;;

let insert_interp1_def = cake_define
  `insert_interp1 e =
     (match opt_interp e with SOME x -> x | NONE ->
         (match e with Let t ys y -> Let None (MAP opt_interp1 ys)
           y | _40 -> e))`;;

let compile_init_def = cake_define
  `compile_init b =
     Let None [Op None (GlobOp AllocGlobal) [Op None (IntOp (Const
       (&1))) []];
               if b then
                 Fn (implode "clos_interpreter") NONE NONE 1
                   clos_interpreter else
                 Op None (BlockOp (Cons 0)) []]
       (Op None (GlobOp (SetGlobal 0)) [Var None 1])`;;

let attach_interpreter_def = cake_define
  `attach_interpreter xs =
     compile_init (has_install_list xs) :: xs`;;

let insert_interp_def = cake_define
  `insert_interp xs = MAP insert_interp1 xs`;;

(* pmatch versions of the op-functions *)
