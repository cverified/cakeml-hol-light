let var_fun m n =
  list_mk_icomb "closLang_Var" [`t:tra`; mk_small_numeral (m - n)];;

let check1 tm var =
  vsubst [var 2,`v2:closLang_exp`; var 1,`v1:closLang_exp`;
          var 0,`v0:closLang_exp`; tm,`tm:closLang_exp`]
  `closLang_If t
     (closLang_Op t (closLang_IntOp closLang_Less)
        [closLang_Op t (closLang_IntOp (closLang_Const (&0))) [];
         v2])
     (closLang_Raise t (closLang_Op t
        (closLang_BlockOp (closLang_Cons subscript_tag)) []))
     (closLang_If t
       (closLang_Op t (closLang_IntOp closLang_Less)
          [closLang_Op t (closLang_IntOp (closLang_Const (&0))) [];
           v1])
       (closLang_Raise t (closLang_Op t
          (closLang_BlockOp (closLang_Cons subscript_tag)) []))
       (closLang_If t
         (closLang_Op t (closLang_MemOp (closLang_BoundsCheckByte T))
            [closLang_Op t (closLang_IntOp closLang_Add) [v2; v1];
             v0])
         tm
         (closLang_Raise t (closLang_Op t
            (closLang_BlockOp (closLang_Cons subscript_tag))
            []))))`;;

let checkT =
  check1 `closLang_Op t (closLang_MemOp (closLang_CopyByte T))
            [closLang_Var t 0; closLang_Var t 1; closLang_Var t 2]`
         (var_fun 2);;

let checkF =
  check1
  `closLang_If t
     (closLang_Op t (closLang_IntOp closLang_Less)
        [closLang_Op t (closLang_IntOp (closLang_Const (&0))) [];
         closLang_Var t 0])
     (closLang_Raise t (closLang_Op t
        (closLang_BlockOp (closLang_Cons subscript_tag)) []))
     (closLang_If t
       (closLang_Op t (closLang_MemOp (closLang_BoundsCheckByte T))
          [closLang_Op t (closLang_IntOp closLang_Add)
             [closLang_Var t 2; closLang_Var t 0];
           closLang_Var t 1])
       (closLang_Op t (closLang_MemOp (closLang_CopyByte F))
          [closLang_Var t 0; closLang_Var t 1; closLang_Var t 2;
           closLang_Var t 3; closLang_Var t 4])
       (closLang_Raise t (closLang_Op t
          (closLang_BlockOp (closLang_Cons subscript_tag)) [])))`
  (var_fun 4);;
