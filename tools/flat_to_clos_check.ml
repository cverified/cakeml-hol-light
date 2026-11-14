let var_fun m n =
  list_mk_icomb "clos_Var" [`t:tra`; mk_small_numeral (m - n)];;

let check1 tm var =
  vsubst [var 2,`v2:clos_exp`; var 1,`v1:clos_exp`;
          var 0,`v0:clos_exp`; tm,`tm:clos_exp`]
  `clos_If t
     (clos_Op t (clos_IntOp clos_Less)
        [clos_Op t (clos_IntOp (clos_Const (&0))) [];
         v2])
     (clos_Raise t (clos_Op t
        (clos_BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t
       (clos_Op t (clos_IntOp clos_Less)
          [clos_Op t (clos_IntOp (clos_Const (&0))) [];
           v1])
       (clos_Raise t (clos_Op t
          (clos_BlockOp (clos_Cons subscript_tag)) []))
       (clos_If t
         (clos_Op t (clos_MemOp (clos_BoundsCheckByte T))
            [clos_Op t (clos_IntOp clos_Add) [v2; v1];
             v0])
         tm
         (clos_Raise t (clos_Op t
            (clos_BlockOp (clos_Cons subscript_tag))
            []))))`;;

let checkT =
  check1 `clos_Op t (clos_MemOp (clos_CopyByte T))
            [clos_Var t 0; clos_Var t 1; clos_Var t 2]`
         (var_fun 2);;

let checkF =
  check1
  `clos_If t
     (clos_Op t (clos_IntOp clos_Less)
        [clos_Op t (clos_IntOp (clos_Const (&0))) [];
         clos_Var t 0])
     (clos_Raise t (clos_Op t
        (clos_BlockOp (clos_Cons subscript_tag)) []))
     (clos_If t
       (clos_Op t (clos_MemOp (clos_BoundsCheckByte T))
          [clos_Op t (clos_IntOp clos_Add)
             [clos_Var t 2; clos_Var t 0];
           clos_Var t 1])
       (clos_Op t (clos_MemOp (clos_CopyByte F))
          [clos_Var t 0; clos_Var t 1; clos_Var t 2;
           clos_Var t 3; clos_Var t 4])
       (clos_Raise t (clos_Op t
          (clos_BlockOp (clos_Cons subscript_tag)) [])))`
  (var_fun 4);;
