(* ======================================================== *)
(*  bvl_inline: ported from HOL4's
    compiler/backend/bvl_inlineScript.sml  *)
(* ======================================================== *)

(*
  A simple function-inlining optimisation within the BVL language.
  There is a more advanced inlining optimisation as part of
  clos_known.
*)

needs "compiler/backend/bvl.ml";;
needs "compiler/backend/bvl_handle.ml";;

(* tick_inline -- a function that inlines a function body *)

let tick_inline_def = cake_define
  `(tick_inline cs [] = []) /\
   (tick_inline cs (x :: y :: xs) =
      HD (tick_inline cs [x]) :: tick_inline cs (y :: xs)) /\
   (tick_inline cs [db_vars_Var v] = [db_vars_Var v]) /\
   (tick_inline cs [bvl_If x1 x2 x3] =
      [bvl_If (HD (tick_inline cs [x1]))
          (HD (tick_inline cs [x2]))
          (HD (tick_inline cs [x3]))]) /\
   (tick_inline cs [bvl_Let xs x2] =
      [bvl_Let (tick_inline cs xs)
            (HD (tick_inline cs [x2]))]) /\
   (tick_inline cs [bvl_Raise x1] =
      [bvl_Raise (HD (tick_inline cs [x1]))]) /\
   (tick_inline cs [bvl_Handle x1 x2] =
      [bvl_Handle (HD (tick_inline cs [x1]))
              (HD (tick_inline cs [x2]))]) /\
   (tick_inline cs [bvl_Op closLang_op xs] =
      [bvl_Op closLang_op (tick_inline cs xs)]) /\
   (tick_inline cs [bvl_Tick x] =
      [bvl_Tick (HD (tick_inline cs [x]))]) /\
   (tick_inline cs [bvl_Force m n] = [bvl_Force m n]) /\
   (tick_inline cs [bvl_Call ticks dest xs] =
      (match dest with NONE -> [bvl_Call ticks dest (tick_inline cs
        xs)] | SOME n ->
      (match sptree_lookup n cs with NONE -> [bvl_Call ticks dest
        (tick_inline cs xs)] | SOME (arity,code) -> [bvl_Let
        (tick_inline cs xs) (mk_tick (SUC ticks) code)])))`;;

let tick_inline_sing_def = cake_define
  `(tick_inline_sing cs (db_vars_Var v) = db_vars_Var v) /\
   (tick_inline_sing cs (bvl_If x1 x2 x3) =
      (bvl_If (tick_inline_sing cs x1)
          (tick_inline_sing cs x2)
          (tick_inline_sing cs x3))) /\
   (tick_inline_sing cs (bvl_Let xs x2) =
      (bvl_Let (tick_inline_list cs xs)
           (tick_inline_sing cs x2))) /\
   (tick_inline_sing cs (bvl_Raise x1) =
      (bvl_Raise (tick_inline_sing cs x1))) /\
   (tick_inline_sing cs (bvl_Handle x1 x2) =
      (bvl_Handle (tick_inline_sing cs x1)
              (tick_inline_sing cs x2))) /\
   (tick_inline_sing cs (bvl_Op closLang_op xs) =
      (bvl_Op closLang_op (tick_inline_list cs xs))) /\
   (tick_inline_sing cs (bvl_Tick x) =
      (bvl_Tick (tick_inline_sing cs x))) /\
   (tick_inline_sing cs (bvl_Force m n) = bvl_Force m n) /\
   (tick_inline_sing cs (bvl_Call ticks dest xs) =
      (match dest with NONE -> bvl_Call ticks dest (tick_inline_list
        cs xs) | SOME n ->
      (match sptree_lookup n cs with NONE -> bvl_Call ticks dest
        (tick_inline_list cs xs) | SOME (arity,code) ->
          bvl_Let (tick_inline_list cs xs) (mk_tick (SUC ticks)
            code)))) /\
   (tick_inline_list cs [] = []) /\
   (tick_inline_list cs (x :: xs) =
      (tick_inline_sing cs x) :: tick_inline_list cs xs)`;;

(* This definition is written to exit as soon as possible. *)
let is_small_aux_def = cake_define
  `(is_small_aux n [] = n) /\
   (is_small_aux n (x :: y :: xs) =
      (if n = 0 then n else
        let n = is_small_aux n [x] in if n = 0 then n else
          is_small_aux n (y :: xs))) /\
   (is_small_aux n [db_vars_Var v] = n) /\
   (is_small_aux n [bvl_If x1 x2 x3] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = is_small_aux n [x1] in if n = 0 then 0 else
      let n = is_small_aux n [x2] in if n = 0 then 0 else
        is_small_aux n [x3])) /\
   (is_small_aux n [bvl_Let xs x2] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = is_small_aux n xs in if n = 0 then 0 else
        is_small_aux n [x2])) /\
   (is_small_aux n [bvl_Raise x1] =
      (let n = n - 1 in if n = 0 then 0 else
        is_small_aux n [x1])) /\
   (is_small_aux n [bvl_Handle x1 x2] =
      (let n = n - 1 in if n = 0 then 0 else
      let n = is_small_aux n [x1] in if n = 0 then 0 else
        is_small_aux n [x2])) /\
   (is_small_aux n [bvl_Op closLang_op xs] =
      (let n = n - 1 in if n = 0 then 0 else
        is_small_aux n xs)) /\
   (is_small_aux n [bvl_Tick x] = is_small_aux n [x]) /\
   (is_small_aux n [bvl_Force _1 _2] = n) /\
   (is_small_aux n [bvl_Call ticks dest xs] =
      (let n = n - 1 in if n = 0 then 0 else
        is_small_aux n xs))`;;

let is_small_sing_def = cake_define
  `(is_small_sing n (db_vars_Var v) = n) /\
   (is_small_sing n (bvl_If x1 x2 x3) =
      (let n = n - 1 in if n = 0 then 0 else
      let n = is_small_sing n x1 in if n = 0 then 0 else
      let n = is_small_sing n x2 in if n = 0 then 0 else
        is_small_sing n x3)) /\
   (is_small_sing n (bvl_Let xs x2) =
      (let n = n - 1 in if n = 0 then 0 else
      let n = is_small_list n xs in if n = 0 then 0 else
        is_small_sing n x2)) /\
   (is_small_sing n (bvl_Raise x1) =
      (let n = n - 1 in if n = 0 then 0 else
        is_small_sing n x1)) /\
   (is_small_sing n (bvl_Handle x1 x2) =
      (let n = n - 1 in if n = 0 then 0 else
      let n = is_small_sing n x1 in if n = 0 then 0 else
        is_small_sing n x2)) /\
   (is_small_sing n (bvl_Op closLang_op xs) =
      (let n = n - 1 in if n = 0 then 0 else
        is_small_list n xs)) /\
   (is_small_sing n (bvl_Tick x) = is_small_sing n x) /\
   (is_small_sing n (bvl_Force _3 _4) = n) /\
   (is_small_sing n (bvl_Call ticks dest xs) =
      (let n = n - 1 in if n = 0 then 0 else
        is_small_list n xs)) /\
   (is_small_list n [] = n) /\
   (is_small_list n (x :: xs) =
      (if n = 0 then n else
        let n = is_small_sing n x in if n = 0 then n else
          is_small_list n xs))`;;

let is_small_def = cake_define
  `is_small limit e = ~(is_small_aux limit [e] = 0)`;;

let is_rec_def = cake_define
  `(bvl_inline_is_rec n [] = F) /\
   (bvl_inline_is_rec n (x :: y :: xs) =
      (if bvl_inline_is_rec n [x] then T else
        bvl_inline_is_rec n (y :: xs))) /\
   (bvl_inline_is_rec n [db_vars_Var v] = F) /\
   (bvl_inline_is_rec n [bvl_If x1 x2 x3] =
      (if bvl_inline_is_rec n [x1] then T else
      if bvl_inline_is_rec n [x2] then T else
        bvl_inline_is_rec n [x3])) /\
   (bvl_inline_is_rec n [bvl_Let xs x2] =
      (if bvl_inline_is_rec n xs then T else
        bvl_inline_is_rec n [x2])) /\
   (bvl_inline_is_rec n [bvl_Raise x1] = bvl_inline_is_rec n [x1]) /\
   (bvl_inline_is_rec n [bvl_Handle x1 x2] =
      (if bvl_inline_is_rec n [x1] then T else
        bvl_inline_is_rec n [x2])) /\
   (bvl_inline_is_rec n [bvl_Op closLang_op xs] = bvl_inline_is_rec n
     xs) /\
   (bvl_inline_is_rec n [bvl_Tick x] = bvl_inline_is_rec n [x]) /\
   (bvl_inline_is_rec n [bvl_Force _5 _6] = F) /\
   (bvl_inline_is_rec n [bvl_Call ticks dest xs] =
      (if dest = SOME n then T else bvl_inline_is_rec n xs))`;;

let is_rec_sing_def = cake_define
  `(is_rec_sing n (db_vars_Var v) = F) /\
   (is_rec_sing n (bvl_If x1 x2 x3) =
      (if is_rec_sing n x1 then T else
      if is_rec_sing n x2 then T else
        is_rec_sing n x3)) /\
   (is_rec_sing n (bvl_Let xs x2) =
      (if is_rec_list n xs then T else
        is_rec_sing n x2)) /\
   (is_rec_sing n (bvl_Raise x1) = is_rec_sing n x1) /\
   (is_rec_sing n (bvl_Handle x1 x2) =
      (if is_rec_sing n x1 then T else
        is_rec_sing n x2)) /\
   (is_rec_sing n (bvl_Op closLang_op xs) = is_rec_list n xs) /\
   (is_rec_sing n (bvl_Tick x) = is_rec_sing n x) /\
   (is_rec_sing n (bvl_Force _7 _8) = F) /\
   (is_rec_sing n (bvl_Call ticks dest xs) =
      (if dest = SOME n then T else is_rec_list n xs)) /\
   (is_rec_list n [] = F) /\
   (is_rec_list n (x :: xs) =
      (if is_rec_sing n x then T else
        is_rec_list n xs))`;;

let must_inline_def = cake_define
  `must_inline name limit e =
     (if is_small limit e then ~(bvl_inline_is_rec name [e]) else
       F)`;;

let tick_inline_all_def = cake_define
  `(tick_inline_all limit cs [] aux = (cs,REVERSE aux)) /\
   (tick_inline_all limit cs ((n,(arity:num),e1) :: xs) aux =
      (let e2 = HD (tick_inline cs [e1]) in
      let cs2 = if must_inline n limit e2 then sptree_insert n
        (arity,e2) cs else cs in
        tick_inline_all limit cs2 xs ((n,arity,e2) :: aux)))`;;

let tick_compile_prog_def = cake_define
  `tick_compile_prog limit cs prog = tick_inline_all limit cs prog []`;;

(* remove_ticks -- a function that removes Ticks *)

let remove_ticks_def = cake_define
  `(bvl_inline_remove_ticks [] = []) /\
   (bvl_inline_remove_ticks (x :: y :: xs) =
      HD (bvl_inline_remove_ticks [x]) :: bvl_inline_remove_ticks (y
        :: xs)) /\
   (bvl_inline_remove_ticks [db_vars_Var v] = [db_vars_Var v]) /\
   (bvl_inline_remove_ticks [bvl_If x1 x2 x3] =
      [bvl_If (HD (bvl_inline_remove_ticks [x1]))
          (HD (bvl_inline_remove_ticks [x2]))
          (HD (bvl_inline_remove_ticks [x3]))]) /\
   (bvl_inline_remove_ticks [bvl_Let xs x2] =
      [bvl_Let (bvl_inline_remove_ticks xs) (HD
        (bvl_inline_remove_ticks [x2]))]) /\
   (bvl_inline_remove_ticks [bvl_Raise x1] =
      [bvl_Raise (HD (bvl_inline_remove_ticks [x1]))]) /\
   (bvl_inline_remove_ticks [bvl_Handle x1 x2] =
      [bvl_Handle (HD (bvl_inline_remove_ticks [x1]))
              (HD (bvl_inline_remove_ticks [x2]))]) /\
   (bvl_inline_remove_ticks [bvl_Op closLang_op xs] =
      [bvl_Op closLang_op (bvl_inline_remove_ticks xs)]) /\
   (bvl_inline_remove_ticks [bvl_Tick x] = bvl_inline_remove_ticks
     [x]) /\
   (bvl_inline_remove_ticks [bvl_Force m n] = [bvl_Force m n]) /\
   (bvl_inline_remove_ticks [bvl_Call ticks dest xs] =
      [bvl_Call 0 dest (bvl_inline_remove_ticks xs)])`;;

let remove_ticks_sing_def = cake_define
  `(bvl_inline_remove_ticks_sing (db_vars_Var v) = db_vars_Var v) /\
   (bvl_inline_remove_ticks_sing (bvl_If x1 x2 x3) =
      bvl_If (bvl_inline_remove_ticks_sing x1)
         (bvl_inline_remove_ticks_sing x2)
         (bvl_inline_remove_ticks_sing x3)) /\
   (bvl_inline_remove_ticks_sing (bvl_Let xs x2) =
      bvl_Let (bvl_inline_remove_ticks_list xs)
        (bvl_inline_remove_ticks_sing x2)) /\
   (bvl_inline_remove_ticks_sing (bvl_Raise x1) =
      bvl_Raise (bvl_inline_remove_ticks_sing x1)) /\
   (bvl_inline_remove_ticks_sing (bvl_Handle x1 x2) =
      bvl_Handle (bvl_inline_remove_ticks_sing x1)
             (bvl_inline_remove_ticks_sing x2)) /\
   (bvl_inline_remove_ticks_sing (bvl_Op closLang_op xs) =
      bvl_Op closLang_op (bvl_inline_remove_ticks_list xs)) /\
   (bvl_inline_remove_ticks_sing (bvl_Tick x) =
     bvl_inline_remove_ticks_sing x) /\
   (bvl_inline_remove_ticks_sing (bvl_Force m n) = bvl_Force m n) /\
   (bvl_inline_remove_ticks_sing (bvl_Call ticks dest xs) =
      bvl_Call 0 dest (bvl_inline_remove_ticks_list xs)) /\
   (bvl_inline_remove_ticks_list [] = []) /\
   (bvl_inline_remove_ticks_list (x :: xs) =
      (bvl_inline_remove_ticks_sing x) ::
        bvl_inline_remove_ticks_list xs)`;;

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

let var_list_def = cake_define
  `bvl_inline_var_list n x2 x3 =
      match (x2,x3) with
        ([],[]) -> T
      | ((bvl_Var m :: xs),(y :: ys)) -> (m = n /\
        bvl_inline_var_list (n + 1) xs ys)
      | (_9,_10) -> F`;;

let dest_op_def = cake_define
  `bvl_inline_dest_op x1 args =
      match x1 with
        (bvl_Op closLang_op xs) -> (if bvl_inline_var_list 0 xs args
          then SOME closLang_op else NONE)
      | _11 -> NONE`;;

let let_op_def = cake_define
  `(bvl_inline_let_op [] = []) /\
   (bvl_inline_let_op ((x:bvl_exp) :: y :: xs) =
      HD (bvl_inline_let_op [x]) :: bvl_inline_let_op (y :: xs)) /\
   (bvl_inline_let_op [db_vars_Var v] = [db_vars_Var v]) /\
   (bvl_inline_let_op [bvl_If x1 x2 x3] =
      [bvl_If (HD (bvl_inline_let_op [x1]))
          (HD (bvl_inline_let_op [x2]))
          (HD (bvl_inline_let_op [x3]))]) /\
   (bvl_inline_let_op [bvl_Let xs x2] =
      (let xs = bvl_inline_let_op xs in
      let x2 = HD (bvl_inline_let_op [x2]) in
        match bvl_inline_dest_op x2 xs with SOME closLang_op ->
          [bvl_Op closLang_op xs] | NONE -> [bvl_Let xs x2])) /\
   (bvl_inline_let_op [bvl_Raise x1] =
      [bvl_Raise (HD (bvl_inline_let_op [x1]))]) /\
   (bvl_inline_let_op [bvl_Handle x1 x2] =
      [bvl_Handle (HD (bvl_inline_let_op [x1]))
               (HD (bvl_inline_let_op [x2]))]) /\
   (bvl_inline_let_op [bvl_Op closLang_op xs] =
      [bvl_Op closLang_op (bvl_inline_let_op xs)]) /\
   (bvl_inline_let_op [bvl_Tick x] = [bvl_Tick (HD (bvl_inline_let_op
     [x]))]) /\
   (bvl_inline_let_op [bvl_Force m n] = [bvl_Force m n]) /\
   (bvl_inline_let_op [bvl_Call ticks dest xs] = [bvl_Call ticks
     dest (bvl_inline_let_op xs)])`;;

let let_op_one_def = cake_define
  `(let_op_one (db_vars_Var v) = db_vars_Var v) /\
   (let_op_one (bvl_If x1 x2 x3) =
      bvl_If (let_op_one x1)
         (let_op_one x2)
         (let_op_one x3)) /\
   (let_op_one (bvl_Let xs x2) =
      (let xs = bvl_inline_let_op_list xs in
      let x2 = let_op_one x2 in
        match bvl_inline_dest_op x2 xs with SOME closLang_op ->
          bvl_Op closLang_op xs | NONE -> bvl_Let xs x2)) /\
   (let_op_one (bvl_Raise x1) =
      bvl_Raise (let_op_one x1)) /\
   (let_op_one (bvl_Handle x1 x2) =
      bvl_Handle (let_op_one x1)
             (let_op_one x2)) /\
   (let_op_one (bvl_Op closLang_op xs) =
      bvl_Op closLang_op (bvl_inline_let_op_list xs)) /\
   (let_op_one (bvl_Tick x) = bvl_Tick (let_op_one x)) /\
   (let_op_one (bvl_Force m n) = bvl_Force m n) /\
   (let_op_one (bvl_Call ticks dest xs) = bvl_Call ticks dest
     (bvl_inline_let_op_list xs)) /\
   (bvl_inline_let_op_list [] = []) /\
   (bvl_inline_let_op_list ((x:bvl_exp) :: xs) =
      (let_op_one x) :: bvl_inline_let_op_list xs)`;;

let let_op_sing_def = cake_define
  `bvl_inline_let_op_sing x =
     (match bvl_inline_let_op [x] with (y :: ys) -> y | _12 ->
       bvl_Op (closLang_IntOp (closLang_Const 0)) [])`;;

let optimise_def = cake_define
  `bvl_inline_optimise split_seq cut_size (name,arity,bvl_exp) =
     (name,arity,compile_any split_seq cut_size arity
                   (bvl_inline_let_op_sing (HD
                     (bvl_inline_remove_ticks [bvl_exp]))))`;;

let compile_inc_def = cake_define
  `bvl_inline_compile_inc limit split_seq cut_size cs prog =
     (let (cs,prog1) = tick_compile_prog limit cs prog in
       (cs,MAP (bvl_inline_optimise split_seq cut_size) prog1))`;;

let compile_prog_def = cake_define
  `bvl_inline_compile_prog limit split_seq cut_size prog =
     bvl_inline_compile_inc limit split_seq cut_size LN prog`;;
