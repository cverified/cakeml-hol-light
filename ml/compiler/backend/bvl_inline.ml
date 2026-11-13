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
needs "compiler/backend/closLang.ml";;
needs "lib/sptree.ml";;
needs "semantics/ast.ml";;

(* the theories whose names the Ancestors blocks of the source
   bring, which are the ones that its statements read: the
   overloads of every other theory come out of the interface
   while this file loads *)
let _ = hol4_ancestors "bvl_inline"
  ["bvl"; "bvl_handle"];;

(* tick_inline -- a function that inlines a function body *)

let tick_inline_def,tick_inline_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`tick_inline cs [] = []`;
   `tick_inline cs (x :: y :: xs) =
         HD (tick_inline cs [x]) :: tick_inline cs (y :: xs)`;
   `tick_inline cs [(Var v:bvl_exp)] = [(Var v:bvl_exp)]`;
   `tick_inline cs [(If x1 x2 x3:bvl_exp)] =
         [If (HD (tick_inline cs [x1]))
             (HD (tick_inline cs [x2]))
             (HD (tick_inline cs [x3]))]`;
   `tick_inline cs [(Let xs x2:bvl_exp)] =
         [Let (tick_inline cs xs)
               (HD (tick_inline cs [x2]))]`;
   `tick_inline cs [(Raise x1:bvl_exp)] =
         [Raise (HD (tick_inline cs [x1]))]`;
   `tick_inline cs [(Handle x1 x2:bvl_exp)] =
         [Handle (HD (tick_inline cs [x1]))
                 (HD (tick_inline cs [x2]))]`;
   `tick_inline cs [(Op op xs:bvl_exp)] =
         [Op op (tick_inline cs xs)]`;
   `tick_inline cs [(Tick x:bvl_exp)] =
         [Tick (HD (tick_inline cs [x]))]`;
   `tick_inline cs [(Force m n:bvl_exp)] = [(Force m n:bvl_exp)]`;
   `tick_inline cs [(Call ticks dest xs:bvl_exp)] =
         (match dest with NONE -> [Call ticks dest (tick_inline cs
           xs)] | SOME n ->
         (match sptree_lookup n cs with NONE -> [Call ticks
           dest (tick_inline cs xs)] | SOME (arity,code) -> [Let
           (tick_inline cs xs) (mk_tick (SUC ticks) code)]))`];;

let tick_inline_sing_def,tick_inline_sing_ind = define_mutual_rec
  [`tick_inline_sing cs (Var v:bvl_exp) = (Var v:bvl_exp)`;
   `tick_inline_sing cs (If x1 x2 x3:bvl_exp) =
         (If (tick_inline_sing cs x1)
             (tick_inline_sing cs x2)
             (tick_inline_sing cs x3))`;
   `tick_inline_sing cs (Let xs x2:bvl_exp) =
         (Let (tick_inline_list cs xs)
              (tick_inline_sing cs x2))`;
   `tick_inline_sing cs (Raise x1:bvl_exp) =
         (Raise (tick_inline_sing cs x1))`;
   `tick_inline_sing cs (Handle x1 x2:bvl_exp) =
         (Handle (tick_inline_sing cs x1)
                 (tick_inline_sing cs x2))`;
   `tick_inline_sing cs (Op op xs:bvl_exp) =
         (Op op (tick_inline_list cs xs))`;
   `tick_inline_sing cs (Tick x:bvl_exp) =
         (Tick (tick_inline_sing cs x))`;
   `tick_inline_sing cs (Force m n:bvl_exp) = (Force m n:bvl_exp)`;
   `tick_inline_sing cs (Call ticks dest xs:bvl_exp) =
         (match dest with NONE -> Call ticks dest (tick_inline_list
           cs xs) | SOME n ->
         (match sptree_lookup n cs with NONE -> Call ticks dest
           (tick_inline_list cs xs) | SOME (arity,code) ->
             Let (tick_inline_list cs xs) (mk_tick (SUC ticks)
               code)))`;
   `tick_inline_list cs [] = []`;
   `tick_inline_list cs (x :: xs) =
         (tick_inline_sing cs x) :: tick_inline_list cs xs`];;

let tick_inline_sing = prove
 (`(!e. tick_inline cs [e] = [tick_inline_sing cs e]) /\
   (!es. tick_inline_list cs es = tick_inline cs es)`,
  CHEAT_TAC);;

(* This definition is written to exit as soon as possible. *)
let _ = size_thms "bvl_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let is_small_aux_def,is_small_aux_ind = define_wf
  `MEASURE (\(x0,x1). bvl_exp_size1 x1)`
  [`is_small_aux n [] = n`;
   `is_small_aux n (x :: y :: xs) =
         (if n = 0 then n else
           let n = is_small_aux n [x] in if n = 0 then n else
             is_small_aux n (y :: xs))`;
   `is_small_aux n [(Var v:bvl_exp)] = n`;
   `is_small_aux n [(If x1 x2 x3:bvl_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = is_small_aux n [x1] in if n = 0 then 0 else
         let n = is_small_aux n [x2] in if n = 0 then 0 else
           is_small_aux n [x3])`;
   `is_small_aux n [(Let xs x2:bvl_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = is_small_aux n xs in if n = 0 then 0 else
           is_small_aux n [x2])`;
   `is_small_aux n [(Raise x1:bvl_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
           is_small_aux n [x1])`;
   `is_small_aux n [(Handle x1 x2:bvl_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
         let n = is_small_aux n [x1] in if n = 0 then 0 else
           is_small_aux n [x2])`;
   `is_small_aux n [(Op op xs:bvl_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
           is_small_aux n xs)`;
   `is_small_aux n [(Tick x:bvl_exp)] = is_small_aux n [x]`;
   `is_small_aux n [(Force _3 _4:bvl_exp)] = n`;
   `is_small_aux n [(Call ticks dest xs:bvl_exp)] =
         (let n = n - 1 in if n = 0 then 0 else
           is_small_aux n xs)`];;

let is_small_sing_def,is_small_sing_ind = define_mutual_rec
  [`is_small_sing n (Var v:bvl_exp) = n`;
   `is_small_sing n (If x1 x2 x3:bvl_exp) =
         (let n = n - 1 in if n = 0 then 0 else
         let n = is_small_sing n x1 in if n = 0 then 0 else
         let n = is_small_sing n x2 in if n = 0 then 0 else
           is_small_sing n x3)`;
   `is_small_sing n (Let xs x2:bvl_exp) =
         (let n = n - 1 in if n = 0 then 0 else
         let n = is_small_list n xs in if n = 0 then 0 else
           is_small_sing n x2)`;
   `is_small_sing n (Raise x1:bvl_exp) =
         (let n = n - 1 in if n = 0 then 0 else
           is_small_sing n x1)`;
   `is_small_sing n (Handle x1 x2:bvl_exp) =
         (let n = n - 1 in if n = 0 then 0 else
         let n = is_small_sing n x1 in if n = 0 then 0 else
           is_small_sing n x2)`;
   `is_small_sing n (Op op xs:bvl_exp) =
         (let n = n - 1 in if n = 0 then 0 else
           is_small_list n xs)`;
   `is_small_sing n (Tick x:bvl_exp) = is_small_sing n x`;
   `is_small_sing n (Force _7 _8:bvl_exp) = n`;
   `is_small_sing n (Call ticks dest xs:bvl_exp) =
         (let n = n - 1 in if n = 0 then 0 else
           is_small_list n xs)`;
   `is_small_list n [] = n`;
   `is_small_list n (x :: xs) =
         (if n = 0 then n else
           let n = is_small_sing n x in if n = 0 then n else
             is_small_list n xs)`];;

let is_small_sing = prove
 (`(!e n. is_small_aux n [e] = is_small_sing n e) /\
   (!es n. is_small_list n es = is_small_aux n es)`,
  CHEAT_TAC);;

let is_small_def = new_definition
  `is_small limit' e = ~(is_small_aux limit' [e] = 0)`;;

(* HOL4 bvl_inlineScript.sml:164: a theorem that HOL4 states as the
   value of an ML expression: is_small_eq *)

let _ = size_thms "bvl_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let bvl_inline_is_rec_def,bvl_inline_is_rec_ind = define_wf
  `MEASURE (\(x0,x1). bvl_exp_size1 x1)`
  [`bvl_inline_is_rec n [] = F`;
   `bvl_inline_is_rec n (x :: y :: xs) =
         (if bvl_inline_is_rec n [x] then T else
           bvl_inline_is_rec n (y :: xs))`;
   `bvl_inline_is_rec n [(Var v:bvl_exp)] = F`;
   `bvl_inline_is_rec n [(If x1 x2 x3:bvl_exp)] =
         (if bvl_inline_is_rec n [x1] then T else
         if bvl_inline_is_rec n [x2] then T else
           bvl_inline_is_rec n [x3])`;
   `bvl_inline_is_rec n [(Let xs x2:bvl_exp)] =
         (if bvl_inline_is_rec n xs then T else
           bvl_inline_is_rec n [x2])`;
   `bvl_inline_is_rec n [(Raise x1:bvl_exp)] = bvl_inline_is_rec n
  [x1]`;
   `bvl_inline_is_rec n [(Handle x1 x2:bvl_exp)] =
         (if bvl_inline_is_rec n [x1] then T else
           bvl_inline_is_rec n [x2])`;
   `bvl_inline_is_rec n [(Op op xs:bvl_exp)] = bvl_inline_is_rec n xs`;
   `bvl_inline_is_rec n [(Tick x:bvl_exp)] = bvl_inline_is_rec n [x]`;
   `bvl_inline_is_rec n [(Force _11 _12:bvl_exp)] = F`;
   `bvl_inline_is_rec n [(Call ticks dest xs:bvl_exp)] =
         (if dest = SOME n then T else bvl_inline_is_rec n xs)`];;
hol4_overload "is_rec" "bvl_inline_is_rec";;

let is_rec_sing_def,is_rec_sing_ind = define_mutual_rec
  [`is_rec_sing n (Var v:bvl_exp) = F`;
   `is_rec_sing n (If x1 x2 x3:bvl_exp) =
         (if is_rec_sing n x1 then T else
         if is_rec_sing n x2 then T else
           is_rec_sing n x3)`;
   `is_rec_sing n (Let xs x2:bvl_exp) =
         (if is_rec_list n xs then T else
           is_rec_sing n x2)`;
   `is_rec_sing n (Raise x1:bvl_exp) = is_rec_sing n x1`;
   `is_rec_sing n (Handle x1 x2:bvl_exp) =
         (if is_rec_sing n x1 then T else
           is_rec_sing n x2)`;
   `is_rec_sing n (Op op xs:bvl_exp) = is_rec_list n xs`;
   `is_rec_sing n (Tick x:bvl_exp) = is_rec_sing n x`;
   `is_rec_sing n (Force _15 _16:bvl_exp) = F`;
   `is_rec_sing n (Call ticks dest xs:bvl_exp) =
         (if dest = SOME n then T else is_rec_list n xs)`;
   `is_rec_list n [] = F`;
   `is_rec_list n (x :: xs) =
         (if is_rec_sing n x then T else
           is_rec_list n xs)`];;

let is_rec_sing = prove
 (`(!e n. bvl_inline_is_rec n [e] = is_rec_sing n e) /\
   (!es n. is_rec_list n es = bvl_inline_is_rec n es)`,
  CHEAT_TAC);;

let must_inline_def = new_definition
  `must_inline name limit' e =
     (if is_small limit' e then ~(bvl_inline_is_rec name [e]) else
       F)`;;

(* HOL4 bvl_inlineScript.sml:227: a theorem that HOL4 states as the
   value of an ML expression: must_inline_eq *)

let tick_inline_all_def,tick_inline_all_ind = define_rec
  [`tick_inline_all limit' cs [] aux = (cs,REVERSE aux)`;
   `tick_inline_all limit' cs ((n,(arity:num),e1) :: xs) aux =
         (let e2 = HD (tick_inline cs [e1]) in
         let cs2 = (if must_inline n limit' e2 then sptree_insert n
           (arity,e2) cs else cs) in
           tick_inline_all limit' cs2 xs ((n,arity,e2) :: aux))`];;

(* HOL4 bvl_inlineScript.sml:237-238: a theorem that HOL4 states as
   the value of an ML expression: tick_inline_all_eq *)

let tick_compile_prog_def = new_definition
  `tick_compile_prog limit' cs prog = tick_inline_all limit' cs prog
  []`;;

let LENGTH_tick_inline = prove
 (`!cs xs. LENGTH (tick_inline cs xs) = LENGTH xs`,
  CHEAT_TAC);;

(* [simp] *)
let HD_tick_inline = prove
 (`[HD (tick_inline cs [x])] = tick_inline cs [x]`,
  CHEAT_TAC);;

(* remove_ticks -- a function that removes Ticks *)

let remove_ticks_def,remove_ticks_ind = define_shaped_rec
  "sing>nested"
  [`bvl_inline_remove_ticks [] = []`;
   `bvl_inline_remove_ticks (x :: y :: xs) =
         HD (bvl_inline_remove_ticks [x]) ::
           bvl_inline_remove_ticks (y :: xs)`;
   `bvl_inline_remove_ticks [(Var v:bvl_exp)] = [(Var v:bvl_exp)]`;
   `bvl_inline_remove_ticks [(If x1 x2 x3:bvl_exp)] =
         [If (HD (bvl_inline_remove_ticks [x1]))
             (HD (bvl_inline_remove_ticks [x2]))
             (HD (bvl_inline_remove_ticks [x3]))]`;
   `bvl_inline_remove_ticks [(Let xs x2:bvl_exp)] =
         [Let (bvl_inline_remove_ticks xs) (HD
           (bvl_inline_remove_ticks [x2]))]`;
   `bvl_inline_remove_ticks [(Raise x1:bvl_exp)] =
         [Raise (HD (bvl_inline_remove_ticks [x1]))]`;
   `bvl_inline_remove_ticks [(Handle x1 x2:bvl_exp)] =
         [Handle (HD (bvl_inline_remove_ticks [x1]))
                 (HD (bvl_inline_remove_ticks [x2]))]`;
   `bvl_inline_remove_ticks [(Op op xs:bvl_exp)] =
         [Op op (bvl_inline_remove_ticks xs)]`;
   `bvl_inline_remove_ticks [(Tick x:bvl_exp)] =
  bvl_inline_remove_ticks [x]`;
   `bvl_inline_remove_ticks [(Force m n:bvl_exp)] = [(Force m
  n:bvl_exp)]`;
   `bvl_inline_remove_ticks [(Call ticks dest xs:bvl_exp)] =
         [Call 0 dest (bvl_inline_remove_ticks xs)]`];;
hol4_overload "remove_ticks" "bvl_inline_remove_ticks";;

let remove_ticks_sing_def,remove_ticks_sing_ind = define_mutual_rec
  [`bvl_inline_remove_ticks_sing (Var v:bvl_exp) = (Var v:bvl_exp)`;
   `bvl_inline_remove_ticks_sing (If x1 x2 x3:bvl_exp) =
         If (bvl_inline_remove_ticks_sing x1)
            (bvl_inline_remove_ticks_sing x2)
            (bvl_inline_remove_ticks_sing x3)`;
   `bvl_inline_remove_ticks_sing (Let xs x2:bvl_exp) =
         Let (bvl_inline_remove_ticks_list xs)
           (bvl_inline_remove_ticks_sing x2)`;
   `bvl_inline_remove_ticks_sing (Raise x1:bvl_exp) =
         Raise (bvl_inline_remove_ticks_sing x1)`;
   `bvl_inline_remove_ticks_sing (Handle x1 x2:bvl_exp) =
         Handle (bvl_inline_remove_ticks_sing x1)
                (bvl_inline_remove_ticks_sing x2)`;
   `bvl_inline_remove_ticks_sing (Op op xs:bvl_exp) =
         Op op (bvl_inline_remove_ticks_list xs)`;
   `bvl_inline_remove_ticks_sing (Tick x:bvl_exp) =
  bvl_inline_remove_ticks_sing x`;
   `bvl_inline_remove_ticks_sing (Force m n:bvl_exp) = (Force m
  n:bvl_exp)`;
   `bvl_inline_remove_ticks_sing (Call ticks dest xs:bvl_exp) =
         Call 0 dest (bvl_inline_remove_ticks_list xs)`;
   `bvl_inline_remove_ticks_list [] = []`;
   `bvl_inline_remove_ticks_list (x :: xs) =
         (bvl_inline_remove_ticks_sing x) ::
           bvl_inline_remove_ticks_list xs`];;
hol4_overload "remove_ticks_list" "bvl_inline_remove_ticks_list";;
hol4_overload "remove_ticks_sing" "bvl_inline_remove_ticks_sing";;

let remove_ticks_sing = prove
 (`(!e. bvl_inline_remove_ticks [e] = [bvl_inline_remove_ticks_sing e])
  /\
   (!es. bvl_inline_remove_ticks_list es = bvl_inline_remove_ticks
     es)`,
  CHEAT_TAC);;

(* [simp] *)
let LENGTH_remove_ticks = prove
 (`!xs. LENGTH (bvl_inline_remove_ticks xs) = LENGTH xs`,
  CHEAT_TAC);;

(* [simp] *)
let remove_ticks_SING = prove
 (`[HD (bvl_inline_remove_ticks [r])] = bvl_inline_remove_ticks [r]`,
  CHEAT_TAC);;

(* let_op -- a function that optimises Let [...] (Op op [Var ...]) *)

let _ = size_thms "bvl_exp";;
(* the termination relation is not in the HOL4 source; this one is
   what the port found for it *)
let var_list_def,var_list_ind = define_wf
  `MEASURE (\(x0,x1,x2). bvl_exp_size1 x1)`
  [`bvl_inline_var_list n x2 x3 =
      match (x2,x3) with
        ([],[]) -> T
      | ((bvl_Var m :: xs),(y :: ys)) -> (m = n /\
        bvl_inline_var_list (n + 1) xs ys)
      | (_17,_18) -> F`];;
hol4_overload "var_list" "bvl_inline_var_list";;

let dest_op_def = new_definition
  `bvl_inline_dest_op x1 args =
      match x1 with
        bvl_Op op xs -> (if bvl_inline_var_list 0 xs args then SOME
          op else NONE)
      | _19 -> NONE`;;
hol4_overload "dest_op" "bvl_inline_dest_op";;

let let_op_def,let_op_ind = assume_definition_rec
  "termination (CHEAT_TAC)"
  [`bvl_inline_let_op [] = []`;
   `bvl_inline_let_op ((x:bvl_exp) :: y :: xs) =
         HD (bvl_inline_let_op [x]) :: bvl_inline_let_op (y ::
           xs)`;
   `bvl_inline_let_op [(Var v:bvl_exp)] = [(Var v:bvl_exp)]`;
   `bvl_inline_let_op [(If x1 x2 x3:bvl_exp)] =
         [If (HD (bvl_inline_let_op [x1]))
             (HD (bvl_inline_let_op [x2]))
             (HD (bvl_inline_let_op [x3]))]`;
   `bvl_inline_let_op [(Let xs x2:bvl_exp)] =
         (let xs = bvl_inline_let_op xs in
         let x2 = HD (bvl_inline_let_op [x2]) in
           match bvl_inline_dest_op x2 xs with SOME op -> [Op op
             xs] | NONE -> [(Let xs x2:bvl_exp)])`;
   `bvl_inline_let_op [(Raise x1:bvl_exp)] =
         [Raise (HD (bvl_inline_let_op [x1]))]`;
   `bvl_inline_let_op [(Handle x1 x2:bvl_exp)] =
         [Handle (HD (bvl_inline_let_op [x1]))
                  (HD (bvl_inline_let_op [x2]))]`;
   `bvl_inline_let_op [(Op op xs:bvl_exp)] =
         [Op op (bvl_inline_let_op xs)]`;
   `bvl_inline_let_op [(Tick x:bvl_exp)] = [Tick (HD
  (bvl_inline_let_op [x]))]`;
   `bvl_inline_let_op [(Force m n:bvl_exp)] = [(Force m n:bvl_exp)]`;
   `bvl_inline_let_op [(Call ticks dest xs:bvl_exp)] = [Call ticks
  dest (bvl_inline_let_op xs)]`];;
hol4_overload "let_op" "bvl_inline_let_op";;

let let_op_one_def,let_op_one_ind = define_mutual_rec
  [`let_op_one (Var v:bvl_exp) = (Var v:bvl_exp)`;
   `let_op_one (If x1 x2 x3:bvl_exp) =
         If (let_op_one x1)
            (let_op_one x2)
            (let_op_one x3)`;
   `let_op_one (Let xs x2:bvl_exp) =
         (let xs = bvl_inline_let_op_list xs in
         let x2 = let_op_one x2 in
           match bvl_inline_dest_op x2 xs with SOME op -> Op op
             xs | NONE -> (Let xs x2:bvl_exp))`;
   `let_op_one (Raise x1:bvl_exp) =
         Raise (let_op_one x1)`;
   `let_op_one (Handle x1 x2:bvl_exp) =
         Handle (let_op_one x1)
                (let_op_one x2)`;
   `let_op_one (Op op xs:bvl_exp) =
         Op op (bvl_inline_let_op_list xs)`;
   `let_op_one (Tick x:bvl_exp) = Tick (let_op_one x)`;
   `let_op_one (Force m n:bvl_exp) = (Force m n:bvl_exp)`;
   `let_op_one (Call ticks dest xs:bvl_exp) = Call ticks dest
  (bvl_inline_let_op_list xs)`;
   `bvl_inline_let_op_list [] = []`;
   `bvl_inline_let_op_list ((x:bvl_exp) :: xs) =
         (let_op_one x) :: bvl_inline_let_op_list xs`];;
hol4_overload "let_op_list" "bvl_inline_let_op_list";;

let let_op_one = prove
 (`(!e. bvl_inline_let_op [e] = [let_op_one e]) /\
   (!es. bvl_inline_let_op_list es = bvl_inline_let_op es)`,
  CHEAT_TAC);;

let let_op_sing_def = new_definition
  `bvl_inline_let_op_sing x =
     (match bvl_inline_let_op [x] with (y :: ys) -> y | _20 -> Op
       (closLang_IntOp (closLang_Const (&0))) [])`;;
hol4_overload "let_op_sing" "bvl_inline_let_op_sing";;

(* HOL4 bvl_inlineScript.sml:414: a theorem that HOL4 states as the
   value of an ML expression: let_op_sing_eq *)

let bvl_inline_optimise_def = new_definition
  `bvl_inline_optimise split_seq cut_size (name,arity,exp) =
     (name,arity,compile_any split_seq cut_size arity
                   (bvl_inline_let_op_sing (HD
                     (bvl_inline_remove_ticks [exp]))))`;;
hol4_overload "optimise" "bvl_inline_optimise";;

(* HOL4 bvl_inlineScript.sml:422: a theorem that HOL4 states as the
   value of an ML expression: optimise_eq *)

let bvl_inline_compile_inc_def = new_definition
  `bvl_inline_compile_inc limit' split_seq cut_size cs prog =
     (let (cs,prog1) = tick_compile_prog limit' cs prog in
       (cs,MAP (bvl_inline_optimise split_seq cut_size) prog1))`;;
hol4_overload "compile_inc" "bvl_inline_compile_inc";;

let bvl_inline_compile_prog_def = new_definition
  `bvl_inline_compile_prog limit' split_seq cut_size prog =
     bvl_inline_compile_inc limit' split_seq cut_size LN prog`;;
hol4_overload "compile_prog" "bvl_inline_compile_prog";;

(* and the overloads that this file cannot see are back in the
   interface *)
let _ = unhide_overloads ();;
