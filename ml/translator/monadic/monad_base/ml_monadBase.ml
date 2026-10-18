(* ======================================================== *)
(*  ml_monadBase: ported from HOL4's
    translator/monadic/monad_base/ml_monadBaseScript.sml  *)
(* ======================================================== *)

(*
  Definitions for the state-and-exception monad that is supported by the
  proof-producing monadic translator.
*)

needs "semantics/semanticPrimitives.ml";;

(* 'a is the type of the state, 'b is the type of successful
   computations, and
 * 'c is the type of exceptions *)

let exc_INDUCT,exc_RECURSION = define_datatype
  "exc = M_success ('a) | M_failure ('b)";;

(* HOL4 ml_monadBaseScript.sml:21: the type abbreviation M, which the
   port expands *)

let liftM_def = cake_define
  `((liftM read' (write':('a->'a)->'d->'d)
  (op:'a->('b,'c)exc#'a)):'d->('b,'c)exc#'d) =
     (\state. let (ret,new) = op (read' state) in
                (ret,write' (K new) state))`;;

(* Definitions using monadic syntax *)

let st_ex_bind_def = cake_define
  `(st_ex_bind:('a->('b,'c)exc#'a)->('b->'a->('d,'c)exc#'a)->'a->('d
  ,'c)exc#'a) x f =
     (\s.
       match x s with
         (M_success y,s) -> f y s | (M_failure x,s) -> (M_failure
           x,s))`;;

let st_ex_ignore_bind_def = cake_define
  `(st_ex_ignore_bind:('a->('b,'c)exc#'a)->('a->('d,'c)exc#'a)->'a->('d
  ,'c)exc#'a) x f =
     (\s.
       match x s with
         (M_success y,s) -> f s | (M_failure x,s) -> (M_failure
           x,s))`;;


(*
 * Congruence theorems for st_ex_bind / st_ex_ignore_bind.
 * Used by TFL rewriters when deriving termination conditions.
 * Ensures that intermediate values of the monad bind (y, s'')
 * are captured.
 *)
(* HOL4 ml_monadBaseScript.sml:70: ML code, not ported *)
(* HOL4 ml_monadBaseScript.sml:83: ML code, not ported *)


let st_ex_return_def = cake_define
  `(st_ex_return) x =
     (\s. (M_success x,s))`;;

(* HOL4 ml_monadBaseScript.sml:91: ML code, not ported *)

let otherwise_def = cake_define
  `otherwise
     x y =
       (\s. match ((x:'a->('b,'c)exc#'a) s) with
             (M_success y,s) -> (M_success y,s) | (M_failure e,s)
               -> (y:'a->('b,'c)exc#'a) s)`;;

hol4_overload "++" "otherwise";;

let can_def = cake_define
  `can f x = (
              otherwise (st_ex_ignore_bind (f x) (st_ex_return T))
                (st_ex_return F))`;;

(* Dynamic allocation of references *)
let store_ref_INDUCT,store_ref_RECURSION = define_datatype
  "store_ref = StoreRef (num)";;

(* Arrays *)

(* Msub *)
let msub_def = cake_define
  `Msub e (n:num) l =
     (match l with
       [] -> M_failure e | x :: l' -> (if n = 0 then M_success x
         else Msub e (n - 1) l'))`;;

(* Mupdate *)
let mupdate_def = cake_define
  `Mupdate e x (n:num) l =
     (match l with
       [] -> M_failure e | x' :: l' ->
         (if n = 0 then
           M_success (x :: l') else
           (match Mupdate e x (n - 1) l' with
              M_success l'' -> M_success (x' :: l'') | other ->
                other)))`;;

(* Array resize *)
let array_resize_def = cake_define
  `array_resize (n:num) x a =
     (if n = 0 then
       [] else
       match a with
         [] -> x :: array_resize (n - 1) x a | x' :: a' -> x' ::
           array_resize (n - 1) x a')`;;

(* User functions *)
let marray_length_def = cake_define
  `Marray_length get_arr =
     (\s. (M_success (LENGTH (get_arr s)),s))`;;

let marray_sub_def = cake_define
  `Marray_sub get_arr e n =
     (\s. (Msub e n (get_arr s),s))`;;

let marray_update_def = cake_define
  `Marray_update get_arr set_arr e n x =
     (\s. match Mupdate e x n (get_arr s) with
           M_success a -> (M_success one,set_arr a s) | M_failure
             e -> (M_failure e,s))`;;

let marray_alloc_def = cake_define
  `Marray_alloc set_arr n x =
     (\s. (M_success one,set_arr (REPLICATE n x) s))`;;

let marray_resize_def = cake_define
  `Marray_resize get_arr set_arr n x =
     (\s. (M_success one,set_arr (array_resize n x (get_arr s))
       s))`;;

(* Dynamic allocated references *)
let mref_def = cake_define
  `Mref cons x = (\s. (M_success (StoreRef (LENGTH s)),cons x :: s))`;;

let dref_def = cake_define
  `dref n = (\s. EL (LENGTH s - n - 1) s)`;;

let mdref_aux_def = cake_define
  `Mdref_aux e (n:num) =
     (\s. match s with
           [] -> M_failure e | x :: s -> (if n = 0 then M_success
             x else Mdref_aux e (n - 1) s))`;;

let mdref_def = cake_define
  `Mdref e (StoreRef n) =
     (\s. (Mdref_aux e (LENGTH s - n - 1) s,s))`;;

let mpop_ref_def = cake_define
  `Mpop_ref e =
     (\(r,s). match s with
                x :: s -> (r,s) | [] -> (M_failure e,s))`;;

let mref_assign_aux_def = cake_define
  `Mref_assign_aux e (n:num) x =
     (\s. match s with
           x' :: s ->
             (if n = 0 then
               M_success (x :: s) else
               (match Mref_assign_aux e (n - 1) x s with
                  M_success s -> M_success (x' :: s) | other ->
                    other)) | [] -> M_failure e)`;;

let mref_assign_def = cake_define
  `Mref_assign e (StoreRef n) x =
     (\s. match Mref_assign_aux e (LENGTH s - n - 1) x s with
           M_success s -> (M_success one,s) | M_failure e ->
             (M_failure e,s))`;;

let ref_assign_def = cake_define
  `ref_assign n x = (\s. LUPDATE x (LENGTH s - n - 1) s)`;;

let ref_bind_def = cake_define
  `ref_bind create f pop =
     (\s. match create s with
           (M_success x,s) -> pop (f x s) | (M_failure x,s) ->
             (M_failure x,s))`;;

(* TODO: use that *)
let mget_ref_def = cake_define
  `Mget_ref get_var' = (\s. (M_success (get_var' s),s))`;;

let mset_ref_def = cake_define
  `Mset_ref set_var' x = (\s. (M_success one,set_var' x s))`;;

(* Rules to deal with the monads *)

(* HOL4 ml_monadBaseScript.sml:557-560: ML code, not ported *)

(* Run *)
let run_def = cake_define
  `run (x:'a->('b,'c)exc#'a) state = FST (x state)`;;

hol4_only "++" "APPEND";;
